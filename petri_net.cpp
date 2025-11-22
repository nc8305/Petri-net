// petri_net_bdd_ilp.cpp
//
// Petri Net Analyzer (PNML) with:
//   - Weighted PT-net parsing (multi-page) via TinyXML2
//   - Matrices Pre/Post/C
//   - Explicit reachability (BFS) [--explicit]
//   - Symbolic reachability with BDD (1-safe) [--bdd]
//       * If compiled with -DUSE_CUDD: real BDD via CUDD
//       * Otherwise: tiny fallback engine (explicit boolean set) to keep interface working
//   - ILP modeling using state equation M = M0 + C x
//       * Dead marking finder [--ilp-dead]
//       * Linear objective max c^T M [--ilp-max c1,c2,...]
//       * If compiled with -DUSE_GLPK: solve directly, else write LP file 'model.lp'
//
// Build examples:
//   (A) Plain (no CUDD/GLPK):
//       g++ -std=c++17 petri_net_bdd_ilp.cpp tinyxml2.cpp -O2 -o petri_net
//
//   (B) With CUDD (Linux):
//       g++ -std=c++17 petri_net.cpp tinyxml2.cpp -I/usr/include -L/usr/lib -lcudd -lutil -lm -DUSE_CUDD -O2 -o petri_net
//
//   (C) With GLPK (Linux):
//       g++ -std=c++17 petri_net.cpp tinyxml2.cpp -lglpk -DUSE_GLPK -O2 -o petri_net
//
//   (D) With both:
//       g++ -std=c++17 petri_net_bdd_ilp.cpp tinyxml2.cpp -DUSE_CUDD -DUSE_GLPK -lcudd -lutil -lglpk -lm -O2 -o petri_net
//
// Windows (MSYS2 UCRT64) thường chỉ cần:
//       g++ -std=c++17 -O2 -DUSE_CUDD petri_net_bdd_ilp.cpp tinyxml2.cpp -lcudd -o petri_net.exe
//
// -----------------------------------------------------------------------------


#include "tinyxml2.h"
#include <iostream>
#include <queue>
#include <unordered_set>
#include <unordered_map>
#include <vector>
#include <string>
#include <algorithm>
#include <stdexcept>
#include <limits>
#include <iomanip>
#include <fstream>
#include <cctype>
#include <sstream>
#include <chrono>
#include <cmath>

using namespace std;

// ===========================
// Optional libraries toggles
// ===========================
#ifdef USE_CUDD
extern "C" {
#include <cudd.h>
// #include <util.h>  // không cần trên Windows/MSYS2 nếu libcudd đã bundle
}
#endif

#ifdef USE_GLPK
#include <glpk.h>
#endif

// ---------------------------
// Timing utilities (with decimals)
// ---------------------------

class Stopwatch {
private:
    using clock = std::chrono::high_resolution_clock;
    clock::time_point t0{}, t1{};
    bool running = false;

public:
    void start() {
        t0 = clock::now();
        running = true;
    }
    // stop() trả về thời gian ms đã đo
    double stop() {
        t1 = clock::now();
        running = false;
        return std::chrono::duration<double, std::milli>(t1 - t0).count();
    }
    // ms() luôn trả về thời gian đã trôi (kể cả sau khi stop)
    double ms() const {
        const auto end = running ? clock::now() : t1;
        return std::chrono::duration<double, std::milli>(end - t0).count();
    }
};

// helper format ms với số thập phân cố định
static std::string fmt_ms(double ms, int prec = 3) {
    std::ostringstream oss;
    oss.setf(std::ios::fixed);
    oss << std::setprecision(prec) << ms;
    return oss.str();
}

#ifdef _WIN32
  #ifndef NOMINMAX
  #define NOMINMAX 1
  #endif
  #ifndef WIN32_LEAN_AND_MEAN
  #define WIN32_LEAN_AND_MEAN
  #endif
  #ifndef NOGDI
  #define NOGDI
  #endif
  #include <windows.h>
  #include <psapi.h>
#else
  #include <sys/resource.h>
#endif

static void print_mem_now(const std::string& label) {
#ifdef _WIN32
    PROCESS_MEMORY_COUNTERS pmc;
    if (GetProcessMemoryInfo(GetCurrentProcess(), &pmc, sizeof(pmc))) {
        std::cout << "[mem ] " << label << " WorkingSet: "
                  << (pmc.WorkingSetSize / 1024) << " KB, Peak: "
                  << (pmc.PeakWorkingSetSize / 1024) << " KB\n";
    }
#else
    struct rusage usage;
    if (getrusage(RUSAGE_SELF, &usage) == 0) {
        std::cout << "[mem ] " << label << " RSS: "
                  << (usage.ru_maxrss) << " KB\n";
    }
#endif
}

// ---------------------------
// Data structures
// ---------------------------

struct Arc {
    string source;
    string target;
    int weight = 1; // default multiplicity
};

struct Place {
    string id;
    string name;
    int tokens = 0;
};

struct Transition {
    string id;
    string name;
};

struct PetriNet {
    unordered_map<string, Place> places;
    unordered_map<string, Transition> transitions;
    vector<Arc> arcs;
};

// Weighted preset/postset maps:
using WMapPT = unordered_map<string, unordered_map<string,int>>; // preW[t][p] = W(p,t)
using WMapTP = unordered_map<string, unordered_map<string,int>>; // postW[t][p] = W(t,p)

// ---------------------------
// BDD Result structure
// ---------------------------

struct BDDResult {
    long long state_count = 0;
    size_t iterations = 0;
    double time_ms = 0.0;
    bool success = false;
};

// ---------------------------
// Utilities
// ---------------------------

static vector<string> sorted_keys(const unordered_map<string, Place>& m) {
    vector<string> v;
    v.reserve(m.size());
    for (auto& kv : m) v.push_back(kv.first);
    sort(v.begin(), v.end());
    return v;
}
static vector<string> sorted_keys(const unordered_map<string, Transition>& m) {
    vector<string> v;
    v.reserve(m.size());
    for (auto& kv : m) v.push_back(kv.first);
    sort(v.begin(), v.end());
    return v;
}

static unordered_map<string,int> initial_marking(const PetriNet& net) {
    unordered_map<string,int> M;
    for (const auto& kv : net.places) M[kv.first] = kv.second.tokens;
    return M;
}

static string marking_to_key(const unordered_map<string,int>& M,
                             const vector<string>& place_order) {
    string key;
    key.reserve(place_order.size()*3);
    for (const auto& p : place_order) {
        auto it = M.find(p);
        int val = (it==M.end()?0:it->second);
        key += to_string(val);
        key.push_back(',');
    }
    return key;
}

static string trim(const string& s) {
    size_t i=0, j=s.size();
    while (i<j && isspace((unsigned char)s[i])) ++i;
    while (j>i && isspace((unsigned char)s[j-1])) --j;
    return s.substr(i, j-i);
}

// ---------------------------
// Incidence (weighted)
// ---------------------------

static pair<WMapPT, WMapTP> build_incidence_maps_w(const PetriNet& net) {
    WMapPT preW;
    WMapTP postW;
    for (const auto& a : net.arcs) {
        bool srcP = net.places.count(a.source);
        bool tgtP = net.places.count(a.target);
        bool srcT = net.transitions.count(a.source);
        bool tgtT = net.transitions.count(a.target);
        if (srcP && tgtT) {
            // Place -> Transition
            preW[a.target][a.source] += std::max(1, a.weight);
        } else if (srcT && tgtP) {
            // Transition -> Place
            postW[a.source][a.target] += std::max(1, a.weight);
        } else {
            // ignore unsupported arcs (P->P or T->T)
        }
    }
    return {preW, postW};
}

// ---------------------------
// PNML parsing (multi-page)
// ---------------------------

static void parse_page(tinyxml2::XMLElement* pageElem, PetriNet& net) {
    // Places
    for (tinyxml2::XMLElement *placeElem = pageElem->FirstChildElement("place");
         placeElem != nullptr; placeElem = placeElem->NextSiblingElement("place"))
    {
        Place p;
        const char *id = placeElem->Attribute("id");
        if (!id) continue;
        p.id = id;

        // name/text
        if (auto nameElem = placeElem->FirstChildElement("name")) {
            if (auto txt = nameElem->FirstChildElement("text")) {
                if (txt->GetText()) p.name = txt->GetText();
            }
        }
        if (p.name.empty()) p.name = p.id;

        // initialMarking/text
        if (auto initElem = placeElem->FirstChildElement("initialMarking")) {
            if (auto txt = initElem->FirstChildElement("text")) {
                if (txt->GetText()) {
                    try { p.tokens = stoi(txt->GetText()); }
                    catch (...) { p.tokens = 0; }
                }
            }
        }

        net.places[p.id] = p;
    }

    // Transitions
    for (tinyxml2::XMLElement *transElem = pageElem->FirstChildElement("transition");
         transElem != nullptr; transElem = transElem->NextSiblingElement("transition"))
    {
        Transition t;
        const char *id = transElem->Attribute("id");
        if (!id) continue;
        t.id = id;

        if (auto nameElem = transElem->FirstChildElement("name")) {
            if (auto txt = nameElem->FirstChildElement("text")) {
                if (txt->GetText()) t.name = txt->GetText();
            }
        }
        if (t.name.empty()) t.name = t.id;

        net.transitions[t.id] = t;
    }

    // Arcs
    for (tinyxml2::XMLElement *arcElem = pageElem->FirstChildElement("arc");
         arcElem != nullptr; arcElem = arcElem->NextSiblingElement("arc"))
    {
        Arc a;
        const char *src = arcElem->Attribute("source");
        const char *tgt = arcElem->Attribute("target");
        if (!src || !tgt) continue;
        a.source = src; a.target = tgt;

        // inscription/text optional
        if (auto ins = arcElem->FirstChildElement("inscription")) {
            if (auto txt = ins->FirstChildElement("text")) {
                if (txt->GetText()) {
                    try { a.weight = stoi(txt->GetText()); }
                    catch (...) { a.weight = 1; }
                }
            }
        }
        if (a.weight <= 0) a.weight = 1;
        net.arcs.push_back(a);
    }
}

static PetriNet parse_pnml(const string& file_path) {
    PetriNet net;
    tinyxml2::XMLDocument doc;
    tinyxml2::XMLError e = doc.LoadFile(file_path.c_str());
    if (e != tinyxml2::XML_SUCCESS) {
        throw runtime_error("Error: Could not open PNML file " + file_path);
    }
    tinyxml2::XMLElement* pnml = doc.FirstChildElement("pnml");
    if (!pnml) throw runtime_error("No <pnml> root element found.");
    tinyxml2::XMLElement* netElem = pnml->FirstChildElement("net");
    if (!netElem) throw runtime_error("No <net> element found within <pnml>.");

    // Iterate all <page> elements
    for (tinyxml2::XMLElement* page = netElem->FirstChildElement("page");
         page != nullptr; page = page->NextSiblingElement("page"))
    {
        parse_page(page, net);
    }

    // Consistency check for arcs
    for (const auto& arc : net.arcs) {
        bool srcOK = net.places.count(arc.source) || net.transitions.count(arc.source);
        bool tgtOK = net.places.count(arc.target) || net.transitions.count(arc.target);
        if (!srcOK) throw runtime_error("Invalid arc source ID found: " + arc.source);
        if (!tgtOK) throw runtime_error("Invalid arc target ID found: " + arc.target);
    }

    cout << "Parsed PNML successfully: "
         << net.places.size() << " places, "
         << net.transitions.size() << " transitions, "
         << net.arcs.size() << " arcs.\n";
    return net;
}

// ---------------------------
// Matrices (Pre/Post/C)
// ---------------------------

struct Matrices {
    vector<string> place_order;
    vector<string> trans_order;
    vector<vector<int>> Pre, Post, C;
    WMapPT preW;
    WMapTP postW;
};

static Matrices build_matrices(const PetriNet& net) {
    auto [preW, postW] = build_incidence_maps_w(net);
    vector<string> P = sorted_keys(net.places);
    vector<string> T = sorted_keys(net.transitions);

    unordered_map<string,int> pIndex, tIndex;
    for (size_t i=0;i<P.size();++i) pIndex[P[i]] = (int)i;
    for (size_t j=0;j<T.size();++j) tIndex[T[j]] = (int)j;

    vector<vector<int>> Pre(P.size(), vector<int>(T.size(), 0));
    vector<vector<int>> Post(P.size(), vector<int>(T.size(), 0));

    for (const auto& kvT : preW) {
        const string& t = kvT.first;
        int j = tIndex[t];
        for (const auto& kvP : kvT.second) {
            const string& p = kvP.first;
            int w = kvP.second;
            int i = pIndex[p];
            Pre[i][j] = w;
        }
    }
    for (const auto& kvT : postW) {
        const string& t = kvT.first;
        int j = tIndex[t];
        for (const auto& kvP : kvT.second) {
            const string& p = kvP.first;
            int w = kvP.second;
            int i = pIndex[p];
            Post[i][j] = w;
        }
    }

    vector<vector<int>> C(P.size(), vector<int>(T.size(), 0));
    for (size_t i=0;i<P.size();++i) {
        for (size_t j=0;j<T.size();++j) {
            C[i][j] = Post[i][j] - Pre[i][j];
        }
    }

    return {P, T, Pre, Post, C, preW, postW};
}

static void print_matrix(const vector<vector<int>>& M,
                         const vector<string>& rows,
                         const vector<string>& cols,
                         const string& title) {
    cout << "\n" << title << " (rows=places, cols=transitions)\n";
    // compute widths
    size_t rw = 0;
    for (auto& r : rows) rw = std::max(rw, r.size());
    size_t cw = 0;
    for (auto& c : cols) cw = std::max(cw, c.size());
    cw = std::max<size_t>(cw, 5);

    cout << setw((int)rw+2) << " ";
    for (const auto& c : cols) cout << setw((int)cw) << c;
    cout << "\n";

    for (size_t i=0;i<rows.size();++i) {
        cout << setw((int)rw+2) << rows[i];
        for (size_t j=0;j<cols.size();++j) {
            cout << setw((int)cw) << M[i][j];
        }
        cout << "\n";
    }
}

static void print_net_structure(const PetriNet& net) {
    cout << "\n--- Network Structure ---\n";
    cout << "Places:\n";
    auto P = sorted_keys(net.places);
    for (const auto& id : P) {
        const auto& p = net.places.at(id);
        cout << " - " << id << " (" << p.name << "): initial tokens=" << p.tokens << "\n";
    }
    cout << "\nTransitions:\n";
    auto T = sorted_keys(net.transitions);
    for (const auto& id : T) {
        const auto& t = net.transitions.at(id);
        cout << " - " << id << " (" << t.name << ")\n";
    }
    cout << "\nArcs:\n";
    for (const auto& a : net.arcs) {
        cout << " - " << a.source << " -> " << a.target << " (weight=" << a.weight << ")\n";
    }
}

// ---------------------------
// Explicit reachability (BFS) — weighted
// ---------------------------

struct AnalysisConfig { size_t MAX_STATES = 100000; size_t MAX_DEPTH = 2000; };

static bool is_enabled_w(const string& tid,
                         const unordered_map<string,int>& M,
                         const WMapPT& preW) {
    auto it = preW.find(tid);
    if (it == preW.end()) return true; // source transition (no input)
    for (const auto& pw : it->second) {
        const string& p = pw.first;
        int w = pw.second;
        auto mp = M.find(p);
        if (mp == M.end() || mp->second < w) return false;
    }
    return true;
}

static unordered_map<string,int> fire_w(const string& tid,
                                        const unordered_map<string,int>& M,
                                        const WMapPT& preW,
                                        const WMapTP& postW) {
    auto M2 = M;
    if (auto it = preW.find(tid); it != preW.end()) {
        for (const auto& pw : it->second) {
            M2[pw.first] -= pw.second;
        }
    }
    if (auto it = postW.find(tid); it != postW.end()) {
        for (const auto& tp : it->second) {
            M2[tp.first] += tp.second;
        }
    }
    return M2;
}

struct ReachabilityResult {
    vector<unordered_map<string,int>> states;
    vector<string> keys;
    bool finished = true;
    size_t explored = 0;
};

static ReachabilityResult compute_reachability_explicit(const PetriNet& net, const Matrices& Mx, const AnalysisConfig& cfg) {
    ReachabilityResult R;
    auto& preW = Mx.preW;
    auto& postW = Mx.postW;
    vector<string> P = Mx.place_order;
    vector<string> T = Mx.trans_order;
    unordered_map<string,int> M0 = initial_marking(net);
    string k0 = marking_to_key(M0, P);
    unordered_set<string> visited;
    visited.insert(k0);
    queue<pair<unordered_map<string,int>, size_t>> q;
    q.push({M0, 0});
    R.states.push_back(M0);
    R.keys.push_back(k0);
    while (!q.empty()) {
        auto [M, depth] = q.front(); q.pop();
        R.explored++;
        if (R.states.size() >= cfg.MAX_STATES || depth >= cfg.MAX_DEPTH) { R.finished=false; continue; }
        for (const auto& t : T) {
            if (!is_enabled_w(t, M, preW)) continue;
            auto M2 = fire_w(t, M, preW, postW);
            string k2 = marking_to_key(M2, P);
            if (visited.insert(k2).second) {
                R.states.push_back(M2);
                R.keys.push_back(k2);
                q.push({M2, depth+1});
                if (R.states.size() >= cfg.MAX_STATES) { R.finished=false; break; }
            }
        }
    }
    return R;
}

// ---------------------------
// BDD symbolic reachability (1-safe)
// ---------------------------

struct BDDOptions { bool one_safe = true; }; // 1-safe assumption

#ifdef USE_CUDD

struct BDDCtx {
    DdManager* mgr = nullptr;
    vector<DdNode*> X;   // current vars
    vector<DdNode*> Xp;  // next vars
    DdNode* cubeX = nullptr; // ∧ X[i]
    int n;
};

static void cudd_safe_deref(DdManager* mgr, DdNode* f) {
    if (f) Cudd_RecursiveDeref(mgr, f);
}

static BDDCtx bdd_init_cudd(int nvars) {
    BDDCtx C;
    C.n = nvars;
    // Cudd_Init(numVars, numVarsZ, numSlots, cacheSize, maxMemory)
    C.mgr = Cudd_Init(2*nvars, 0, CUDD_UNIQUE_SLOTS, CUDD_CACHE_SLOTS, 0);
    Cudd_AutodynEnable(C.mgr, CUDD_REORDER_SIFT);
    C.X.resize(nvars); C.Xp.resize(nvars);
    for (int i=0;i<nvars;i++) {
        C.X[i]  = Cudd_bddIthVar(C.mgr, i);
        Cudd_Ref(C.X[i]);
    }
    for (int i=0;i<nvars;i++) {
        C.Xp[i] = Cudd_bddIthVar(C.mgr, nvars + i);
        Cudd_Ref(C.Xp[i]);
    }
    // cube of X
    DdNode* cube = Cudd_ReadOne(C.mgr); Cudd_Ref(cube);
    for (int i=0;i<nvars;i++) {
        DdNode* tmp = Cudd_bddAnd(C.mgr, cube, C.X[i]); Cudd_Ref(tmp);
        Cudd_RecursiveDeref(C.mgr, cube);
        cube = tmp;
    }
    C.cubeX = cube;
    return C;
}

static void bdd_free_cudd(BDDCtx& C) {
    for (auto v : C.X) cudd_safe_deref(C.mgr, v);
    for (auto v : C.Xp) cudd_safe_deref(C.mgr, v);
    cudd_safe_deref(C.mgr, C.cubeX);
    Cudd_Quit(C.mgr);
    C.mgr=nullptr;
}

static DdNode* bdd_mk_literal(DdManager* mgr, DdNode* var, bool positive) {
    DdNode* f = positive ? var : Cudd_Not(var);
    Cudd_Ref(f);
    return f;
}

static DdNode* bdd_and(DdManager* mgr, DdNode* a, DdNode* b) {
    DdNode* f = Cudd_bddAnd(mgr, a, b); Cudd_Ref(f); return f;
}
static DdNode* bdd_or(DdManager* mgr, DdNode* a, DdNode* b) {
    DdNode* f = Cudd_bddOr(mgr, a, b); Cudd_Ref(f); return f;
}
static DdNode* bdd_xnor(DdManager* mgr, DdNode* a, DdNode* b) {
    DdNode* f = Cudd_bddXnor(mgr, a, b); Cudd_Ref(f); return f;
}

static DdNode* build_initial_1safe(const unordered_map<string,int>& M0,
                                   const vector<string>& P,
                                   BDDCtx& C) {
    DdNode* one = Cudd_ReadOne(C.mgr); Cudd_Ref(one);
    DdNode* S = one;
    for (size_t i=0;i<P.size();++i) {
        bool val = (M0.at(P[i]) != 0);
        DdNode* lit = bdd_mk_literal(C.mgr, C.X[i], val);
        DdNode* tmp = bdd_and(C.mgr, S, lit);
        cudd_safe_deref(C.mgr, S);
        cudd_safe_deref(C.mgr, lit);
        S = tmp;
    }
    return S; // already Ref'd
}

static DdNode* build_transition_relation_1safe(const string& tid,
                                               const Matrices& Mx,
                                               BDDCtx& C) {
    // For 1-safe PN:
    // enabling:   ∧_{p in pre} X[p]  ∧  ∧_{r in post\pre} !X[r]   (capacity 1)
    // update:     For each place q:
    //               if q in pre\post: Xp[q] = 0
    //               if q in post\pre: Xp[q] = 1
    //               if q in pre∩post: Xp[q] = 1  (self-loop keeps 1)
    //               else:             Xp[q] ↔ X[q]
    DdManager* mgr = C.mgr;
    size_t nP = Mx.place_order.size();
    unordered_map<string,int> pre;
    unordered_map<string,int> post;
    int j = (int)(find(Mx.trans_order.begin(), Mx.trans_order.end(), tid) - Mx.trans_order.begin());
    for (size_t i=0;i<nP;++i) {
        if (Mx.Pre[i][j] > 0) pre[Mx.place_order[i]] = 1;
        if (Mx.Post[i][j] > 0) post[Mx.place_order[i]] = 1;
    }

    DdNode* en = Cudd_ReadOne(mgr); Cudd_Ref(en);
    for (size_t i=0;i<nP;++i) {
        const string& p = Mx.place_order[i];
        bool inPre  = pre.count(p);
        bool inPost = post.count(p);
        if (inPre) {
            DdNode* lit = bdd_mk_literal(mgr, C.X[i], true);
            DdNode* tmp = bdd_and(mgr, en, lit); cudd_safe_deref(mgr, en); cudd_safe_deref(mgr, lit); en = tmp;
        }
        if (inPost && !inPre) {
            // ensure capacity: cannot produce into an already-1 place
            DdNode* lit0 = bdd_mk_literal(mgr, C.X[i], false);
            DdNode* tmp = bdd_and(mgr, en, lit0); cudd_safe_deref(mgr, en); cudd_safe_deref(mgr, lit0); en = tmp;
        }
    }

    DdNode* upd = Cudd_ReadOne(mgr); Cudd_Ref(upd);
    for (size_t i=0;i<nP;++i) {
        const string& p = Mx.place_order[i];
        bool inPre  = pre.count(p);
        bool inPost = post.count(p);
        DdNode* con = nullptr;
        if (inPre && !inPost) {
            con = bdd_mk_literal(mgr, C.Xp[i], false);
        } else if (!inPre && inPost) {
            con = bdd_mk_literal(mgr, C.Xp[i], true);
        } else if (inPre && inPost) {
            con = bdd_mk_literal(mgr, C.Xp[i], true); // remains 1
        } else {
            // Xp == X
            con = bdd_xnor(mgr, C.Xp[i], C.X[i]);
        }
        DdNode* tmp = bdd_and(mgr, upd, con);
        cudd_safe_deref(mgr, upd); cudd_safe_deref(mgr, con);
        upd = tmp;
    }

    DdNode* R = bdd_and(mgr, en, upd);
    cudd_safe_deref(mgr, en);
    cudd_safe_deref(mgr, upd);
    return R;
}

static DdNode* post_image_cudd(BDDCtx& C, DdNode* S, const vector<DdNode*>& Rts) {
    // Img(S) = ⋁_t ∃X ( S(X) ∧ Rt(X,X') )  with variables X eliminated, result in X'
    DdManager* mgr = C.mgr;
    DdNode* zero = Cudd_ReadLogicZero(mgr); Cudd_Ref(zero);
    DdNode* acc = zero;
    for (auto R : Rts) {
        DdNode* conj = Cudd_bddAnd(mgr, S, R); Cudd_Ref(conj);
        DdNode* exist = Cudd_bddExistAbstract(mgr, conj, C.cubeX); Cudd_Ref(exist);
        cudd_safe_deref(mgr, conj);
        // rename X' -> X
        DdNode* ren = Cudd_bddSwapVariables(mgr, exist, C.Xp.data(), C.X.data(), C.n); Cudd_Ref(ren);
        cudd_safe_deref(mgr, exist);
        DdNode* tmp = Cudd_bddOr(mgr, acc, ren); Cudd_Ref(tmp);
        cudd_safe_deref(mgr, acc); cudd_safe_deref(mgr, ren);
        acc = tmp;
    }
    return acc; // already ref'd
}

static BDDResult bdd_fixpoint_reach(const PetriNet& net, const Matrices& Mx) {
    BDDResult result;

    if (Mx.place_order.size() != Mx.Post.size()) {
        cerr << "Internal error: matrices mismatch.\n";
        return result;
    }

    size_t nP = Mx.place_order.size();
    BDDCtx C = bdd_init_cudd((int)nP);
    auto M0 = initial_marking(net);
    DdNode* S = build_initial_1safe(M0, Mx.place_order, C);
    vector<DdNode*> Rts;

    for (const auto& t : Mx.trans_order) {
        DdNode* R = build_transition_relation_1safe(t, Mx, C);
        Rts.push_back(R);
    }

    // fixpoint S = μ Z . ( I ∨ PostImage(Z) )
    DdNode* I = S; Cudd_Ref(I);
    bool changed = true;
    size_t iter = 0;

    Stopwatch sw; sw.start();
    while (changed && iter < 10000) {
        ++iter;
        DdNode* img = post_image_cudd(C, S, Rts);
        DdNode* next = Cudd_bddOr(C.mgr, S, img);
        Cudd_Ref(next);
        cudd_safe_deref(C.mgr, img);
        changed = (next != S);
        cudd_safe_deref(C.mgr, S);
        S = next;
    }
    result.time_ms = sw.stop();

    // Count minterms (#states) for nP vars
    double states = Cudd_CountMinterm(C.mgr, S, (int)nP);

    result.state_count = (long long)states;
    result.iterations  = iter;
    result.success     = true;

    // Cleanup
    cudd_safe_deref(C.mgr, S);
    cudd_safe_deref(C.mgr, I);
    for (auto R : Rts) cudd_safe_deref(C.mgr, R);
    bdd_free_cudd(C);

    return result;
}

#else // !USE_CUDD

// Fallback "toy BDD": explicit boolean exploration for 1-safe nets.
static BDDResult bdd_fixpoint_reach(const PetriNet& net, const Matrices& Mx) {
    BDDResult result;
    cout << "[WARN] Running fallback explicit boolean engine (CUDD not enabled). "
            "Use -DUSE_CUDD for real BDD.\n";

    AnalysisConfig cfg;
    Stopwatch sw; sw.start();
    auto R = compute_reachability_explicit(net, Mx, cfg);
    result.time_ms = sw.stop();

    result.state_count = (long long)R.states.size();
    result.iterations  = 1; // fallback doesn't do iterations
    result.success     = true;

    return result;
}
#endif // USE_CUDD

// ---------------------------
// ILP modeling
// ---------------------------

struct ILPModel {
    string name;
    vector<string> var_order_M; // places
    vector<string> var_order_x; // transitions
};

// write LP: dead marking
static void write_lp_deadmarking(const Matrices& Mx,
                                 const unordered_map<string,int>& M0,
                                 int Ubound,
                                 const string& outfile_lp) {
    ofstream f(outfile_lp);
    if (!f) { cerr << "Cannot open " << outfile_lp << " for writing.\n"; return; }
    f << "\\ ILP Dead Marking via state equation\n";
    f << "Minimize\n obj: 0\nSubject To\n";
    // State equations
    for (size_t i=0;i<Mx.place_order.size();++i) {
        const string& p = Mx.place_order[i];
        f << " se_" << p << ": M_" << p << " = " << M0.at(p);
        for (size_t j=0;j<Mx.trans_order.size();++j) {
            int c = Mx.C[i][j];
            if (c==0) continue;
            f << (c>=0 ? " + " : " - ") << abs(c) << " x_" << Mx.trans_order[j];
        }
        f << "\n";
    }
    // Disabling constraints
    for (size_t j=0;j<Mx.trans_order.size();++j) {
        const string& t = Mx.trans_order[j];
        f << " dis1_" << t << ": ";
        bool first=true; int cnt=0;
        for (size_t i=0;i<Mx.place_order.size();++i) {
            int pre = Mx.Pre[i][j];
            if (pre>0) {
                if (!first) f << " + ";
                f << " s_" << Mx.place_order[i] << "_" << t;
                first=false; cnt++;
            }
        }
        if (cnt==0) {
            f << " 0 >= 1\n";
        } else {
            f << " >= 1\n";
        }
        // Witness constraints
        for (size_t i=0;i<Mx.place_order.size();++i) {
            int pre = Mx.Pre[i][j];
            if (pre>0) {
                f << " dis2_" << Mx.place_order[i] << "_" << t << ": M_" << Mx.place_order[i]
                  << " + " << Ubound << " s_" << Mx.place_order[i] << "_" << t
                  << " <= " << (pre-1 + Ubound) << "\n";
            }
        }
    }
    // Bounds
    f << "Bounds\n";
    for (auto& p : Mx.place_order)  f << " 0 <= M_" << p << " <= " << Ubound << "\n";
    for (auto& t : Mx.trans_order)  f << " x_" << t << " >= 0\n";
    // Binaries & Generals
    f << "Binaries\n";
    for (size_t j=0;j<Mx.trans_order.size();++j)
        for (size_t i=0;i<Mx.place_order.size();++i)
            if (Mx.Pre[i][j]>0) f << " s_" << Mx.place_order[i] << "_" << Mx.trans_order[j] << "\n";
    f << "Generals\n";
    for (auto& t : Mx.trans_order) f << " x_" << t << "\n";
    for (auto& p : Mx.place_order) f << " M_" << p << "\n";
    f << "End\n";
    f.close();
    cout << "Wrote LP model to: " << outfile_lp << "\n";
}

// write LP: maximize c^T M
static void write_lp_maximize(const Matrices& Mx,
                              const unordered_map<string,int>& M0,
                              int Ubound,
                              const vector<int>& c,
                              const string& outfile_lp) {
    ofstream f(outfile_lp);
    if (!f) { cerr << "Cannot open " << outfile_lp << " for writing.\n"; return; }
    f << "\\ ILP Maximize c^T M via state equation\n";
    f << "Maximize\n obj: ";
    bool first=true;
    for (size_t i=0;i<Mx.place_order.size();++i) {
        int coef = (i < c.size() ? c[i] : 0);
        if (coef==0) continue;
        if (!first) f << " + ";
        f << coef << " M_" << Mx.place_order[i];
        first=false;
    }
    if (first) f << "0";
    f << "\nSubject To\n";
    // State equations
    for (size_t i=0;i<Mx.place_order.size();++i) {
        const string& p = Mx.place_order[i];
        f << " se_" << p << ": M_" << p << " = " << M0.at(p);
        for (size_t j=0;j<Mx.trans_order.size();++j) {
            int c = Mx.C[i][j];
            if (c==0) continue;
            f << (c>=0 ? " + " : " - ") << abs(c) << " x_" << Mx.trans_order[j];
        }
        f << "\n";
    }
    // Bounds
    f << "Bounds\n";
    for (auto& p : Mx.place_order)  f << " 0 <= M_" << p << " <= " << Ubound << "\n";
    for (auto& t : Mx.trans_order)  f << " x_" << t << " >= 0\n";
    // Integrality
    f << "Generals\n";
    for (auto& t : Mx.trans_order) f << " x_" << t << "\n";
    for (auto& p : Mx.place_order) f << " M_" << p << "\n";
    f << "End\n";
    f.close();
    cout << "Wrote LP model to: " << outfile_lp << "\n";
}

#ifdef USE_GLPK
static bool solve_lp_dead_with_glpk(const Matrices& Mx,
                                    const unordered_map<string,int>& M0,
                                    int Ubound) {
    glp_prob* lp = glp_create_prob();
    glp_set_obj_dir(lp, GLP_MIN);

    int nM = (int)Mx.place_order.size();
    int nx = (int)Mx.trans_order.size();
    int ns = 0;
    for (size_t j=0;j<Mx.trans_order.size();++j)
        for (size_t i=0;i<Mx.place_order.size();++i)
            if (Mx.Pre[i][j]>0) ns++;

    int ncols = nM + nx + ns;
    glp_add_cols(lp, ncols);

    // M_p
    for (int i=0;i<nM;++i) {
        int col = i+1;
        glp_set_col_name(lp, col, ("M_"+Mx.place_order[i]).c_str());
        glp_set_col_bnds(lp, col, GLP_DB, 0.0, (double)Ubound);
        glp_set_col_kind(lp, col, GLP_IV);
        glp_set_obj_coef(lp, col, 0.0);
    }
    // x_t
    for (int j=0;j<nx;++j) {
        int col = nM + j + 1;
        glp_set_col_name(lp, col, ("x_"+Mx.trans_order[j]).c_str());
        glp_set_col_bnds(lp, col, GLP_LO, 0.0, 0.0);
        glp_set_col_kind(lp, col, GLP_IV);
        glp_set_obj_coef(lp, col, 0.0);
    }
    // s_{p,t}
    int baseS = nM + nx;
    int sIndex = 0;
    vector<pair<int,int>> map_s;
    for (int j=0;j<nx;++j) {
        for (int i=0;i<nM;++i) {
            if (Mx.Pre[i][j]>0) {
                int col = baseS + (++sIndex);
                string nm = "s_" + Mx.place_order[i] + "_" + Mx.trans_order[j];
                glp_set_col_name(lp, col, nm.c_str());
                glp_set_col_bnds(lp, col, GLP_DB, 0.0, 1.0);
                glp_set_col_kind(lp, col, GLP_BV);
                glp_set_obj_coef(lp, col, 0.0);
                map_s.push_back({i,j});
            }
        }
    }

    // Rows
    int nRows = 0;
    int nSE = nM;
    int nDis1 = nx;
    int nDis2 = sIndex;
    glp_add_rows(lp, nSE + nDis1 + nDis2);

    // State equations
    int row = 0;
    for (int i=0;i<nM;++i) {
        row++;
        glp_set_row_name(lp, row, ("se_"+Mx.place_order[i]).c_str());
        glp_set_row_bnds(lp, row, GLP_FX, (double)M0.at(Mx.place_order[i]), (double)M0.at(Mx.place_order[i]));
    }

    // dis1
    for (int j=0;j<nx;++j) {
        row++;
        glp_set_row_name(lp, row, ("dis1_"+Mx.trans_order[j]).c_str());
        bool hasPre=false;
        for (int i=0;i<nM;++i) if (Mx.Pre[i][j]>0) { hasPre=true; break; }
        glp_set_row_bnds(lp, row, GLP_LO, 1.0, 0.0); // nếu không có hệ số -> 0 >= 1 (block)
    }

    // dis2
    for (int k=0;k<sIndex;++k) {
        row++;
        int i = map_s[k].first;
        int j = map_s[k].second;
        int rhs = Mx.Pre[i][j] - 1;
        glp_set_row_name(lp, row, ("dis2_"+Mx.place_order[i]+"_"+Mx.trans_order[j]).c_str());
        glp_set_row_bnds(lp, row, GLP_UP, -1e30, (double)rhs + Ubound);
    }

    // Sparse matrix
    int nnz = 0;
    for (int i=0;i<nM;++i) {
        nnz++; // M_i
        for (int j=0;j<nx;++j) if (Mx.C[i][j]!=0) nnz++;
    }
    for (int j=0;j<nx;++j)
        for (int k=0;k<sIndex;++k) if (map_s[k].second==j) nnz++;
    nnz += 2*sIndex;

    vector<int> ia(nnz+1), ja(nnz+1);
    vector<double> ar(nnz+1);
    int ptr = 0;

    // SE rows
    row = 0;
    for (int i=0;i<nM;++i) {
        row++;
        ptr++; ia[ptr]=row; ja[ptr]= i+1; ar[ptr]= 1.0; // M_i
        for (int j=0;j<nx;++j) {
            if (Mx.C[i][j]==0) continue;
            ptr++; ia[ptr]=row; ja[ptr]= nM + j + 1; ar[ptr]= (double)Mx.C[i][j];
        }
    }
    // dis1 rows
    for (int j=0;j<nx;++j) {
        row++;
        for (int k=0;k<sIndex;++k) {
            if (map_s[k].second != j) continue;
            ptr++; ia[ptr]=row; ja[ptr]= nM + nx + k + 1; ar[ptr]= 1.0;
        }
    }
    // dis2 rows
    for (int k=0;k<sIndex;++k) {
        row++;
        int i = map_s[k].first;
        ptr++; ia[ptr]=row; ja[ptr]= i+1;                ar[ptr]= 1.0;           // M_i
        ptr++; ia[ptr]=row; ja[ptr]= nM + nx + k + 1;    ar[ptr]= (double)Ubound; // +U*s
    }

    glp_load_matrix(lp, ptr, ia.data(), ja.data(), ar.data());

    glp_iocp parm; glp_init_iocp(&parm); parm.msg_lev = GLP_MSG_ON; parm.presolve = GLP_ON;
    int ret = glp_intopt(lp, &parm);
    if (ret != 0) { cerr << "GLPK intopt failed, code " << ret << "\n"; glp_delete_prob(lp); return false; }
    int status = glp_mip_status(lp);
    cout << "GLPK MIP status: " << status << " (1=optimal, 5=feasible)\n";
    if (status==GLP_OPT || status==GLP_FEAS) {
        cout << "Found a candidate dead marking (state equation):\n";
        for (int i=0;i<nM;++i) {
            double v = glp_mip_col_val(lp, i+1);
            cout << "  " << Mx.place_order[i] << " = " << (long long) llround(v) << "\n";
        }
        glp_delete_prob(lp);
        return true;
    } else {
        cout << "No feasible dead marking (under this ILP model).\n";
        glp_delete_prob(lp);
        return false;
    }
}

static bool solve_lp_max_with_glpk(const Matrices& Mx,
                                   const unordered_map<string,int>& M0,
                                   int Ubound,
                                   const vector<int>& c) {
    glp_prob* lp = glp_create_prob();
    glp_set_obj_dir(lp, GLP_MAX);

    int nM = (int)Mx.place_order.size();
    int nx = (int)Mx.trans_order.size();
    glp_add_cols(lp, nM + nx);

    // M_i vars
    for (int i=0;i<nM;++i) {
        int col = i+1;
        glp_set_col_name(lp, col, ("M_"+Mx.place_order[i]).c_str());
        glp_set_col_bnds(lp, col, GLP_DB, 0.0, (double)Ubound);
        glp_set_col_kind(lp, col, GLP_IV);
        double coef = (i < (int)c.size()? c[i] : 0.0);
        glp_set_obj_coef(lp, col, coef);
    }
    // x_j vars
    for (int j=0;j<nx;++j) {
        int col = nM + j + 1;
        glp_set_col_name(lp, col, ("x_"+Mx.trans_order[j]).c_str());
        glp_set_col_bnds(lp, col, GLP_LO, 0.0, 0.0);
        glp_set_col_kind(lp, col, GLP_IV);
        glp_set_obj_coef(lp, col, 0.0);
    }

    // Rows: state equations
    glp_add_rows(lp, nM);
    int nnz = 0;
    for (int i=0;i<nM;++i) {
        nnz++; // M_i
        for (int j=0;j<nx;++j) if (Mx.C[i][j]!=0) nnz++;
    }
    vector<int> ia(nnz+1), ja(nnz+1);
    vector<double> ar(nnz+1);
    int ptr=0;
    for (int i=0;i<nM;++i) {
        glp_set_row_name(lp, i+1, ("se_"+Mx.place_order[i]).c_str());
        glp_set_row_bnds(lp, i+1, GLP_FX, (double)M0.at(Mx.place_order[i]), (double)M0.at(Mx.place_order[i]));
        // M_i coef 1
        ptr++; ia[ptr]=i+1; ja[ptr]= i+1; ar[ptr]=1.0;
        for (int j=0;j<nx;++j) {
            if (Mx.C[i][j]==0) continue;
            ptr++; ia[ptr]=i+1; ja[ptr]= nM + j + 1; ar[ptr]= -(double)Mx.C[i][j];
        }
    }
    glp_load_matrix(lp, ptr, ia.data(), ja.data(), ar.data());

    glp_iocp parm; glp_init_iocp(&parm); parm.msg_lev = GLP_MSG_ON; parm.presolve = GLP_ON;
    int ret = glp_intopt(lp, &parm);
    if (ret != 0) { cerr << "GLPK intopt failed, code " << ret << "\n"; glp_delete_prob(lp); return false; }
    int status = glp_mip_status(lp);
    cout << "GLPK MIP status: " << status << " (1=optimal, 5=feasible)\n";
    if (status==GLP_OPT || status==GLP_FEAS) {
        cout << "Optimal/feasible marking M:\n";
        for (int i=0;i<nM;++i) {
            double v = glp_mip_col_val(lp, i+1);
            cout << "  " << Mx.place_order[i] << " = " << (long long) llround(v) << "\n";
        }
        cout << "Objective value: " << glp_mip_obj_val(lp) << "\n";
        glp_delete_prob(lp);
        return true;
    } else {
        cout << "No feasible solution under bounds.\n";
        glp_delete_prob(lp);
        return false;
    }
}
#endif // USE_GLPK

// ---------------------------
// Command-line parsing helpers
// ---------------------------

struct CLI {
    string pnml;
    bool do_explicit=false;
    bool do_bdd=false;
    bool do_ilp_dead=false;
    bool do_ilp_max=false;
    vector<int> cvec;
    int Ubound = 1; // default 1-safe bound
};

static vector<string> split_csv(const string& s) {
    vector<string> out;
    string token;
    stringstream ss(s);
    while (getline(ss, token, ',')) out.push_back(trim(token));
    return out;
}

static CLI parse_cli(int argc, char** argv) {
    CLI cli;
    if (argc>=2) cli.pnml = argv[1];
    for (int i=2;i<argc;i++) {
        string a = argv[i];
        if (a == "--explicit") cli.do_explicit = true;
        else if (a == "--bdd") cli.do_bdd = true;
        else if (a == "--ilp-dead") cli.do_ilp_dead = true;
        else if (a == "--ilp-max") {
            cli.do_ilp_max = true;
            if (i+1 < argc) {
                auto parts = split_csv(argv[++i]);
                for (auto& t : parts) cli.cvec.push_back(stoi(t));
            }
        } else if (a == "--bound") {
            if (i+1 < argc) cli.Ubound = stoi(argv[++i]);
        }
    }
    if (!cli.do_explicit && !cli.do_bdd && !cli.do_ilp_dead && !cli.do_ilp_max) {
        // default to explicit
        cli.do_explicit = true;
    }
    return cli;
}

// ---------------------------
// Main
// ---------------------------

int main(int argc, char** argv) {
    try {
        CLI cli = parse_cli(argc, argv);
        if (cli.pnml.empty()) {
            cerr << "Usage: " << argv[0] << " <model.pnml> [--explicit] [--bdd] [--ilp-dead|--ilp-max c1,c2,...] [--bound U]\n";
            return 1;
        }

        double t_total = 0.0;

        // --- Parse PNML
        Stopwatch sw_parse; sw_parse.start();
        PetriNet net = parse_pnml(cli.pnml);
        double dt_parse = sw_parse.stop();
        t_total += dt_parse;
        cout << "[time] Parse PNML: " << fmt_ms(dt_parse) << " ms\n";
        print_mem_now("(after parse)");

        print_net_structure(net);

        // --- Build matrices
        Stopwatch sw_build; sw_build.start();
        auto Mx = build_matrices(net);
        double dt_build = sw_build.stop();
        t_total += dt_build;
        cout << "[time] Build matrices: " << fmt_ms(dt_build) << " ms\n";
        print_mem_now("(after build)");

        print_matrix(Mx.Pre,  Mx.place_order, Mx.trans_order, "Pre");
        print_matrix(Mx.Post, Mx.place_order, Mx.trans_order, "Post");
        print_matrix(Mx.C,    Mx.place_order, Mx.trans_order, "C = Post - Pre");

        // --- Explicit BFS
        if (cli.do_explicit) {
            cout << "\n=======================================\n";
            cout << "--- Explicit Reachability (BFS, weighted) ---\n";

            print_mem_now("(before explicit BFS)");
            AnalysisConfig cfg;
            Stopwatch sw_exp; sw_exp.start();

            auto R = compute_reachability_explicit(net, Mx, cfg);

            double dt_exp = sw_exp.stop();
            t_total += dt_exp;

            cout << "[time] Explicit BFS: " << fmt_ms(dt_exp) << " ms\n";
            print_mem_now("(after explicit BFS)");

            cout << "Visited states: " << R.states.size()
                 << "  | explored nodes: " << R.explored
                 << "  | finished=" << (R.finished ? "yes" : "no (hit limits)") << "\n";

            cout << "[EXPLICIT] Performance: Time=" << fmt_ms(dt_exp)
                 << "ms, States=" << R.states.size()
                 << ", Memory usage reported above\n";

            size_t cap = std::min<size_t>(R.states.size(), 100);
            cout << (R.states.size()>cap ? "Showing first " : "All Reachable Markings (")
                 << cap
                 << (R.states.size()>cap ? " of " + to_string(R.states.size()) + " " : to_string(R.states.size()) + " ")
                 << "total):\n";
            for (size_t i=0;i<cap;++i) {
                cout << "M" << i << ": (";
                for (size_t k=0;k<Mx.place_order.size();++k) {
                    const string& p = Mx.place_order[k];
                    cout << p << "=" << R.states[i].at(p);
                    if (k+1<Mx.place_order.size()) cout << ", ";
                }
                cout << ")\n";
            }
        }

        // --- BDD reachability (1-safe)
        if (cli.do_bdd) {
            cout << "\n=======================================\n";
            cout << "--- Symbolic Reachability (BDD, 1-safe) ---\n";
            if (cli.Ubound != 1) {
                cout << "[WARN] BDD mode currently assumes 1-safe. Ignoring --bound " << cli.Ubound << ".\n";
            }

            print_mem_now("(before BDD)");
            Stopwatch sw_bdd; sw_bdd.start();

            BDDResult bdd_result = bdd_fixpoint_reach(net, Mx);

            double dt_bdd = sw_bdd.stop();
            // thời gian BDD đã đo bên trong bdd_fixpoint_reach, ta ưu tiên bdd_result.time_ms (nội bộ)
            if (bdd_result.time_ms <= 0.0) bdd_result.time_ms = dt_bdd;
            t_total += bdd_result.time_ms;

            if (bdd_result.success) {
                cout << "[BDD] Fixpoint iterations: " << bdd_result.iterations << "\n";
                cout << "[BDD] #Reachable states (1-safe): " << bdd_result.state_count << "\n";
                cout << "[time] BDD reachability: " << fmt_ms(bdd_result.time_ms) << " ms\n";
            } else {
                cout << "[BDD] Error in BDD computation\n";
            }

            print_mem_now("(after BDD)");

            cout << "[BDD] Performance: Time=" << fmt_ms(bdd_result.time_ms)
                 << "ms, States=" << bdd_result.state_count
                 << ", Memory usage reported above\n";
        }

        // --- ILP parts
        if (cli.do_ilp_dead) {
            cout << "\n=======================================\n";
            cout << "--- ILP: Dead Marking via State Equation ---\n";
#ifdef USE_GLPK
            bool ok = solve_lp_dead_with_glpk(Mx, initial_marking(net), cli.Ubound);
            if (!ok) {
                cout << "Falling back to writing LP file.\n";
                write_lp_deadmarking(Mx, initial_marking(net), cli.Ubound, "model_dead.lp");
                cout << "You can solve 'model_dead.lp' with GLPK, Gurobi, or CPLEX.\n";
            }
#else
            write_lp_deadmarking(Mx, initial_marking(net), cli.Ubound, "model_dead.lp");
            cout << "GLPK not enabled. Wrote 'model_dead.lp'.\n";
#endif
        }

        if (cli.do_ilp_max) {
            cout << "\n=======================================\n";
            cout << "--- ILP: Maximize c^T M via State Equation ---\n";
#ifdef USE_GLPK
            bool ok = solve_lp_max_with_glpk(Mx, initial_marking(net), cli.Ubound, cli.cvec);
            if (!ok) {
                cout << "Falling back to writing LP file.\n";
                write_lp_maximize(Mx, initial_marking(net), cli.Ubound, cli.cvec, "model_max.lp");
            }
#else
            write_lp_maximize(Mx, initial_marking(net), cli.Ubound, cli.cvec, "model_max.lp");
            cout << "GLPK not enabled. Wrote 'model_max.lp'.\n";
#endif
        }

        cout << "\n[time] TOTAL: " << fmt_ms(t_total) << " ms\n";
        print_mem_now("[mem ] FINAL");
        cout << "\nDone.\n";
    } catch (const std::exception& e) {
        cerr << "\nFATAL ERROR: " << e.what() << "\n";
        return 1;
    }
    return 0;
}
