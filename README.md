# Petri_net

## Description
Petri_net is a tool for analyzing Petri nets (PNML format) with features including:
- Reachability and deadlock analysis
- Marking optimization (ILP)
- Support for ILP solving via GLPK and symbolic reachability via BDD/CUDD

## System Requirements
- C++17
- GLPK (`libglpk-dev`)
- CUDD (manual installation, see below)
- Python (optional, for supporting scripts)

## Library Installation
### GLPK
```sh
sudo apt-get update
sudo apt-get install libglpk-dev
```

### CUDD
```sh
sudo apt-get install automake autoconf m4 perl
cd cudd
./configure --prefix=/usr/local
make
sudo make install
```
If `cudd.h` is not found, use:
```sh
g++ ... -I./cudd/cudd -L/usr/local/lib -lcudd -lutil -lm -DUSE_CUDD ...
```

## Build
```sh
g++ -std=c++17 petri_net.cpp tinyxml2.cpp -lglpk -DUSE_GLPK -O2 -o petri_net
# Or with CUDD:
g++ -std=c++17 petri_net.cpp tinyxml2.cpp -I/usr/local/include -L/usr/local/lib -lcudd -lutil -lm -DUSE_CUDD -O2 -o petri_net
# Or both:
g++ -std=c++17 petri_net.cpp tinyxml2.cpp -I/usr/local/include -L/usr/local/lib -lcudd -lutil -lglpk -lm -DUSE_CUDD -DUSE_GLPK -O2 -o petri_net
```

## Usage
```sh
./petri_net hi.pnml --ilp-max 10,0,1,1   # optimize marking with GLPK
./petri_net example.pnml                 # analyze Petri net
```

## Configuration Files
- `requirements.txt`: library installation instructions, Python packages (if needed)
- `model_max.lp`: ILP template for marking optimization
- `example.pnml`, `hi.pnml`: Petri net examples

## Contributing & Contact
- Contribute via GitHub Pull Request
- Contact: [Your Name] (add email if desired)

