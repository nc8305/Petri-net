\ ILP Maximize c^T M via state equation
Maximize
 obj: 10 M_P1 + 1 M_P3 + 1 M_P4
Subject To
 se_P1: M_P1 = 1
 se_P2: M_P2 = 0 - 1 x_T1 + 1 x_T2
 se_P3: M_P3 = 0 + 1 x_T1 - 1 x_T2
 se_P4: M_P4 = 1
Bounds
 0 <= M_P1 <= 1
 0 <= M_P2 <= 1
 0 <= M_P3 <= 1
 0 <= M_P4 <= 1
 x_T1 >= 0
 x_T2 >= 0
Generals
 x_T1
 x_T2
 M_P1
 M_P2
 M_P3
 M_P4
End
