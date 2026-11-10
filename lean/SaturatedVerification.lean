/- Axiom audit for the exact contextuality degrees of the configurations that attain the spectral floor
   (paper, Section 5 and Table 3).  Every line must report [propext, Classical.choice, Quot.sound].

   run:  cd lean && lake build HoggarBound.Saturated HoggarBound.SaturatedPhaseFive && lake env lean SaturatedVerification.lean -/
import HoggarBound.Saturated
import HoggarBound.SaturatedPhaseFive

-- the general bridge from bit masks to configurations of explicit Pauli matrices
#print axioms HoggarBound.card_flags_cfg
#print axioms HoggarBound.card_violated_cfg
#print axioms HoggarBound.degree_of_certificate
#print axioms HoggarBound.contexts_of_flags

-- two qubits: the 12 observables outside a maximal commuting set (Liu-Low-Yin state)
#print axioms HoggarBound.lly_degree
-- three qubits: the 28 real non-diagonal observables (CCZ state), and all 63 (Hoggar fiducial)
#print axioms HoggarBound.ccz_degree
#print axioms HoggarBound.hoggar_degree
-- four qubits: the hyperbolic quadric, and the pivot configuration S_B (new)
#print axioms HoggarBound.quadric_degree
#print axioms HoggarBound.pivot_degree
#print axioms HoggarBound.pivot_contexts
-- five qubits: the support S_5 of Cieslinski's state (degree new)
#print axioms HoggarBound.cieslinski5_degree
#print axioms HoggarBound.cieslinski5_contexts
-- five qubits: the support of the phase state CCZ(0,1,4) CCZ(0,2,3) CS(0,1) CS(1,3) CS(2,4) |+++++> (new)
#print axioms HoggarBound.phase5_degree
#print axioms HoggarBound.phase5_contexts
