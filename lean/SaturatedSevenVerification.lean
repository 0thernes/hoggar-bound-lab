/- Axiom audit for the exact contextuality degree of the seven-qubit configuration
   (publication/ADDENDUM-seven-qubit-lean.md).  No line may report an axiom other than
   propext, Classical.choice and Quot.sound.

   run:  cd lean && lake build HoggarBound.SaturatedPhaseSeven && lake env lean SaturatedSevenVerification.lean -/
import HoggarBound.SaturatedPhaseSeven

-- packed sets: the number of elements is the remainder modulo 2^b - 1
#print axioms HoggarBound.Packed.card
-- the sign of a context of two commuting codes, as an exclusive or of five bits
#print axioms HoggarBound.sign_table
#print axioms HoggarBound.viol_bit
-- one row evaluated on packed sets is the row of the double sum, for every number of qubits
#print axioms HoggarBound.flagRow_eq_fast
#print axioms HoggarBound.violRow_eq_fast
-- the counts of a mask configuration as sums of such rows
#print axioms HoggarBound.card_cfg_fast
#print axioms HoggarBound.card_flags_cfg_fast
#print axioms HoggarBound.card_violated_cfg_fast
-- seven qubits: observables, flags and violated flags, evaluated by the kernel
#print axioms HoggarBound.phase7_card
#print axioms HoggarBound.phase7_flags
#print axioms HoggarBound.phase7_witness
-- seven qubits: the support of the phase state of Theorem 13 (8128 observables, 2824192 contexts)
#print axioms HoggarBound.phase7_degree
#print axioms HoggarBound.phase7_contexts
