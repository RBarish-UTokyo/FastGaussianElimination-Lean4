module

import FastGESolution
import WordRAM
import Kasteleyn
import NestedDissection
import PlanarSeparator
import FastGE

/-!
# Axiom audit

Prints the axioms of the 6 compared theorems (stated in `FastGEChallenge.lean`, proved by
`FastGESolution.lean`) and of 23 further theorems of the libraries. Every report must name only
`propext`, `Classical.choice` and `Quot.sound`. Run it with

    lake build && lake env lean Audit.lean
-/

-- The compared theorems
#print axioms FastGE.strassen_count
#print axioms FastGE.strassen_exponent
#print axioms FastGE.inverse_determinant
#print axioms FastGE.planar_fast_determinant
#print axioms FastGE.square_fast_determinant
#print axioms FastGE.square_fast_determinant_posDef

-- Further theorems of the libraries
#print axioms PlanarSeparator.planar_separator
#print axioms PlanarSeparator.planar_separator_induce
#print axioms PlanarSeparator.planar_separator_card
#print axioms PlanarSeparator.exists_sepTree
#print axioms PlanarSeparator.exists_sepTree_square
#print axioms PlanarSeparator.planar_nestedDissection_elimination
#print axioms PlanarSeparator.square_nestedDissection_elimination
#print axioms NestedDissection.card_edgeFinset_fill_le
#print axioms NestedDissection.nestedDissection_elimination
#print axioms NestedDissection.nestedDissection_det
#print axioms NestedDissection.fill_adj_iff_path
#print axioms FastGE.Strassen.strassen_val
#print axioms FastGE.Strassen.strassen_cost
#print axioms FastGE.MatMulAlgorithm.strassen_hasExponent
#print axioms FastGE.FastDet.invDet_val
#print axioms FastGE.FastDet.invDet_cost_le_rpow
#print axioms FastGE.FastDet.invDet_strassen_cost_le
#print axioms FastGE.FastDissection.nestedDissection_fast
#print axioms FastGE.FastDissection.nestedDissection_strassen
#print axioms FastGE.FastDissection.planar_nestedDissection_fast
#print axioms FastGE.FastDissection.square_nestedDissection_fast
#print axioms NestedDissection.det_eq_prod_pivots
#print axioms FastGE.FastDissection.square_nestedDissection_fast_of_posDef
