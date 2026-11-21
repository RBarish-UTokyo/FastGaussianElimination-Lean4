module

public import FastGE.Main

/-!
# Solution for `FastGEChallenge.lean`

The six theorems of `FastGEChallenge.lean` are the theorems of the same names in
`FastGE/Main.lean`, about the definitions of the specification modules `FastGE/Spec.lean`,
`NestedDissection/Spec.lean`, `WordRAM/AlgebraicSpec.lean` and `Kasteleyn/Spec.lean`. This
module imports the library and never imports `FastGEChallenge`.

* `FastGE.strassen_count : FastGE.StrassenCount`
* `FastGE.strassen_exponent : FastGE.StrassenExponent`
* `FastGE.inverse_determinant : FastGE.InverseDeterminant`
* `FastGE.planar_fast_determinant : FastGE.PlanarFastDeterminant`
* `FastGE.square_fast_determinant : FastGE.SquareFastDeterminant`
* `FastGE.square_fast_determinant_posDef : FastGE.SquareFastDeterminantPosDef`
-/
