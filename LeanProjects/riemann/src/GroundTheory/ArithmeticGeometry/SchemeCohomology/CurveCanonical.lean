import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveDivisors
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveProper
import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorTensor
import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorInvertible
import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorPicard
import GroundTheory.FunctionField.DivisorDegree
import GroundTheory.FunctionField.WeilDifferential

open CategoryTheory AlgebraicGeometry Order Topology Module MonoidalCategory

universe u

namespace GroundTheory.Arith.SchemeCoh

open GroundTheory.FunctionField

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]
  [IsNoetherian X] [IsLocallyFactorial X] [IsProper (X ↘ Spec (.of k))]
  [IsFunctionField k X.functionField]

omit [IsProper (X ↘ Spec (.of k))] [IsFunctionField k X.functionField] in

noncomputable def invertibleDegree {L : X.Modules} (hL : IsInvertibleSheaf L) : ℤ :=
  WeilDivisor.degree (k := k) (divisorOfInvertible hL)

omit [IsProper (X ↘ Spec (.of k))] [IsFunctionField k X.functionField] in

lemma nonempty_iso_of_weilDivisorToPic {M : X.Modules} (hM : IsInvertibleSheaf M)
    {D : WeilDivisor X} (h : Additive.ofMul (Pic.mk M hM) = weilDivisorToPic D) :
    Nonempty (M ≅ divisorSheaf D) := by
  rw [weilDivisorToPic_apply] at h
  exact (Pic.mk_eq_mk_iff _ _).mp (Additive.ofMul.injective h)

omit [IsProper (X ↘ Spec (.of k))] [IsFunctionField k X.functionField] in

theorem nonempty_tensor_dualSheaf_iso (D : WeilDivisor X) {L : X.Modules}
    (hL : IsInvertibleSheaf L) {E : WeilDivisor X} (e : L ≅ divisorSheaf E) :
    Nonempty (divisorSheaf D ⊗ dualSheaf L ≅ divisorSheaf (D - E)) := by
  refine nonempty_iso_of_weilDivisorToPic ((isInvertibleSheaf_divisorSheaf D).tensor hL.dual) ?_
  have hLE : Pic.mk L hL = Pic.mk (divisorSheaf E) (isInvertibleSheaf_divisorSheaf E) :=
    (Pic.mk_eq_mk_iff _ _).mpr ⟨e⟩
  rw [Pic.mk_tensor (isInvertibleSheaf_divisorSheaf D) hL.dual, Pic.mk_dualSheaf hL, hLE, map_sub,
    weilDivisorToPic_apply, weilDivisorToPic_apply, ofMul_mul, ofMul_inv, sub_eq_add_neg]

variable (hX : topologicalKrullDim X ≤ 1)

noncomputable def canonicalDifferential : WeilDifferential k X.functionField :=
  (WeilDifferential.exists_ne_zero (k := k) (K := X.functionField)).choose

omit [AlgebraicGeometry.IsNoetherian X] [IsLocallyFactorial X] [IsProper (X ↘ Spec (.of k))] in
lemma canonicalDifferential_ne_zero : canonicalDifferential (k := k) (X := X) ≠ 0 :=
  (WeilDifferential.exists_ne_zero (k := k) (K := X.functionField)).choose_spec

noncomputable def canonicalDivisor : WeilDivisor X :=
  (divisorEquiv (k := k) hX).symm (canonicalDifferential (k := k) (X := X)).divisor

lemma divisorEquiv_canonicalDivisor :
    divisorEquiv (k := k) hX (canonicalDivisor (k := k) hX) =
      (canonicalDifferential (k := k) (X := X)).divisor := by
  simp [canonicalDivisor]

noncomputable def canonicalSheaf : X.Modules :=
  divisorSheaf (canonicalDivisor (k := k) hX)

end GroundTheory.Arith.SchemeCoh
