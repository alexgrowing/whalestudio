import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieCombOneIffComp
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CurveHomExtOfDerivativeLieBasisStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.LieMultiple

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isLieComb_natCast_pow {v : epsR R ⟶ G} (hv : IsTangent v) (n : ℕ) :
    IsLieComb ![(n : R)] ![v] (v ^ n) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, pow_zero]
    exact (lieMultiple_calculus R G G v v v 0 0).2.2.2.2.2 hv
  | succ n ih =>
    rw [Nat.cast_succ, pow_succ]
    exact (lieMultiple_calculus R G G v _ v n 1).2.1 hv ih
      (lieMultiple_calculus R G G v v v 0 0).2.2.2.2.1

theorem isMonHom_id_pow [IsCommMonObj G] (n : ℕ) : IsMonHom ((𝟙 G) ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))
  | succ n ih =>
    rw [pow_succ]
    exact inferInstanceAs (IsMonHom (lift ((𝟙 G) ^ n) (𝟙 G) ≫ μ[G]))

theorem quadratic_equation_of_derivative : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (k : Type) [Field k] (s : k →+* ℂ) (P : Out.PolAV (Sp k)) (v : epsR k ⟶ P.A) (W : P.A ⟶ P.A) (w : k) (n : ℕ), IsTangent v → (∀ (R' : Type) [CommRing R'] (f' : k →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) → IsMonHom W → IsLieComb ![w] ![v] (v ≫ W) → w * w + n = w → (W ≫ W) * (𝟙 P.A) ^ n = W := by
  intro hT hB k _ s P v W w n hv hb hW hw heq
  have hc := P.isAb.comm
  have h1 := isMonHom_id_pow (G := P.A) n
  have h2 : IsMonHom ((W ≫ W) * (𝟙 P.A) ^ n) :=
    inferInstanceAs (IsMonHom (lift (W ≫ W) ((𝟙 P.A) ^ n) ≫ μ[P.A]))
  refine GlobalTheory.T.curve_hom_ext_of_derivative_lieBasis hT hB k s P P v _ _ hb h2 hW ?_
  have h3 : IsLieComb ![w] ![v ≫ W] ((v ≫ W) ≫ W) :=
    (lieMultiple_calculus k P.A P.A v _ v w w).2.2.2.1 W hw
  have h4 : IsLieComb ![w * w] ![v] ((v ≫ W) ≫ W) :=
    (lieMultiple_calculus k P.A P.A v _ _ w w).2.2.1 hw h3
  have h5 : IsLieComb ![w * w + n] ![v] (((v ≫ W) ≫ W) * v ^ n) :=
    (lieMultiple_calculus k P.A P.A v _ _ (w * w) n).2.1 hv h4 (isLieComb_natCast_pow hv n)
  rw [heq, isLieComb_one_iff_comp] at h5
  rw [isLieComb_one_iff_comp] at hw
  rw [MonObj.comp_mul, MonObj.comp_pow, Category.comp_id, ← Category.assoc, h5, ← hw]

end GlobalTheory.LieMultiple
