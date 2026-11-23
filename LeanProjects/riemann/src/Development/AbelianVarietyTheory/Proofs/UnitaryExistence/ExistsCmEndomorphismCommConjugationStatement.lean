import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCmEndomorphismCommConjugation
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmEndomorphism_comm_conjugation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (C : Curve H), ∃ W : C.P.A ⟶ C.P.A, IsMonHom W ∧ (∀ z, C.pt z ≫ W.left = C.pt (wC H (0, 1) * z)) ∧ (∀ z z', C.pt z = C.pt z' ↔ ∃ a, z - z' = wC H a) ∧ (∀ x : Sp ℂ ⟶ C.P.A.left, x ≫ C.P.A.hom = 𝟙 _ → ∃ z, C.pt z = x) ∧ ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ io : C.P.A.left ⟶ C.P.A.left, IsGrpPullback C.P.A C.P.A (spMap (τ : ℂ →+* ℂ)) io → W.left ≫ io = io ≫ W.left := by
  first | exact @GlobalTheory.CurveEndo.exists_endo_comm | exact GlobalTheory.CurveEndo.exists_endo_comm | (intros; apply GlobalTheory.CurveEndo.exists_endo_comm <;> assumption)
