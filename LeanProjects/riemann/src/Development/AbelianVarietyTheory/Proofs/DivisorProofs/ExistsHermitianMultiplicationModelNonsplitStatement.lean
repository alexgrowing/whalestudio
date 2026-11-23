import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianMultiplicationModelNonsplit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitianMultiplicationModel_nonsplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u : B.A), Q.Separable → Fits w e B Q u → ∀ γ : GLw n w, γ ∈ UL n w → γ.val.charpoly = Q → ∃ x : B.A, B.σ x = x ∧ IsUnit x ∧ IsModel w e B u x γ := by
  first | exact @GlobalTheory.KapLat.ExModel.exists_isModel | exact GlobalTheory.KapLat.ExModel.exists_isModel | (intros; apply GlobalTheory.KapLat.ExModel.exists_isModel <;> assumption)
