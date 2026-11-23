import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfHermitianMultiplicationModel
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_eq_of_hermitianMultiplicationModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (γ : GLw n w), Q.Monic → Fits w e B Q u → IsModel w e B u x γ → γ.val.charpoly = Q := by
  first | exact @GlobalTheory.KapLat.charpoly_of_model | exact GlobalTheory.KapLat.charpoly_of_model | (intros; apply GlobalTheory.KapLat.charpoly_of_model <;> assumption)
