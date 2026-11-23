import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjOfFrobeniusMatch
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_of_frobenius_match : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), FrobDense D → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : D.naut.CG a) (s : ℝ) (r r' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)), IsAttachedAway D T ι π s r → Continuous (fun g => (r' g : Matrix (Fin a) (Fin a) (Qbar l))) → IsSSRep r' → FrobMatch D π ι.toRingHom r' (s + (1 - (a : ℝ)) / 2) → ∃ A : GL (Fin a) (Qbar l), ∀ g, r' g = A * r g * A⁻¹ := by
  first | exact @GlobalTheory.TripleLocal.conj_of_frobMatch | exact GlobalTheory.TripleLocal.conj_of_frobMatch | (intros; apply GlobalTheory.TripleLocal.conj_of_frobMatch <;> assumption)
