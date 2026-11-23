import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorsModerateGrowthSmoothFrechetRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vectors_moderate_growth_smooth_frechet_rep : ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (ρ : Mx n → (E →L[ℂ] E)), ModRep ε ρ → IsClosed (Fam ε ρ : Set (List (lie (Jm ε)) → E)) ∧ ∃ (p : ℕ → Seminorm ℂ (Fam ε ρ)) (π dπ : Mx n → (Fam ε ρ →L[ℂ] Fam ε ρ)), IsSmoothModRep ε p π dπ ∧ (∀ (g : Mx n) (hg : g ∈ UJset ε) (v : Fam ε ρ) (l : List (lie (Jm ε))), (π g v).1 l = ρ g (v.1 (l.map (adInv hg)))) ∧ (∀ (X : lie (Jm ε)) (v : Fam ε ρ) (l : List (lie (Jm ε))), (dπ (X : Mx n) v).1 l = v.1 (l ++ [X])) ∧ ∀ v : Fam ε ρ, ‖v.1 []‖ ≤ p 0 v := by
  first | exact @GlobalTheory.TypeSum.SmoothFrechet.smooth_frechet_rep | exact GlobalTheory.TypeSum.SmoothFrechet.smooth_frechet_rep | (intros; apply GlobalTheory.TypeSum.SmoothFrechet.smooth_frechet_rep <;> assumption)
