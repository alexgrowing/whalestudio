import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.YvEqSumMinorsGMat
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.yv_eq_sum_minors_gMat : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), ∀ r k, blkF Ψ p q K₀ r = some k → ∀ i : idx J₀ n k, yv A x₀ ⟨k, i⟩ = ∑ I, algebraMap Ω (GenField Ω (rk Ψ p q)) (coefF A ⟨k, i⟩ I) * minorIJ (gMat p q Ω r.1) I (stepCols (p + q) p r.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.BlockEmbeddings.yv_step | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.BlockEmbeddings.yv_step | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.BlockEmbeddings.yv_step <;> assumption)
