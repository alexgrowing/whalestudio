import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointLinearFunctionalCm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit Classical
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_linear_functional_cm : ∀ {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (φ : E →+* C), ∃ (m : ℕ) (u : Fin m → P.T) (ℓ : Fin m → (P.T →ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] 𝓞 E)) (e : ℤ_[p] ⊗[ℤ] 𝓞 E), (∀ j a t, ℓ j (P.actT a t) = (1 ⊗ₜ a) * ℓ j t) ∧ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (embO P.integers φ) e = 1 ∧ ∀ t, tensorAction P.actT e t = ∑ j, tensorAction P.actT (ℓ j t) (u j) := by
  first | exact @GlobalTheory.TateLocFree.exists_place_decomp | exact GlobalTheory.TateLocFree.exists_place_decomp | (intros; apply GlobalTheory.TateLocFree.exists_place_decomp <;> assumption)
