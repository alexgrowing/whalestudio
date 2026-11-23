import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointTraceDual
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
open NumberField GlobalTheory.HTLat GlobalTheory.EigenSplit Classical
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.p_adic_point_trace_dual : ∀ {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (φ : E →+* C) (d : C), d ≠ 0 → (∀ (n : ℕ) (r : Fin n → O) (a : Fin n → 𝓞 E) (s : C), (∀ σ : E →+* C, ∑ k, algebraMap O C (r k) * σ (a k) = if σ = φ then s else 0) → v s ≤ v d) → ∀ (m : ℕ) (u : Fin m → P.T) (ℓ : Fin m → (P.T →ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] 𝓞 E)) (e : ℤ_[p] ⊗[ℤ] 𝓞 E), (∀ j a t, ℓ j (P.actT a t) = (1 ⊗ₜ a) * ℓ j t) → ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs.tauExt (embO P.integers φ) e = 1 → (∀ t, tensorAction P.actT e t = ∑ j, tensorAction P.actT (ℓ j t) (u j)) → ∀ w : P.V, w ∈ P.eigV (embO P.integers φ) → d • w ∈ P.latT → w ∈ P.latTQuot (σ := fun ψ : E →+* C => embO P.integers ψ) (isSplitting_embO P.integers) φ := by
  first | exact @GlobalTheory.EigGlue.mem_latTQuot_of_smul_mem_latT | exact GlobalTheory.EigGlue.mem_latTQuot_of_smul_mem_latT | (intros; apply GlobalTheory.EigGlue.mem_latTQuot_of_smul_mem_latT <;> assumption)
