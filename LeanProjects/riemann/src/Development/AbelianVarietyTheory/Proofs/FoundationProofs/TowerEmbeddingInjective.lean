import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOnZetaPowMulQPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

noncomputable section

namespace GlobalTheory.K5.EmbInj

theorem emb_injective : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : Tower p Ω) (n : ℕ), 1 ≤ n → ∀ ι : On p n →ₐ[O0 p] Ω, IsEmb T n ι →
      Function.Injective ι := by
  intro p _ Ω _ _ hc T n hn ι _
  obtain ⟨hdom, -, -⟩ := GlobalTheory.K5.OnDVR.isDVR_On p n hn
  obtain ⟨b, -⟩ := GlobalTheory.K5.OnFree.on_free p n
  haveI : Module.Finite (O0 p) (On p n) := Module.Finite.of_basis b
  haveI : Algebra.IsIntegral (O0 p) (On p n) := Algebra.IsIntegral.of_finite _ _
  rw [injective_iff_map_eq_zero]
  have hker : RingHom.ker (ι : On p n →+* Ω) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := O0 p)
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    have : algebraMap (O0 p) Ω a = 0 := by
      rw [← ι.commutes a]; exact ha
    rw [Ideal.mem_bot]
    exact hc.inj (this.trans (map_zero _).symm)
  intro x hx
  have : x ∈ RingHom.ker (ι : On p n →+* Ω) := hx
  rwa [hker, Ideal.mem_bot] at this

end GlobalTheory.K5.EmbInj
