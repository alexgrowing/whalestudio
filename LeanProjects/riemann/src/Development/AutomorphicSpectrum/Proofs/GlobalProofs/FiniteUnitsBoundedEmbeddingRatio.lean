import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialZetaTwistedEntireDifference

set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem embedding_unit_le_abs {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {R : ℝ} {u : (𝓞 F)ˣ}
    (hu : TotPos F ((u : 𝓞 F) : F)) (hR : ∀ σ τ : F →+* ℝ, σ ((u : 𝓞 F) : F) ≤ R * τ ((u : 𝓞 F) : F))
    (σ : F →+* ℝ) : σ ((u : 𝓞 F) : F) ≤ |R| := by
  classical
  haveI : Finite (F →+* ℝ) := Finite.of_equiv _ (realEmbeddingsEquiv F).symm
  haveI : Fintype (F →+* ℝ) := Fintype.ofFinite _
  have hprod : ∏ τ : F →+* ℝ, τ ((u : 𝓞 F) : F) = 1 := by
    rw [prod_real_embeddings_eq_absNorm (u : 𝓞 F) hu, Ideal.span_singleton_eq_top.2 u.isUnit, Ideal.absNorm_top]
    simp
  obtain ⟨τ, hτ⟩ : ∃ τ : F →+* ℝ, τ ((u : 𝓞 F) : F) ≤ 1 := by
    by_contra hne
    push_neg at hne
    have hlt : ∏ _τ : F →+* ℝ, (1 : ℝ) < ∏ τ : F →+* ℝ, τ ((u : 𝓞 F) : F) :=
      Finset.prod_lt_prod_of_nonempty (fun _ _ => one_pos) (fun τ _ => hne τ) ⟨σ, Finset.mem_univ σ⟩
    rw [hprod] at hlt
    simp at hlt
  calc σ ((u : 𝓞 F) : F) ≤ R * τ ((u : 𝓞 F) : F) := hR σ τ
    _ ≤ |R| * τ ((u : 𝓞 F) : F) := mul_le_mul_of_nonneg_right (le_abs_self R) (hu τ).le
    _ ≤ |R| * 1 := mul_le_mul_of_nonneg_left hτ (abs_nonneg R)
    _ = |R| := mul_one _

theorem finite_totPos_units_bounded_ratio : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (R : ℝ),
    {u : (𝓞 F)ˣ | TotPos F ((u : 𝓞 F) : F) ∧ ∀ σ τ : F →+* ℝ, σ ((u : 𝓞 F) : F) ≤ R * τ ((u : 𝓞 F) : F)}.Finite := by
  intro F _ _ _ R
  have hinj : Function.Injective (fun u : (𝓞 F)ˣ => ((u : 𝓞 F) : F)) := fun a b h =>
    Units.ext (RingOfIntegers.ext h)
  refine ((Embeddings.finite_of_norm_le F ℂ |R|).preimage hinj.injOn).subset ?_
  rintro u ⟨hu, hR⟩
  refine ⟨(u : 𝓞 F).isIntegral_coe, fun φ => ?_⟩
  obtain ⟨σ, rfl⟩ := (realEmbeddingsEquiv F).surjective φ
  have h := embedding_unit_le_abs hu hR σ
  change ‖((σ ((u : 𝓞 F) : F) : ℝ) : ℂ)‖ ≤ |R|
  rw [Complex.norm_real, Real.norm_of_nonneg (hu σ).le]
  exact h

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
