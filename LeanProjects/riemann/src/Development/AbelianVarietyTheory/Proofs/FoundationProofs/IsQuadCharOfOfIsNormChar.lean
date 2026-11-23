import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import CompanionTheory.EightfoldTheory.VariationTheory.TwistedTheory.FrobeniusPowerCompatibility
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.AdTransfer

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal UpperTheory.V.Published UpperTheory.V.Af.Bc

namespace GlobalTheory.QuadNormChar

theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem tendsto_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K'] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 K') => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 K')) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl

theorem fixes_or {F E Ω : Type} [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosed Ω] [CharZero F] (h2 : Module.finrank F E = 2) (σ : G F Ω)
    (hσ : ∃ e : E, σ (algebraMap E Ω e) ≠ algebraMap E Ω e) (τ : G F Ω) :
    τ ∈ (res F Ω E).range ∨ σ⁻¹ * τ ∈ (res F Ω E).range := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hfix : ∀ ρ : G F Ω, (∀ e : E, ρ (algebraMap E Ω e) = algebraMap E Ω e) → ρ ∈ (res F Ω E).range :=
    fun ρ hρ => ⟨AlgEquiv.ofRingEquiv (f := ρ.toRingEquiv) hρ, AlgEquiv.ext fun _ => rfl⟩
  let f : G F Ω → (E →ₐ[F] Ω) := fun ρ => (ρ : Ω →ₐ[F] Ω).comp (IsScalarTower.toAlgHom F E Ω)
  have hf : ∀ ρ e, f ρ e = ρ (algebraMap E Ω e) := fun _ _ => rfl
  have hcard : Fintype.card (E →ₐ[F] Ω) = 2 := by rw [AlgHom.card, h2]
  obtain ⟨e₀, he₀⟩ := hσ
  have h01 : f 1 ≠ f σ := fun h => he₀ (by have := DFunLike.congr_fun h e₀; rw [hf, hf] at this; exact this.symm)
  by_cases h1 : f τ = f 1
  · left
    exact hfix τ fun e => by have := DFunLike.congr_fun h1 e; rw [hf, hf] at this; exact this
  · by_cases h2' : f τ = f σ
    · right
      refine hfix _ fun e => ?_
      have := DFunLike.congr_fun h2' e
      rw [hf, hf] at this
      rw [AlgEquiv.mul_apply, this]
      exact σ.symm_apply_apply _
    · exfalso
      have : 2 < Fintype.card (E →ₐ[F] Ω) :=
        Fintype.two_lt_card_iff.2 ⟨f 1, f σ, f τ, h01, Ne.symm h1, Ne.symm h2'⟩
      omega

end GlobalTheory.QuadNormChar
