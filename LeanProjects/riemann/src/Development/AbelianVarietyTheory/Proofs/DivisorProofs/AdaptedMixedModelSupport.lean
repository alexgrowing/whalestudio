import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedMixedModelEvaluationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

open scoped Classical

namespace GlobalTheory.ThKExpandXAdm

theorem adm : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d₁ : ℕ) (X : Spc F E n) (W₁ : Spc F E d₁) (M₁ : Model σ X W₁), M₁.IsGood B.ψ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ →
    ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → B.IsGood σ →
    (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W₁.IsSkew σ B r' s') →
    ∀ g ∈ SB (Fin n × Fin d₁ → FiniteAdeleRing (𝓞 F) F), ∃ T : SInf F (Fin n × Fin d₁) →L[ℂ] ℂ,
      ∀ f : SInf F (Fin n × Fin d₁), (∑' w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (pureA F f g)))) = T f := by
  intro hKP F E _ _ _ _ _ σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' hev hB hXW g hg
  have hψ : IsStd B.ψ := hB.std
  have hSumm := GlobalTheory.T.adapted_mixed_model_evaluation hKP F E σ B n d₁ X W₁ M₁ hM₁ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' hev hB hXW
  obtain ⟨l₀, hl₀, hl₀eq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n₁ × Fin d₁)
  have hl₁ := GlobalTheory.ConeMeasV.comp_ev_mem_adm hM₁ hM₂ hev hl₀
  have hterm : ∀ w : Fin d₁ → E, ∃ T : SInf F (Fin n × Fin d₁) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d₁),
      thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (pureA F f g))) = T f := by
    intro w
    obtain ⟨T, hT⟩ := GlobalTheory.ConeMeasV.comp_schr_mem_adm hψ (M₁.co.e (Matrix.vecMulVec (incV F H.y) (incV F w))) hl₁ g hg
    refine ⟨T, fun f => ?_⟩
    have hA : pureA F (f : (Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) → ℂ) g ∈ schA F (Fin n × Fin d₁) :=
      Submodule.subset_span ⟨f, g, hg, rfl⟩
    have h1 := GlobalTheory.ConeMeasV.schr_mem_schA hψ (M₁.co.e (Matrix.vecMulVec (incV F H.y) (incV F w))) hA
    have h2 := hev.maps _ h1
    rw [← hT f]
    exact (hl₀eq _ h2).symm
  choose T hT using hterm
  have hsum : ∀ f : SInf F (Fin n × Fin d₁), Summable fun w : Fin d₁ → E => T w f := by
    intro f
    have hA : pureA F (f : (Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) → ℂ) g ∈ schA F (Fin n × Fin d₁) :=
      Submodule.subset_span ⟨f, g, hg, rfl⟩
    have := hSumm _ hA
    simpa only [hT] using this
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  obtain ⟨en, hen⟩ := exists_surjective_nat (Fin d₁ → E)
  let S : ℕ → Finset (Fin d₁ → E) := fun N => (Finset.range N).image en
  have hS : Tendsto S atTop atTop := by
    refine Filter.tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun w => ?_)
    · exact Finset.image_subset_image (Finset.range_subset_range.2 hab)
    · obtain ⟨k, rfl⟩ := hen w
      exact ⟨k + 1, Finset.mem_image_of_mem _ (Finset.mem_range.2 (Nat.lt_succ_self k))⟩
  haveI : BarrelledSpace ℂ (SInf F (Fin n × Fin d₁)) := GlobalTheory.schwartzMap_barrelledSpace _
  have hlim : Tendsto (fun N f => (∑ w ∈ S N, T w) f) atTop
      (𝓝 fun f : SInf F (Fin n × Fin d₁) => ∑' w, T w f) := by
    rw [tendsto_pi_nhds]
    intro f
    simp only [ContinuousLinearMap.sum_apply]
    exact (hsum f).hasSum.comp hS
  refine ⟨continuousLinearMapOfTendsto (fun N => ∑ w ∈ S N, T w) hlim, fun f => ?_⟩
  show _ = linearMapOfTendsto _ _ hlim f
  rw [linearMapOfTendsto_apply]
  simp only [hT]

end GlobalTheory.ThKExpandXAdm
