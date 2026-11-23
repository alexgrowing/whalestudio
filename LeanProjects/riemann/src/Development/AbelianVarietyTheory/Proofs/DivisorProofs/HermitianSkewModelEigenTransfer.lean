import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalMapExistsScalarFactorAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.XiTermDecayUnif

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∀ g ∈ SB (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F), ∀ N K : ℕ, 1 ≤ N → ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : SInf F (Fin n × Fin d)) (ξ : Fin n → E), (∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o) →
      ‖thetaSum F (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F ξ) (incV F H'.y)) (pureA F f g)))‖ * (1 + ∑ i, ∑ w : InfinitePlace E, w (ξ i)) ^ K ≤
        C * (s.sup (schwartzSeminormFamily ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)) f := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ hev hB hM hXW g hg N K hN
  have hψ : IsStd B.ψ := hB.std
  let u : (Fin n → E) → Matrix (Fin n) (Fin d) (AE F E) := fun ξ => Matrix.vecMulVec (incV F ξ) (incV F H'.y)
  let wt : (Fin n → E) → ℝ := fun ξ => (1 + ∑ i, ∑ w : InfinitePlace E, w (ξ i)) ^ K
  obtain ⟨l₀, hl₀, hl₀eq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d₁)
  have hl₁ := GlobalTheory.ConeMeasV.comp_ev_mem_adm hM hM₁ hev hl₀
  have hterm : ∀ ξ : Fin n → E, ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d),
      thetaSum F (e₀ (M.co.rho B.ψ (u ξ) (pureA F f g))) = T f := by
    intro ξ
    obtain ⟨T, hT⟩ := GlobalTheory.ConeMeasV.comp_schr_mem_adm hψ (M.co.e (u ξ)) hl₁ g hg
    refine ⟨T, fun f => ?_⟩
    have hA : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) g ∈ schA F (Fin n × Fin d) :=
      Submodule.subset_span ⟨f, g, hg, rfl⟩
    have h1 := GlobalTheory.ConeMeasV.schr_mem_schA hψ (M.co.e (u ξ)) hA
    have h2 := hev.maps _ h1
    rw [← hT f]
    exact (hl₀eq _ h2).symm
  choose T hT using hterm
  let ι := {ξ : Fin n → E // ∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o}
  let L : ι → SInf F (Fin n × Fin d) →L[ℂ] ℂ := fun ξ => ((wt ξ.1 : ℝ) : ℂ) • T ξ.1
  have hwt : ∀ ξ, 0 ≤ wt ξ := fun ξ => by
    have : 0 ≤ ∑ i, ∑ w : InfinitePlace E, w (ξ i) := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun w _ => apply_nonneg w _
    positivity
  have hLn : ∀ ξ : ι, ∀ f, ‖L ξ f‖ = ‖thetaSum F (e₀ (M.co.rho B.ψ (u ξ.1) (pureA F f g)))‖ * wt ξ.1 := by
    intro ξ f
    simp only [L, ContinuousLinearMap.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hwt ξ.1), hT]
    ring
  have hbdd : ∀ f, BddAbove (Set.range fun ξ : ι => (normSeminorm ℂ ℂ).comp (L ξ).toLinearMap f) := by
    intro f
    have hA : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) g ∈ schA F (Fin n × Fin d) :=
      Submodule.subset_span ⟨f, g, hg, rfl⟩
    obtain ⟨C, hC⟩ := GlobalTheory.T.norm_thetaSum_rho_vecMulVec_mul_pow_bounded hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH hM₁ e₀ hev hB hM hXW _ hA N K hN
    refine ⟨C, ?_⟩
    rintro _ ⟨ξ, rfl⟩
    simp only [Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe]
    rw [hLn]
    exact hC ξ.1 ξ.2
  have hbdd' : BddAbove (Set.range fun ξ : ι => (normSeminorm ℂ ℂ).comp (L ξ).toLinearMap) :=
    (Seminorm.bddAbove_range_iff).2 hbdd
  haveI : BarrelledSpace ℂ (SInf F (Fin n × Fin d)) := GlobalTheory.schwartzMap_barrelledSpace _
  have hcont : Continuous (⨆ ξ : ι, (normSeminorm ℂ ℂ).comp (L ξ).toLinearMap) :=
    Seminorm.continuous_iSup _ (fun ξ => continuous_norm.comp (L ξ).continuous) hbdd'
  let S : Seminorm ℂ (SInf F (Fin n × Fin d)) := ⨆ ξ : ι, (normSeminorm ℂ ℂ).comp (L ξ).toLinearMap
  have hS : Continuous S := by
    change Continuous ⇑(⨆ ξ : ι, (normSeminorm ℂ ℂ).comp (L ξ).toLinearMap)
    rw [Seminorm.coe_iSup_eq hbdd']
    exact hcont
  obtain ⟨s, C, -, hle⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ) S hS
  refine ⟨s, C, C.2, fun f ξ hξ => ?_⟩
  have h1 : ‖L ⟨ξ, hξ⟩ f‖ ≤ S f := by
    change _ ≤ ⇑(⨆ ξ : ι, (normSeminorm ℂ ℂ).comp (L ξ).toLinearMap) f
    rw [Seminorm.coe_iSup_eq hbdd', iSup_apply]
    exact le_ciSup (f := fun ξ : ι => (normSeminorm ℂ ℂ).comp (L ξ).toLinearMap f) (hbdd f) ⟨ξ, hξ⟩
  have h2 := hle f
  rw [hLn] at h1
  exact h1.trans h2

end GlobalTheory.XiTermDecayUnif

end
