import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermStronglyMeasurable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CountableDoubledHermitianLagrangians
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActEquivSymmApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumSetIntegralEqZeroOfStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumSetIntegralProdEqZeroOfInnerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsotropicFrameLagrangianFirstSummandStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalUnitaryLagrangianActionEqOfMemFrameUnipoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagrangianStabilizerNormalizesFrameUnipotentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open scoped GlobalTheory.GaugeEx

noncomputable section
namespace GlobalTheory.RallisCusp

theorem nonGraph_sum_eq_zero : ∀ D : D7, EisAbs D → TermMove D → TermInv D → CuspKill D → (∀ ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr, SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ Y : Lag W, Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥ → Continuous fun g : GA D W => lagTerm μ 𝓕 (fr Y) (om (1, g) f₁) f₂) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → ∑' Y : {Y : Lag W // Y.1.comap (LinearMap.inl D.host.E _ _) ≠ ⊥}, ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) = 0 := by
  intro D hEis hMove hInv hKill hcont ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ ha₁ hc₁ ha₂ hc₂
  haveI : Countable (Lag W) := lag_countable D W
  haveI : Countable D.host.E := countable_numberField_type D.host.E
  haveI := hS.haarW
  have hw := hS.weil
  have hpres : ∀ p f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (om p f) := hw.om_pres
  have hom : ∀ (g h : GA D W) f, om (1, g) (om (1, h) f) = om (1, g * h) f := by
    intro g h f
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]

  have hmove : ∀ (γ : GQ W) (Y : Lag W) (g : GA D W) (F₂ : WO V W → ℂ), IsThetaFunO ψ V W F₂ →
      lagTerm μ 𝓕 (fr (lagAct W γ Y)) (om (1, g) f₁) F₂ = lagTerm μ 𝓕 (fr Y) (om (1, (γ : GA D W)⁻¹ * g) f₁) F₂ := by
    intro γ Y g F₂ hF₂
    have h1 := (hMove ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS (om (1, g) f₁) F₂ (hpres _ _ hf₁) hF₂).1
      (lagAct W γ Y) _ (isLagFrame_lagAct W γ Y (fr Y) (hS.frame Y))
    have h2 := ((hMove ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS (om (1, (γ : GA D W)⁻¹ * g) f₁) F₂ (hpres _ _ hf₁) hF₂).2
      γ γ.2 (gqMat W γ) (gqMat_map W γ).symm).1 (fr Y)
    rw [← h1, ← h2, hom, mul_inv_cancel_left]

  have hslice : ∀ g₂ : GA D W, ∑' Y : NGLag W, ∫⁻ g in 𝓖, ‖star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)‖ₑ ∂νW ≠ ⊤ →
      ∑' Y : NGLag W, ∫ g in 𝓖, star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) ∂νW = 0 := by
    intro g₂ hfin
    have hF₂ := hpres (1, g₂) f₂ hf₂
    have hGQ : Countable (GQ W) := by
      haveI : Countable (Matrix (Fin W.rank) (Fin W.rank) D.host.E) :=
        inferInstanceAs (Countable (Fin W.rank → Fin W.rank → D.host.E))
      refine Function.Injective.countable (f := fun γ : GQ W => gqMat W γ) ?_
      intro γ δ h
      apply Subtype.ext
      apply GlobalTheory.MixModel.mt_injective W
      have := congrArg (fun c => c.map (incA D)) h
      simpa only [gqMat_map] using this
    refine GlobalTheory.T.tsum_setIntegral_eq_zero_of_stabilizer_integrals νW inferInstance (GQ W) hGQ 𝓖 hS.fdW (ngAct W) (ngAct_one W) (ngAct_mul W)
      (fun Y g => star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)) ?_ ?_ hfin ?_
    · intro γ Y g
      show star (φ₁ g) * lagTerm μ 𝓕 (fr (lagAct W γ Y.1)) _ _ = _
      rw [hmove γ Y.1 g _ hF₂, ha₁.left _ (inv_mem γ.2) g]
    · intro Y
      exact ((continuous_star.comp ha₁.cont).mul (hcont ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ _ hf₁ hF₂ Y.1 Y.2)).aestronglyMeasurable
    · intro Y Γ hΓ 𝓓 h𝓓 hint
      obtain ⟨s, I, hI, hspan⟩ := GlobalTheory.T.exists_isotropicFrame_lagrangian_first_summand D W Y.1 Y.2
      have hle : Γ ≤ GQ W := fun g hg => ((hΓ g).1 hg).1
      have hfix : ∀ g (hg : g ∈ Γ), lagAct W ⟨g, hle hg⟩ Y.1 = Y.1 := by
        intro g hg
        obtain ⟨h, e⟩ := (hΓ g).1 hg
        exact congrArg Subtype.val e
      have key := hKill W νW hS.haarW s I hI Γ hle
        (fun n hn => (hΓ n).2 ⟨hn.2, Subtype.ext (GlobalTheory.T.rationalUnitaryLagrangianAction_eq_of_mem_frameUnipotent D W Y.1 s I hI hspan ⟨n, hn.2⟩ hn.1)⟩)
        (fun γ hγ n hn => GlobalTheory.T.lagrangianStabilizer_normalizes_frameUnipotent D W Y.1 s I hI hspan ⟨γ, hle hγ⟩ (hfix γ hγ) n hn) 𝓓 h𝓓
        (fun g => lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)) (fun g => star (φ₁ g))
        (hcont ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS f₁ _ hf₁ hF₂ Y.1 Y.2) ?_ ?_ ?_ ?_ ?_
      · rw [← key]
        congr 1
        funext g
        ring
      · intro γ hγ g
        show lagTerm μ 𝓕 (fr Y.1) (om (1, γ * g) f₁) (om (1, g₂) f₂) = lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)
        have := hmove ⟨γ, hle hγ⟩ Y.1 (γ * g) _ hF₂
        rw [hfix γ hγ] at this
        rw [this]
        congr 3
        exact congrArg (Prod.mk 1) (inv_mul_cancel_left γ g)
      · intro n hn g
        show lagTerm μ 𝓕 (fr Y.1) (om (1, n * g) f₁) (om (1, g₂) f₂) = lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂)
        rw [← hom]
        exact hInv ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS Y.1 s I hI hspan n hn _ _ (hpres _ _ hf₁) hF₂
      · exact ⟨fun γ hγ g => by show star (φ₁ (γ * g)) = star (φ₁ g); rw [ha₁.left γ hγ g],
          by
            obtain ⟨U, hU, hk⟩ := ha₁.level
            exact ⟨U, hU, fun k hk1 hk2 g => by show star (φ₁ (g * k)) = star (φ₁ g); rw [hk k hk1 hk2 g]⟩,
          continuous_star.comp ha₁.cont⟩
      · intro r C hC μ' 𝓕' hμ' h𝓕' g
        have := hc₁ r C hC μ' 𝓕' hμ' h𝓕' g
        show ∫ n in 𝓕', (starRingEnd ℂ) (φ₁ ((n : GA D W) * g)) ∂μ' = 0
        rw [integral_conj, this, map_zero]
      · have e : (fun g => lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) * star (φ₁ g)) =
            fun g => star (φ₁ g) * lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) := funext fun g => mul_comm _ _
        show IntegrableOn (fun g => lagTerm μ 𝓕 (fr Y.1) (om (1, g) f₁) (om (1, g₂) f₂) * star (φ₁ g)) 𝓓 νW
        rw [e]
        exact hint
  have hφ₁c : Continuous φ₁ := ha₁.cont
  refine GlobalTheory.T.tsum_setIntegral_prod_eq_zero_of_inner' (X := NGLag W) inferInstance νW inferInstance 𝓖
    (fun Y p => star (φ₁ p.1) * φ₂ p.2 * lagTerm μ 𝓕 (fr Y.1) (om (1, p.1) f₁) (om (1, p.2) f₂)) ?_ ?_ ?_
  · intro Y
    have hm := GlobalTheory.RallisMeas.lagTerm_stronglyMeasurable D ψ V W χV χW om μ 𝓕 hw hS.covol f₁ f₂ hf₁ hf₂ (fr Y.1)
    exact (((continuous_star.comp hφ₁c).comp continuous_fst).mul (ha₂.cont.comp continuous_snd)).aestronglyMeasurable.mul
      hm.aestronglyMeasurable
  · have h0 := hEis ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ hf₁ hf₂ φ₁ φ₂ ha₁ hc₁ ha₂ hc₂
    refine ne_top_of_le_ne_top h0 (lintegral_mono fun g₁ => lintegral_mono fun g₂ => ?_)
    have e : ∀ Y : NGLag W, ‖star (φ₁ g₁) * φ₂ g₂ * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ =
        (fun Y : Lag W => ‖lagTerm μ 𝓕 (fr Y) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ * ‖φ₁ g₁‖ₑ * ‖φ₂ g₂‖ₑ) Y.1 := by
      intro Y
      have hs : ‖star (φ₁ g₁)‖ₑ = ‖φ₁ g₁‖ₑ := by simp [enorm_eq_nnnorm]
      simp only
      rw [enorm_mul, enorm_mul, hs]
      ring
    rw [tsum_congr e]
    exact ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
  · intro g₂ hfin
    by_cases h0 : φ₂ g₂ = 0
    · simp [h0]
    · have e1 : ∀ Y : NGLag W, ∫ g₁ in 𝓖, star (φ₁ g₁) * φ₂ g₂ * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂) ∂νW =
          φ₂ g₂ * ∫ g₁ in 𝓖, star (φ₁ g₁) * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂) ∂νW := by
        intro Y
        rw [← integral_const_mul]
        congr 1
        funext g₁
        ring
      have e2 : ∀ Y : NGLag W, ∫⁻ g₁ in 𝓖, ‖star (φ₁ g₁) * φ₂ g₂ * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ ∂νW =
          ‖φ₂ g₂‖ₑ * ∫⁻ g₁ in 𝓖, ‖star (φ₁ g₁) * lagTerm μ 𝓕 (fr Y.1) (om (1, g₁) f₁) (om (1, g₂) f₂)‖ₑ ∂νW := by
        intro Y
        rw [← lintegral_const_mul' _ _ enorm_ne_top]
        congr 1
        funext g₁
        rw [enorm_mul, enorm_mul, enorm_mul]
        ring
      simp only at hfin ⊢
      rw [tsum_congr e2, ENNReal.tsum_mul_left] at hfin
      rw [tsum_congr e1, tsum_mul_left, hslice g₂ ?_, mul_zero]
      intro htop
      rw [htop, ENNReal.mul_top (enorm_ne_zero.2 h0)] at hfin
      exact hfin rfl

end GlobalTheory.RallisCusp
end
