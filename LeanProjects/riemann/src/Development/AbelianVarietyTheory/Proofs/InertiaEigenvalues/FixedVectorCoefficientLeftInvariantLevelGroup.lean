import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LatIndexEqOneOfMem
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialLevelCosetRepresentativeMemLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.CoefLeft

theorem ip_eq_of_sq {X : Type} [MeasurableSpace X] (ν : Measure X) (a b c d : X → ℂ)
    (ha : MemLp a 2 ν) (hb : MemLp b 2 ν) (hc : MemLp c 2 ν) (hd : MemLp d 2 ν)
    (h : ∀ z : ℂ, ∫⁻ x, ‖c x + z * d x‖ₑ ^ 2 ∂ν = ∫⁻ x, ‖a x + z * b x‖ₑ ^ 2 ∂ν) :
    ∫ x, star (c x) * d x ∂ν = ∫ x, star (a x) * b x ∂ν := by
  have pt : ∀ p q : ℂ, star p * q = (1/4 : ℂ) * ((((‖p + 1 * q‖ ^ 2 : ℝ)) : ℂ) - ((‖p + (-1) * q‖ ^ 2 : ℝ) : ℂ)
      + Complex.I * ((‖p + (-Complex.I) * q‖ ^ 2 : ℝ) : ℂ) - Complex.I * ((‖p + Complex.I * q‖ ^ 2 : ℝ) : ℂ)) := by
    intro p q
    have e : ∀ w : ℂ, ((‖w‖ ^ 2 : ℝ) : ℂ) = w * (starRingEnd ℂ) w := by
      intro w; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [e, map_add, map_mul, map_neg, map_one, Complex.conj_I]
    show (starRingEnd ℂ) p * q = _
    ring_nf
    try (simp only [Complex.I_sq]; ring)
  have mem : ∀ (f g : X → ℂ), MemLp f 2 ν → MemLp g 2 ν → ∀ z : ℂ,
      Integrable (fun x => (((‖f x + z * g x‖ ^ 2 : ℝ)) : ℂ)) ν := by
    intro f g hf hg z
    have h2 : MemLp (fun x => f x + z * g x) 2 ν := hf.add (hg.const_mul z)
    have : Integrable (fun x => ‖f x + z * g x‖ ^ 2) ν := by
      have := h2.integrable_norm_pow (p := 2) (by norm_num)
      simpa using this
    exact this.ofReal
  have Q : ∀ (f g : X → ℂ), MemLp f 2 ν → MemLp g 2 ν → ∀ z : ℂ,
      ∫ x, (((‖f x + z * g x‖ ^ 2 : ℝ)) : ℂ) ∂ν = (((∫⁻ x, ‖f x + z * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ) := by
    intro f g hf hg z
    rw [integral_complex_ofReal]
    congr 1
    have hm : AEStronglyMeasurable (fun x => f x + z * g x) ν :=
      (hf.add (hg.const_mul z)).aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖f x + z * g x‖ ^ 2)
      (Filter.Eventually.of_forall fun x => by simp only [Pi.zero_apply]; positivity) (hm.norm.pow 2)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have expand : ∀ (f g : X → ℂ), MemLp f 2 ν → MemLp g 2 ν →
      ∫ x, star (f x) * g x ∂ν = (1/4 : ℂ) * ((((∫⁻ x, ‖f x + 1 * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ)
        - (((∫⁻ x, ‖f x + (-1) * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ)
        + Complex.I * (((∫⁻ x, ‖f x + (-Complex.I) * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ)
        - Complex.I * (((∫⁻ x, ‖f x + Complex.I * g x‖ₑ ^ 2 ∂ν).toReal : ℝ) : ℂ)) := by
    intro f g hf hg
    simp_rw [pt (f _) (g _)]
    rw [integral_const_mul, integral_sub, integral_add, integral_sub, integral_const_mul, integral_const_mul,
      Q f g hf hg, Q f g hf hg, Q f g hf hg, Q f g hf hg]
    · exact mem f g hf hg 1
    · exact mem f g hf hg (-1)
    · exact (mem f g hf hg 1).sub (mem f g hf hg (-1))
    · exact (mem f g hf hg (-Complex.I)).const_mul _
    · exact ((mem f g hf hg 1).sub (mem f g hf hg (-1))).add ((mem f g hf hg (-Complex.I)).const_mul _)
    · exact (mem f g hf hg Complex.I).const_mul _
  rw [expand c d hc hd, expand a b ha hb, h 1, h (-1), h (-Complex.I), h Complex.I]

end GlobalTheory.RawLift.CoefLeft

namespace GlobalTheory.RawLift.CoefLeft

variable {D : D7}

theorem isThetaFunO_add_smul {S T' : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {f g : WO S T' → ℂ}
    (hf : IsThetaFunO ψ S T' f) (hg : IsThetaFunO ψ S T' g) (z : ℂ) : IsThetaFunO ψ S T' (f + z • g) where
  quasi γ w := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hf.quasi, hg.quasi]; ring
  level := by
    obtain ⟨U₁, hU₁, h₁⟩ := hf.level
    obtain ⟨U₂, hU₂, h₂⟩ := hg.level
    refine ⟨U₁ ⊓ U₂, by rw [AddSubgroup.coe_inf]; exact hU₁.inter hU₂, fun u hu hu0 => ?_⟩
    have e1 := h₁ u hu.1 hu0
    have e2 := h₂ u hu.2 hu0
    funext w
    have e1' := congrFun e1 w
    have e2' := congrFun e2 w
    simp only [heisO, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at e1' e2' ⊢
    rw [← e1', ← e2']; ring_nf
  cont := hf.cont.add (hg.cont.const_smul z)
  smooth k L hL hL0 w := by
    have := (hf.smooth k L hL hL0 w).add ((hg.smooth k L hL hL0 w).const_smul z)
    simpa only [Pi.add_apply, Pi.smul_apply] using this

theorem memLp_two_of_lintegral {X : Type} [MeasurableSpace X] {ν : Measure X} {f : X → ℂ}
    (hm : AEStronglyMeasurable f ν) (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν < ⊤) : MemLp f 2 ν := by
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine ⟨hm.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simpa [enorm_pow] using h

end GlobalTheory.RawLift.CoefLeft

namespace GlobalTheory.RawLift.CoefLeft

theorem aesm_of_theta {D : D7} {S T' : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {f : WO S T' → ℂ} (ν : Measure (WO S T'))
    (hf : IsThetaFunO ψ S T' f) : AEStronglyMeasurable f ν := by
  haveI : OpensMeasurableSpace (WO S T') := ⟨le_rfl⟩
  exact hf.cont.aestronglyMeasurable

theorem thetaInner_weilRep {D : D7} {S T' : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T' →* Module.End ℂ (WO S T' → ℂ)} (hW : IsWeilDatumO ψ S T' χS χT om)
    {μ : Measure (WO S T')} {𝓕 : Set (WO S T')} (hμ : IsCovolOne (ratL T' S) μ 𝓕) (p : GA D S × GA D T')
    {u v : WO S T' → ℂ} (hu : IsThetaFunO ψ S T' u) (hv : IsThetaFunO ψ S T' v)
    (hu2 : ∫⁻ w in 𝓕, ‖u w‖ₑ ^ 2 ∂μ < ⊤) (hv2 : ∫⁻ w in 𝓕, ‖v w‖ₑ ^ 2 ∂μ < ⊤) :
    thetaIP μ 𝓕 (om p u) (om p v) = thetaIP μ 𝓕 u v := by
  have un := fun f (hf : IsThetaFunO ψ S T' f) => hW.om_unit μ 𝓕 hμ.1 hμ.2.1 p f hf
  unfold thetaIP
  refine ip_eq_of_sq (μ.restrict 𝓕) u v (om p u) (om p v)
    (memLp_two_of_lintegral (aesm_of_theta _ hu) hu2) (memLp_two_of_lintegral (aesm_of_theta _ hv) hv2)
    (memLp_two_of_lintegral (aesm_of_theta _ (hW.om_pres p u hu)) (by rw [un u hu]; exact hu2))
    (memLp_two_of_lintegral (aesm_of_theta _ (hW.om_pres p v hv)) (by rw [un v hv]; exact hv2)) (fun z => ?_)
  have := un (u + z • v) (isThetaFunO_add_smul hu hv z)
  simpa only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this

theorem thetaIP₂ {D : D7} {S T' : HSp D} {μ : Measure (WO S T')} {𝓕 : Set (WO S T')}
    {v : WO S T' → ℂ} (h : thetaIP μ 𝓕 v v ≠ 0) : ∫⁻ w in 𝓕, ‖v w‖ₑ ^ 2 ∂μ < ⊤ := by
  have hi : Integrable (fun w => star (v w) * v w) (μ.restrict 𝓕) := by
    by_contra hn
    exact h (integral_undef hn)
  have := hi.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at this
  simpa [enorm_mul, sq] using this

end GlobalTheory.RawLift.CoefLeft

namespace GlobalTheory.RawLift.CoefLeft

set_option maxHeartbeats 1000000 in

theorem coef_lev_mul : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i t, LevFix R i t → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL i t hfix μ 𝓕 hμ k hk g
  have hW := hL.thP.ωP i t
  have hv1 : R.ωP i t (1, k) (R.vP i t) = R.vP i t := by
    have := hfix k hk 1
    rwa [Model.pureTensor_one] at this
  have hvθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    rwa [Model.pureTensor_one] at this
  unfold coef
  by_cases h0 : thetaIP μ 𝓕 (R.vP i t) (R.vP i t) = 0
  · rw [h0, div_zero, div_zero]
  congr 1
  have e : R.ωP i t (1, k * g) = R.ωP i t (1, k) * R.ωP i t (1, g) := by rw [← map_mul]; simp
  rw [e, Module.End.mul_apply]
  have hv2 := thetaIP₂ h0
  have huθ := hW.om_pres (1, g) _ hvθ
  have hu2 : ∫⁻ w in 𝓕, ‖R.ωP i t (1, g) (R.vP i t) w‖ₑ ^ 2 ∂μ < ⊤ := by
    rw [hW.om_unit μ 𝓕 hμ.1 hμ.2.1 (1, g) _ hvθ]; exact hv2
  have key := thetaInner_weilRep hW hμ (1, k) huθ hvθ hu2 hv2
  rwa [hv1] at key

end GlobalTheory.RawLift.CoefLeft

end
