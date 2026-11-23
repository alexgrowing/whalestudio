import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSIpInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRadAdj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACHaarPos

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Fund

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]

theorem rds_zeta_compact (D : B.RealPlaceData k r Wp Wq) {Kz : Set ℂ} (hKz : IsCompact Kz)
    (hKzA : Kz ⊆ JCx2.rbO (Tz k r D.z) (Tz k r D.z')) :
    ∃ K' : Set (Mx k r), IsCompact K' ∧ K' ⊆ Qx5.Dp k r D.z D.z' ∧
      ∀ g ∈ Glev k r (Fin.last r), 0 < GGl k r D.z D.z' g → zetaL k r D.z D.z' (Fin.last r) g ∈ Kz → g ∈ K' := by
  have hmem := Formalism.FourierDecayAlt.P.b2_rank_one_mem k r D.z D.z' D.μsec D.z_mem D.z'_mem D.sec
  let SW : Set (Mt k r) := {x | (Matrix.of x : Mx k r) ∈ UWset k r D.z}
  let SW' : Set (Mt k r) := {x | (Matrix.of x : Mx k r) ∈ UWset k r D.z'}
  let F : ℂ × (Mt k r × Mt k r) → Mt k r := fun p =>
    JCx2.rbMul (JCx2.rbMul (p.2.1, JCx2.rbEf k r D.μsec p.1), p.2.2)
  have hF : ∀ p : ℂ × (Mt k r × Mt k r),
      (Matrix.of (F p) : Mx k r) = Matrix.of p.2.1 * NF.muZ k r D.μsec p.1 * Matrix.of p.2.2 := fun p => rfl
  have hSW : IsCompact SW := Formalism.FourierDecayAlt.P.B2x3.compactW k r D.z D.z_mem D.T_pos
  have hSW' : IsCompact SW' := Formalism.FourierDecayAlt.P.B2x3.compactW k r D.z' D.z'_mem D.T'_pos
  have hS : IsCompact (Kz ×ˢ (SW ×ˢ SW')) := hKz.prod (hSW.prod hSW')
  have hEc : ContinuousOn (JCx2.rbEf k r D.μsec) (JCx2.rbO (Tz k r D.z) (Tz k r D.z')) :=
    JCx2.rb_contOn_E fun i j => (D.sec.1 i j).continuousOn
  have hFc : ContinuousOn F (Kz ×ˢ (SW ×ˢ SW')) := by
    have hA : ContinuousOn (fun p : ℂ × (Mt k r × Mt k r) =>
        (p.2.1, JCx2.rbEf k r D.μsec p.1)) (Kz ×ˢ (SW ×ˢ SW')) :=
      (continuous_fst.comp continuous_snd).continuousOn.prodMk
        (hEc.comp continuousOn_fst fun p hp => hKzA hp.1)
    have hB : ContinuousOn (fun p : ℂ × (Mt k r × Mt k r) =>
        (JCx2.rbMul (p.2.1, JCx2.rbEf k r D.μsec p.1), p.2.2)) (Kz ×ˢ (SW ×ˢ SW')) :=
      (Formalism.FourierDecayAlt.P.B7.continuous_mulM.comp_continuousOn hA).prodMk
        (continuous_snd.comp continuous_snd).continuousOn
    exact Formalism.FourierDecayAlt.P.B7.continuous_mulM.comp_continuousOn hB
  refine ⟨F '' (Kz ×ˢ (SW ×ˢ SW')), hS.image_of_continuousOn hFc, ?_, ?_⟩
  · rintro g ⟨p, ⟨hp1, hp2, hp3⟩, rfl⟩
    have hζ : Tz k r D.z * Tz k r D.z' < Complex.normSq p.1 := hKzA hp1
    obtain ⟨-, hherm⟩ := hmem p.1 hζ ((Matrix.of p.2.1 : Mx k r)⁻¹) (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp2)
      (Matrix.of p.2.2) hp3
    have hinvinv : ((Matrix.of p.2.1 : Mx k r)⁻¹)⁻¹ = Matrix.of p.2.1 :=
      Matrix.inv_eq_right_inv (Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul hp2)
    rw [hinvinv] at hherm
    show 0 < GGl k r D.z D.z' (Matrix.of (F p))
    rw [hF]
    unfold GGl
    rw [P5.Rad.zetaL_last]
    erw [hherm]
    exact sub_pos.2 hζ
  · intro g hg hG hζK
    have hu := P5.Rad.glev_last_uwb hg
    have hζA : Tz k r D.z * Tz k r D.z' < Complex.normSq (herm (Hpk k r) (g.mulVec D.z') D.z) := by
      unfold GGl at hG
      rw [P5.Rad.zetaL_last] at hG
      linarith
    obtain ⟨h, hh, h', hh', hgeq⟩ := Formalism.FourierDecayAlt.P.b2_rank_one_coord k r D.z D.z' D.μsec D.k_pos D.z_mem
      D.z'_mem D.T_pos D.T'_pos D.sec g hu hζA
    rw [P5.Rad.zetaL_last] at hζK
    refine ⟨(herm (Hpk k r) (g.mulVec D.z') D.z, ((h⁻¹ : Mx k r), (h' : Mx k r))),
      ⟨hζK, Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh, hh'⟩, ?_⟩
    show (Matrix.of (F _) : Mx k r) = g
    rw [hF]
    exact hgeq.symm

theorem rds_haar_pos {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {g₀ : Mx k r}
    (hg₀ : g₀ ∈ Glev k r (Fin.last r)) {V : Set (Mt k r)} (hV : IsOpen V) (hgV : (g₀ : Mt k r) ∈ V) : 0 < μ V := by
  have hinv : ∀ u ∈ Glev k r (Fin.last r), u⁻¹ ∈ Glev k r (Fin.last r) := fun u hu => Formalism.FourierDecayAlt.P.Qx8.glev_inv hu
  have hunit : ∀ u ∈ Glev k r (Fin.last r), IsUnit (u : B.Mat k r).det := fun u hu =>
    Matrix.isUnit_det_of_left_inverse (Formalism.FourierDecayAlt.P.Qx8.inv_mul_uh hu.1)
  have hV1 : IsOpen (lmulM g₀ ⁻¹' V) := hV.preimage (Formalism.FourierDecayAlt.P.B2x1.lmulM_cont _)
  have h1 : ((1 : B.Mat k r) : Mt k r) ∈ lmulM g₀ ⁻¹' V := by
    show g₀ * 1 ∈ V
    rw [mul_one]; exact hgV
  have hpos := Formalism.FourierDecayAlt.P.CutMP.JA.SA.haar_pos_nhds_one hμ hinv hunit hV1 h1
  have e := hμ.left g₀ hg₀
  have hm := Measure.map_apply (μ := μ) (Formalism.FourierDecayAlt.P.B2x1.lmulM_cont (k := k) (r := r) g₀).measurable hV.measurableSet
  rw [e] at hm
  rw [hm]; exact hpos

theorem rds_dxc_pos {A : Set (Fin r → ℂ)} (hA : IsOpen A) (hAne : A.Nonempty) (hAO : A ⊆ OmX r) : 0 < dxc r A := by
  have hmeas : Measurable fun c : Fin r → ℂ => ENNReal.ofReal (∏ l, (‖c l‖ ^ 2)⁻¹) := by
    refine ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun l _ => ?_)
    exact ((measurable_pi_apply l).norm.pow_const 2).inv
  rw [pos_iff_ne_zero]
  intro h0
  unfold dxc at h0
  rw [withDensity_apply_eq_zero' hmeas.aemeasurable] at h0
  have hsub : A ⊆ {c | ENNReal.ofReal (∏ l, (‖c l‖ ^ 2)⁻¹) ≠ 0} ∩ A := by
    intro c hc
    refine ⟨?_, hc⟩
    simp only [Set.mem_ofPred_eq, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Finset.prod_pos fun l _ => inv_pos.2 (pow_pos (norm_pos_iff.2 (hAO hc l)) 2)
  exact (hA.measure_ne_zero volume hAne) (measure_mono_null hsub h0)

end Fund

section Fund2

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem rds_hsVec_ne_zero {A : Wq →L[ℂ] Wp} (hA : A ≠ 0) : B.hsVec A ≠ 0 := by
  intro h
  apply hA
  have hb : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0 := fun i => by
    have := congrArg (fun v => (WithLp.ofLp v) i) h
    simpa [B.hsVec] using this
  ext v
  rw [← (stdOrthonormalBasis ℂ Wq).sum_repr v, map_sum]
  simp [hb]

theorem rdsMul_mem (a : (Fin r → ℂ) → ℝ) (b : ℂ → ℝ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (Δ : RadSp k r z z' π π') :
    (fun c g => ((a c * b (zetaL k r z z' (Fin.last r) g) : ℝ) : ℂ) • (Δ : Fn k r (Wq →L[ℂ] Wp)) c g) ∈
      RadSp k r z z' π π' := by
  refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
  · simp [Δ.2.1 x hx]
  · obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := Δ.2.2.1 x₀ hx₀
    refine ⟨U, fun x => ((a x.1 * b (zetaL k r z z' (Fin.last r) x.2) : ℝ) : ℂ) • F x, hU, hxU, ?_,
      fun x hx hg => by simp only [hΦF x hx hg]⟩
    have hs : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r =>
        ((a x.1 * b (zetaL k r z z' (Fin.last r) x.2) : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((ha.comp contDiff_fst).mul
        (hb.comp ((Qx5.zetaL_contDiff k r z z' _).comp contDiff_snd)))
    exact hs.contDiffOn.smul hF
  · show ((a x.1 * b (zetaL k r z z' (Fin.last r) (h * x.2 * h')) : ℝ) : ℂ) •
        (Δ : Fn k r (Wq →L[ℂ] Wp)) x.1 (h * x.2 * h') =
      (π h).comp ((((a x.1 * b (zetaL k r z z' (Fin.last r) x.2) : ℝ) : ℂ) •
        (Δ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2).comp (π' h'))
    rw [Formalism.FourierDecayAlt.P.Qx8.zetaL_equiv hh hh', Δ.2.2.2 x hx h hh h' hh', ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul]

end Fund2

theorem spectral_fundamental_identity : RDSFund := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Φ₁ Φ₂ hEq x₀ hx₀
  subst hz hz' hπ hπ'
  have hμ := hD.2.1
  have hσ := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hμ
  by_contra hne
  let Δ : RadSp P.k P.r D.z D.z' D.π D.π' := Φ₁ - Φ₂
  have hΔ0 : (Δ : Fn P.k P.r (Wq →L[ℂ] Wp)) x₀.1 x₀.2 ≠ 0 := by
    simp only [Δ, Submodule.coe_sub, Pi.sub_apply]
    exact sub_ne_zero.2 hne

  have hOm : IsOpen (OmX P.r) := by
    have : OmX P.r = ⋂ l, {c : Fin P.r → ℂ | c l ≠ 0} := by ext c; simp [OmX]
    rw [this]; exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const

  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hOm x₀.1 hx₀.1
  let χb : ContDiffBump x₀.1 := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hχO : Metric.closedBall x₀.1 (ε / 2) ⊆ OmX P.r :=
    (Metric.closedBall_subset_ball (by linarith)).trans hεO

  let ζ₀ := zetaL P.k P.r D.z D.z' (Fin.last P.r) x₀.2
  have hζ₀ : ζ₀ ∈ JCx2.rbO (Tz P.k P.r D.z) (Tz P.k P.r D.z') := by
    have := hx₀.2.2
    unfold GGl at this
    show Tz P.k P.r D.z * Tz P.k P.r D.z' < Complex.normSq ζ₀
    linarith
  obtain ⟨δ, hδ, hδO⟩ := Metric.isOpen_iff.1 (JCx2.rb_isOpen_O _ _) ζ₀ hζ₀
  let ηb : ContDiffBump ζ₀ := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  have hKz : IsCompact (Metric.closedBall ζ₀ (δ / 2)) := isCompact_closedBall _ _
  have hKzA : Metric.closedBall ζ₀ (δ / 2) ⊆ JCx2.rbO (Tz P.k P.r D.z) (Tz P.k P.r D.z') :=
    (Metric.closedBall_subset_ball (by linarith)).trans hδO
  obtain ⟨K', hK'c, hK'D, hK'⟩ := rds_zeta_compact D hKz hKzA

  let Ψ : RadSp P.k P.r D.z D.z' D.π D.π' := ⟨_, rdsMul_mem χb ηb χb.contDiff ηb.contDiff Δ⟩
  have hΨv : ∀ c g, (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      ((χb c * ηb (zetaL P.k P.r D.z D.z' (Fin.last P.r) g) : ℝ) : ℂ) • (Δ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g :=
    fun _ _ => rfl
  have hΨ : RTest Ψ := by
    refine ⟨Metric.closedBall x₀.1 (ε / 2) ×ˢ (K' ∩ Glev P.k P.r (Fin.last P.r)),
      (isCompact_closedBall _ _).prod (hK'c.inter_right (Qx5.Glev_closed _)), ?_, ?_⟩
    · rintro x ⟨hx1, hx2, hx3⟩
      exact ⟨hχO hx1, hx3, hK'D hx2⟩
    · intro x hx
      rw [hΨv]
      by_cases hxD : x ∈ DomR P.k P.r D.z D.z'
      · have hcoef : χb x.1 * ηb (zetaL P.k P.r D.z D.z' (Fin.last P.r) x.2) = 0 := by
          by_cases h1 : x.1 ∈ Metric.closedBall x₀.1 (ε / 2)
          · have h2 : x.2 ∉ K' := fun h2 => hx ⟨h1, h2, hxD.2.1⟩
            have h3 : zetaL P.k P.r D.z D.z' (Fin.last P.r) x.2 ∉ Metric.closedBall ζ₀ (δ / 2) :=
              fun h3 => h2 (hK' x.2 hxD.2.1 hxD.2.2 h3)
            have h4 : ηb (zetaL P.k P.r D.z D.z' (Fin.last P.r) x.2) = 0 := by
              rw [← Function.notMem_support, ηb.support_eq]
              exact fun h5 => h3 (Metric.ball_subset_closedBall h5)
            rw [h4, mul_zero]
          · have h4 : χb x.1 = 0 := by
              rw [← Function.notMem_support, χb.support_eq]
              exact fun h5 => h1 (Metric.ball_subset_closedBall h5)
            rw [h4, zero_mul]
        rw [hcoef]; simp
      · rw [Δ.2.1 x hxD, smul_zero]

  have h1 := hEq Ψ hΨ
  rw [radIp_eq_prod hμ Φ₁ Ψ hΨ, radIp_eq_prod hμ Φ₂ Ψ hΨ] at h1
  have hsub : ∫ p, ipF Δ Ψ p ∂((dxc P.r).prod μ) = 0 := by
    have e : ipF Δ Ψ = fun p => ipF Φ₁ Ψ p - ipF Φ₂ Ψ p := by
      funext p
      simp only [ipF, Δ, Submodule.coe_sub, Pi.sub_apply, hsVec_sub_rd, inner_sub_left]
    rw [e, integral_sub (ipF_integrable hμ Φ₁ Ψ hΨ) (ipF_integrable hμ Φ₂ Ψ hΨ), h1, sub_self]

  let f : (Fin P.r → ℂ) × Mt P.k P.r → ℝ := fun p =>
    (χb p.1 * ηb (zetaL P.k P.r D.z D.z' (Fin.last P.r) (Matrix.of p.2))) *
      ‖B.hsVec ((Δ : Fn P.k P.r (Wq →L[ℂ] Wp)) p.1 (Matrix.of p.2))‖ ^ 2
  have hf : ∀ p, ipF Δ Ψ p = (f p : ℂ) := by
    intro p
    simp only [ipF, hΨv, rds_hsVec_smul, inner_smul_right, inner_self_eq_norm_sq_to_K, f]
    push_cast
    rfl
  have hfi : Integrable f ((dxc P.r).prod μ) := by
    have := (ipF_integrable hμ Δ Ψ hΨ).re
    simpa [hf] using this
  have hf0 : ∫ p, f p ∂((dxc P.r).prod μ) = 0 := by
    have e : (fun p => ipF Δ Ψ p) = fun p => ((f p : ℝ) : ℂ) := funext hf
    rw [e, integral_complex_ofReal] at hsub
    exact_mod_cast hsub
  have hfnn : 0 ≤ f := fun p =>
    mul_nonneg (mul_nonneg (χb.nonneg) (ηb.nonneg)) (sq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg hfnn hfi).1 hf0

  let p₀ : (Fin P.r → ℂ) × Mt P.k P.r := (x₀.1, x₀.2)
  have hp₀D : p₀ ∈ DomRt P.k P.r D.z D.z' := hx₀
  have hfp₀ : 0 < f p₀ := by
    refine mul_pos (mul_pos (χb.pos_of_mem_ball (Metric.mem_ball_self χb.rOut_pos))
      (ηb.pos_of_mem_ball (Metric.mem_ball_self ηb.rOut_pos))) ?_
    exact pow_pos (norm_pos_iff.2 (rds_hsVec_ne_zero hΔ0)) 2
  have hfc : ContinuousOn f (DomRt P.k P.r D.z D.z') := by
    have e : f = fun p => Complex.re (ipF Δ Ψ p) := by funext p; rw [hf]; simp
    rw [e]
    exact Complex.continuous_re.comp_continuousOn (ipF_contOn Δ Ψ)
  have hev : ∀ᶠ p in 𝓝[DomRt P.k P.r D.z D.z'] p₀, 0 < f p := (hfc p₀ hp₀D).eventually (lt_mem_nhds hfp₀)
  obtain ⟨O, hOo, hp₀O, hOsub⟩ := mem_nhdsWithin.1 hev
  obtain ⟨A, Bo, hA, hB, hA0, hB0, hAB⟩ := isOpen_prod_iff.1 hOo p₀.1 p₀.2 hp₀O
  let A' := A ∩ OmX P.r
  let B' := Bo ∩ {x : Mt P.k P.r | 0 < GGl P.k P.r D.z D.z' (Matrix.of x)}
  have hA' : IsOpen A' := hA.inter hOm
  have hB' : IsOpen B' := hB.inter (isOpen_lt continuous_const (Qx5.GGl_continuous P.k P.r D.z D.z'))
  have hGl : IsClosed {x : Mt P.k P.r | (Matrix.of x : Mx P.k P.r) ∈ Glev P.k P.r (Fin.last P.r)} :=
    Qx5.Glev_closed _
  have hbox : A' ×ˢ (B' ∩ {x : Mt P.k P.r | (Matrix.of x : Mx P.k P.r) ∈ Glev P.k P.r (Fin.last P.r)}) ⊆
      {p | ¬ f p = (0 : (Fin P.r → ℂ) × Mt P.k P.r → ℝ) p} := by
    rintro p ⟨⟨hpA, hpO⟩, ⟨hpB, hpG⟩, hpL⟩
    have hpD : p ∈ DomRt P.k P.r D.z D.z' := ⟨hpO, hpL, hpG⟩
    exact (hOsub ⟨hAB ⟨hpA, hpB⟩, hpD⟩).ne'
  have hnull := measure_mono_null hbox (ae_iff.1 hae)
  rw [Measure.prod_prod, measure_inter_conull (show μ {x : Mt P.k P.r |
      (Matrix.of x : Mx P.k P.r) ∈ Glev P.k P.r (Fin.last P.r)}ᶜ = 0 from hμ.conc)] at hnull
  have hApos : 0 < dxc P.r A' := rds_dxc_pos hA' ⟨x₀.1, hA0, hx₀.1⟩ Set.inter_subset_right
  have hBpos : 0 < μ B' := rds_haar_pos hμ hx₀.2.1 hB' ⟨hB0, hx₀.2.2⟩
  exact (ENNReal.mul_pos hApos.ne' hBpos.ne').ne' hnull

end Formalism.FourierDecayAlt.P.CutSE
