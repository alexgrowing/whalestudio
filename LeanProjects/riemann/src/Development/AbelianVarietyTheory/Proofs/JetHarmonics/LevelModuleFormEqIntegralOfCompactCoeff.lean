import Mathlib
import Formalism.HermitianCurvature.StatementTBB
import Formalism.HermitianCurvature.HerGenC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingOfHeads
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadGermSmoothExtension
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialExhaustion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeNeZeroComplex
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLevelZeroOfMemGroup

noncomputable section

namespace GlobalTheory.CptBesselPairing

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx2
open scoped ENNReal NNReal Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem integrable_zeta_of_integrable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}
    {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    {μb μW μW' : Measure (Mt k r)} {C : ℝ≥0} (hC : 0 < C) (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) (hW : B.IsHaarOn (UWset k r z) μW) (hW' : B.IsHaarOn (UWset k r z') μW')
    (hmap : μb = (C : ℝ≥0∞) • (rbP k r (Tz k r z) (Tz k r z') μW μW').map (rbPsi k r (Tz k r z) (Tz k r z') μsec))
    (φ : Mt k r → ℂ) (hφ : Integrable φ μb) (ψ : ℂ → ℂ)
    (hψ : ∀ ζ ∈ rbO (Tz k r z) (Tz k r z'), ∀ x y : Mt k r, Matrix.of x ∈ UWset k r z → Matrix.of y ∈ UWset k r z' →
      φ (rbPsi k r (Tz k r z) (Tz k r z') μsec (ζ, (x, y))) = ψ ζ) :
    Integrable fun ζ => (B2.zWeight k (Tz k r z) (Tz k r z') ζ : ℂ) * ψ ζ := by
  have := B7.sf hW
  have := B7.sf hW'
  have hcont : ∀ i j, ContinuousOn (fun ζ => μsec ζ i j) (rbO (Tz k r z) (Tz k r z')) :=
    fun i j => (hsec.1 i j).continuousOn
  subst hmap
  rw [integrable_smul_measure (by exact_mod_cast hC.ne') ENNReal.coe_ne_top] at hφ
  have hφ2 := hφ.comp_measurable (rb_measurable_Psi hcont)
  have h1 : ∀ᵐ ζ ∂((volume : Measure ℂ).withDensity (rbW k (Tz k r z) (Tz k r z'))),
      ζ ∈ rbO (Tz k r z) (Tz k r z') := by
    rw [ae_withDensity_iff (measurable_radial_weight k _ _)]
    filter_upwards [rb_ae_ne_circle (mul_pos hT hT')] with ζ hζ hw
    by_contra h
    exact hw (by simp [rbW, rb_zWeight_zero_of_not h hζ])
  have h2 : ∀ᵐ p ∂(μW.prod μW'), Matrix.of p.1 ∈ UWset k r z ∧ Matrix.of p.2 ∈ UWset k r z' := by
    have a1 := (Measure.quasiMeasurePreserving_fst (μ := μW) (ν := μW')).ae (B7.ae_mem hW)
    have a2 := (Measure.quasiMeasurePreserving_snd (μ := μW) (ν := μW')).ae (B7.ae_mem hW')
    filter_upwards [a1, a2] with p hp1 hp2 using ⟨hp1, hp2⟩
  have hne : μW.prod μW' ≠ 0 := by
    intro h0
    have h3 := congrArg (fun ν : Measure (Mt k r × Mt k r) => ν (Set.univ ×ˢ Set.univ)) h0
    simp only [Measure.prod_prod, Measure.coe_zero, Pi.zero_apply, mul_eq_zero, Measure.measure_univ_eq_zero] at h3
    exact h3.elim hW.ne_zero hW'.ne_zero
  unfold rbP at hφ2
  have : NeZero (μW.prod μW') := ⟨hne⟩
  obtain ⟨p, hp, hp2⟩ := (hφ2.prod_left_ae.and h2).exists
  have h4 : Integrable ψ ((volume : Measure ℂ).withDensity (rbW k (Tz k r z) (Tz k r z'))) := by
    refine hp.congr ?_
    filter_upwards [h1] with ζ hζ
    exact hψ ζ hζ p.1 p.2 hp2.1 hp2.2
  rw [integrable_withDensity_iff_integrable_smul' (measurable_radial_weight k _ _)
    (Filter.Eventually.of_forall fun ζ => ENNReal.ofReal_lt_top)] at h4
  refine h4.congr (Filter.Eventually.of_forall fun ζ => ?_)
  simp only [rbW]
  rw [ENNReal.toReal_ofReal (rb_zWeight_nonneg k _ _ ζ), Complex.real_smul]

section pairing

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

omit [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] in

theorem act_one {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S] (x : Ix S → RadSp k r z z' π π') :
    act (1 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) x = x := by
  funext a
  unfold act
  rw [Finset.sum_eq_single a]
  · rw [Matrix.one_apply_eq]; rfl
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb)]; rfl
  · simp

theorem integrable_pair_of_cor (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r)) [SFinite μ]
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (hC : CompositeFormulaLevelZero (S := Empty) P z z' π π' μ L st K l0) (Φ Φ' : RadSp P.k P.r z z' π π') (hΦ : Φ ∈ K 0)
    (hΦ' : Φ' ∈ K 0) :
    Integrable (fun q : (Fin P.r → ℂ) × Mt P.k P.r => ((∏ a : Fin P.r, ‖q.1 a‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      B.hsInner ((Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 (Matrix.of q.2))
        ((Φ' : Fn P.k P.r (Wq →L[ℂ] Wp)) q.1 (Matrix.of q.2))) (volume.prod μ) := by
  have h := (hC [] (by simp [WordOK, Fr.admitted]) (fun _ => Φ) (fun _ => Φ') (fun _ => hΦ) (fun _ => hΦ')
    (fun _ => 1) (fun _ => one_ne_zero)).1
  have hb : bTall (S := Empty) L [] = 1 := by
    unfold bTall
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
    rfl
  have ht : ∀ c g, topDens (S := Empty) L st [] (fun _ => Φ) (fun _ => Φ') c g =
      B.hsInner ((Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) ((Φ' : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) := by
    intro c g
    simp [topDens, Fr.ofWord, Fr.Start.frame, Fr.FrameData.d, act_one]
  simp only [hb, act_one, ht] at h
  let e : {l : Fin P.r // (0 : Fin (P.r + 1)).val ≤ l.val} ≃ Fin P.r := Equiv.subtypeUnivEquiv (fun l => Nat.zero_le _)
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin P.r => ℂ) e
  have hmp2 := hmp.prod (MeasurePreserving.id μ)
  have hemb : MeasurableEmbedding (Prod.map (MeasurableEquiv.piCongrLeft (fun _ : Fin P.r => ℂ) e)
      (id : Mt P.k P.r → Mt P.k P.r)) :=
    (MeasurableEquiv.piCongrLeft (fun _ : Fin P.r => ℂ) e).measurableEmbedding.prodMap MeasurableEmbedding.id
  rw [← hmp2.integrable_comp_emb hemb]
  refine h.congr (Filter.Eventually.of_forall fun q => ?_)
  have hv : ∀ l : {l : Fin P.r // (0 : Fin (P.r + 1)).val ≤ l.val},
      (MeasurableEquiv.piCongrLeft (fun _ : Fin P.r => ℂ) e q.1) (e l) = q.1 l := fun l =>
    Equiv.piCongrLeft_apply_apply _ _ _ _
  have hg : P5.glue 0 (fun _ => 1) q.1 = MeasurableEquiv.piCongrLeft (fun _ : Fin P.r => ℂ) e q.1 := by
    funext l
    have h := hv ⟨l, Nat.zero_le _⟩
    simp only [P5.glue]
    exact h.symm
  simp only [hg, Function.comp_apply, Prod.map_fst, Prod.map_snd, id]
  rw [Fintype.prod_equiv e (fun l => ‖q.1 l‖ ^ (-2 : ℤ))
    (fun a => ‖(MeasurableEquiv.piCongrLeft (fun _ : Fin P.r => ℂ) e q.1) a‖ ^ (-2 : ℤ)) (fun l => by rw [hv])]

theorem integrable_bigCell_of_radial {k r : ℕ} (D : B.RealPlaceData k r Wp Wq) (μ : Measure (Mt k r))
    (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (F F' : B.Mat k r → (Wq →L[ℂ] Wp))
    (hF : ∀ (A : ℝ) (m : ℕ), B.InCC A m F) (hF' : ∀ (A : ℝ) (m : ℕ), B.InCC A m F')
    (Φ Φ' : Q.RadSp k r D.z D.z' D.π D.π')
    (hΦ : ∀ y ∈ Q.DomR k r D.z D.z',
      (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D F) y.1 y.2)
    (hΦ' : ∀ y ∈ Q.DomR k r D.z D.z',
      (Φ' : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D F') y.1 y.2)
    (H : Integrable (fun q : (Fin r → ℂ) × Mt k r => ((∏ a : Fin r, ‖q.1 a‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) q.1 (Matrix.of q.2))
        ((Φ' : Fn k r (Wq →L[ℂ] Wp)) q.1 (Matrix.of q.2))) (volume.prod μ)) :
    Integrable (fun q => (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D F' (B.gq D q))) (B.hsVec (B.JF D F (B.gq D q)))) := by
  have hsf := B7.sf hμ
  have hmeas : AEStronglyMeasurable (fun q => (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D F' (B.gq D q))) (B.hsVec (B.JF D F (B.gq D q)))) volume := by
    refine rb_aesm D _ ?_ fun q h => by simp [h]
    exact (Complex.continuous_ofReal.comp_continuousOn (rb_contOn_bcW D)).mul
      ((rb_contOn_J D F' hF').inner (rb_contOn_J D F hF))
  have hμb : B.IsHaarOn (B2.UWb k r) μ := by
    rw [rb_uwb_eq]
    exact hμ
  obtain ⟨C, hC, hmap⟩ := rb_map D.k_pos D.z_mem D.z'_mem D.T_pos D.T'_pos D.sec hμb D.haarW D.haarW'
  have hfW : IsFiniteMeasure D.μW := RankOneEmbeddings.R1.haar_finite B2x3.compactW D.z_mem D.T_pos D.haarW
  have hfW' : IsFiniteMeasure D.μW' := RankOneEmbeddings.R1.haar_finite B2x3.compactW D.z'_mem D.T'_pos D.haarW'
  set m : ℝ := (C : ℝ) * (D.μW.prod D.μW').real Set.univ with hm
  have hm0 : m ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast hC.ne') ?_
    rw [Measure.real_def, ← Set.univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul]
    refine mul_ne_zero (ENNReal.toReal_ne_zero.2 ⟨?_, measure_ne_top _ _⟩)
      (ENNReal.toReal_ne_zero.2 ⟨?_, measure_ne_top _ _⟩)
    · exact Measure.measure_univ_ne_zero.2 D.haarW.ne_zero
    · exact Measure.measure_univ_ne_zero.2 D.haarW'.ne_zero
  let Wc : (Fin r → ℂ) → ℂ := fun c => ((∏ a : Fin r, ‖c a‖ ^ (-2 : ℤ) : ℝ) : ℂ)
  let ψ : (Fin r → ℂ) → ℂ → ℂ := fun c ζ => Wc c *
    (((rbGauge k r c ^ 2 : ℝ) : ℂ) * B.hsInner (B.JF D F (B.gq D (c, ζ))) (B.JF D F' (B.gq D (c, ζ))))
  have hψ : ∀ c ∈ OmX r, ∀ ζ, (B2.zWeight k (Tz k r D.z) (Tz k r D.z') ζ : ℂ) * ψ c ζ =
      (bcWeight k r (Tz k r D.z) (Tz k r D.z') (c, ζ) : ℂ) *
        inner ℂ (B.hsVec (B.JF D F' (B.gq D (c, ζ)))) (B.hsVec (B.JF D F (B.gq D (c, ζ)))) := by
    intro c hc ζ
    simp only [ψ, Wc]
    rw [mul_left_comm, rb_weight hc]
    rfl
  rw [show (volume : Measure ((Fin r → ℂ) × ℂ)) = (volume : Measure (Fin r → ℂ)).prod volume from rfl] at hmeas ⊢
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards [H.prod_right_ae, rb_ae_OmX] with c h1 hc
    have := integrable_zeta_of_integrable hC D.T_pos D.T'_pos D.sec D.haarW D.haarW' hmap _ h1 (ψ c)
      (fun ζ hζ x y hx hy => congrArg (fun t => Wc c * t) (rb_point D F F' Φ Φ' hΦ hΦ' hc hζ hx hy))
    exact this.congr (Filter.Eventually.of_forall (hψ c hc))
  · refine (H.integral_norm_prod_left.const_mul m⁻¹).congr ?_
    filter_upwards [rb_ae_OmX] with c hc
    have hsm : StronglyMeasurable fun g : Mt k r => ((‖Wc c * B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
        ((Φ' : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))‖ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp_stronglyMeasurable (((rb_pair_sm Φ Φ' c).const_mul (Wc c)).norm)
    have key := rb_integral D.T_pos D.T'_pos D.sec D.haarW D.haarW' hmap _ hsm (fun ζ => ((‖ψ c ζ‖ : ℝ) : ℂ))
      (fun ζ hζ x y hx hy => congrArg (fun t => ((‖Wc c * t‖ : ℝ) : ℂ)) (rb_point D F F' Φ Φ' hΦ hΦ' hc hζ hx hy))
    have e : ∀ ζ, (B2.zWeight k (Tz k r D.z) (Tz k r D.z') ζ : ℂ) * ((‖ψ c ζ‖ : ℝ) : ℂ) =
        ((‖(bcWeight k r (Tz k r D.z) (Tz k r D.z') (c, ζ) : ℂ) *
        inner ℂ (B.hsVec (B.JF D F' (B.gq D (c, ζ)))) (B.hsVec (B.JF D F (B.gq D (c, ζ))))‖ : ℝ) : ℂ) := by
      intro ζ
      rw [← hψ c hc ζ, norm_mul _ (ψ c ζ), Complex.norm_real, Real.norm_of_nonneg (rb_zWeight_nonneg k _ _ ζ),
        Complex.ofReal_mul]
    simp only [e] at key
    rw [integral_complex_ofReal, integral_complex_ofReal, ← Complex.ofReal_mul, Complex.ofReal_inj] at key
    show m⁻¹ * ∫ g, ‖Wc c * B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
        ((Φ' : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))‖ ∂μ = _
    rw [key, ← hm, ← mul_assoc, inv_mul_cancel₀ hm0, one_mul]

theorem integrable_bigCell_of_cpt (hP : P5.ThmPActualCpt) (P : M.Par) (D : B.RealPlaceData P.k P.r Wp Wq)
    (X : ActualOps P.k P.r D.z D.z' D.π D.π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r D.z D.z' D.π D.π')) P.r)
    (st : Fr.Start (Pr (RadSp P.k P.r D.z D.z' D.π D.π'))) (l0 : ℕ)
    (hD : IsData P D.z D.z' D.π D.π' X μ L st l0) (hl1 : 1 ≤ l0) (hlk : l0 ≤ P.k)
    (F F' : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef D F) (hF' : KB.CptCoef D F') :
    Integrable (fun q => (bcWeight P.k P.r (Tz P.k P.r D.z) (Tz P.k P.r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D F' (B.gq D q))) (B.hsVec (B.JF D F (B.gq D q)))) := by
  obtain ⟨K, -, -, hC, hJ⟩ := hP Wp Wq Empty P _ _ _ _ X μ L st l0 D _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  obtain ⟨Φ, hΦK, hΦ⟩ := PBO.pic_cpt D (K 0) hJ hF
  obtain ⟨Φ', hΦ'K, hΦ'⟩ := PBO.pic_cpt D (K 0) hJ hF'
  obtain ⟨ε, -, hn⟩ := (PBF.cpt_nice_bsr hF).1
  obtain ⟨ε', -, hn'⟩ := (PBF.cpt_nice_bsr hF').1
  have hsf := B7.sf hD.2.1
  exact integrable_bigCell_of_radial D μ hD.2.1 F F' hn.2.1 hn'.2.1 Φ Φ' hΦ hΦ'
    (integrable_pair_of_cor P _ _ _ _ μ L st K l0 hC Φ Φ' hΦK hΦ'K)

theorem form_eq_sum_beta {k r : ℕ} (D : B.RealPlaceData k r Wp Wq) (μ : Measure (Mt k r)) (C1 : ℝ)
    (hpair : ∀ (F F' : B.Mat k r → (Wq →L[ℂ] Wp)) (Φ Φ' : Q.RadSp k r D.z D.z' D.π D.π'),
      (∀ y ∈ Q.DomR k r D.z D.z',
        (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D F) y.1 y.2) →
      (∀ y ∈ Q.DomR k r D.z D.z',
        (Φ' : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D F') y.1 y.2) →
      ∀ c ∈ OmX r, P5.pairAt μ Φ Φ' c = (C1 : ℂ) * ∫ ζ, (B2.zWeight k (Tz k r D.z) (Tz k r D.z') ζ : ℂ) *
        (((rbGauge k r c ^ 2 : ℝ) : ℂ) * B.hsInner (B.JF D F (B.gq D (c, ζ))) (B.JF D F' (B.gq D (c, ζ)))))
    {n : ℕ} (x x' : Wd.Ix (Fin n) → B.Mat k r → (Wq →L[ℂ] Wp)) (Φ Φ' : Wd.Ix (Fin n) → Q.RadSp k r D.z D.z' D.π D.π')
    (hI : ∀ a, Integrable (fun q => (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D (x' a) (B.gq D q))) (B.hsVec (B.JF D (x a) (B.gq D q)))))
    (hΦ : ∀ a, ∀ y ∈ Q.DomR k r D.z D.z',
      (Φ a : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D (x a)) y.1 y.2)
    (hΦ' : ∀ a, ∀ y ∈ Q.DomR k r D.z D.z',
      (Φ' a : Q.Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = Q.resG k r (Fin.last r) (B.JF D (x' a)) y.1 y.2) :
    P5.form μ 0 Φ Φ' 0 = (C1 : ℂ) * ∑ a, B.beta D (x a) (x' a) := by
  rw [rb_form_eq]
  let f : Wd.Ix (Fin n) → (Fin r → ℂ) × ℂ → ℂ := fun a q =>
    (bcWeight k r (Tz k r D.z) (Tz k r D.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF D (x' a) (B.gq D q))) (B.hsVec (B.JF D (x a) (B.gq D q)))
  have hint : ∀ a, Integrable (f a) := hI
  have hae : (fun c : Fin r → ℂ => ((∏ a : Fin r, ‖c a‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ b, P5.pairAt μ (Φ b) (Φ' b) c)
      =ᵐ[volume] fun c => ∑ b, (C1 : ℂ) * ∫ ζ, f b (c, ζ) := by
    filter_upwards [rb_ae_OmX] with c hc
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hpair (x b) (x' b) (Φ b) (Φ' b) (hΦ b) (hΦ' b) c hc, mul_left_comm, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    dsimp only
    rw [rb_weight hc]
    rfl
  rw [integral_congr_ae hae, integral_finsetSum _ (fun b _ => ((hint b).integral_prod_left).const_mul _),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, ← integral_prod _ (hint b)]
  rfl

end pairing

def FormConstOneCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (j : Fin (P0.r + 1))
    (X : Q.ActualOps (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (μ : Measure (Formalism.QuantumDeterminants.Mt (JC.parLev P0 j).k (JC.parLev P0 j).r))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
      (T.bs j).π')) (JC.parLev P0 j).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
      (T.bs j).π'))) (l0 : ℕ),
    P5.IsData (JC.parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0 →
    KB.ZetaNorm (T.bs j) μ → 1 ≤ l0 → l0 ≤ P0.k →
    ∀ (w : List C.Letter) (F F' : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
      (Φ Φ' : Wd.Ix (Fin w.length) →
        Q.RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'),
      (∀ a, KB.CptCoef (T.bs j) (F a)) → (∀ a, KB.CptCoef (T.bs j) (F' a)) →
      (∀ a, ∀ y ∈ Q.DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
        (Φ a : Q.Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          Q.resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) (B.JF (T.bs j) (F a)) y.1 y.2) →
      (∀ a, ∀ y ∈ Q.DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
        (Φ' a : Q.Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          Q.resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) (B.JF (T.bs j) (F' a)) y.1 y.2) →
      D.formLev T (M.sgn P0 l0) j w F F' = P5.form μ 0 (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ' 0

theorem formConstOneCpt (hP : P5.ThmPActualCpt) : FormConstOneCpt := by
  intro Wp Wq _ _ _ _ _ _ P0 T j X μ L st l0 hD hZ hl1 hlk w F F' Φ Φ' hFc hFc' hΦ hΦ'
  obtain ⟨ε, hε, hF⟩ := PBO.nice_common (T.bs j) hFc
  choose R hR using fun a => (hFc a).2.1
  have hRs : ∀ a, PBF.BSR (∑ b, |R b|) (F a) := fun a g hg hne =>
    ((hR a g hg hne).trans (le_abs_self _)).trans
      (Finset.single_le_sum (f := fun b => |R b|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a))
  have hN : ∀ a, KB.CptCoef (T.bs j) (D.actOp (D.RRlev T (M.sgn P0 l0) j w) F a) := fun a => by
    obtain ⟨h1, h2⟩ := PBF.actOp_nice_bsr P0 T (M.sgn P0 l0) j w F hF hRs a
    exact ⟨h1.1, ⟨_, h2⟩, ε, hε, h1.2.2⟩
  have hPic : ∀ a, ∀ y ∈ Q.DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
      (P5.act (P5.RRi L st 0 (D.positionted w)) Φ a : Q.Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
        Q.resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _)
          (B.JF (T.bs j) (D.actOp (D.RRlev T (M.sgn P0 l0) j w) F a)) y.1 y.2 := by
    intro a y hy
    rw [Formalism.FourierDecayAlt.P.radial_module_action Wp Wq P0 T j X μ L st l0 hD w (fun b => B.JF (T.bs j) (F b)) Φ
      (fun b => Formalism.FourierDecayAlt.P.bessel_function_finite_class _ _ Wp Wq (T.bs j) (F b) ε hε (hF b)) hΦ a y hy]
    exact (Formalism.FourierDecayAlt.P.bessel_module Wp Wq P0 T (M.sgn P0 l0) j w F ε hε hF a y hy).symm
  have h := form_eq_sum_beta (T.bs j) μ 1
    (fun G G' Ψ Ψ' hΨ hΨ' c hc => PBF.pairAt_one (T.bs j) μ hZ G G' Ψ Ψ' hΨ hΨ' c hc)
    (D.actOp (D.RRlev T (M.sgn P0 l0) j w) F) F' (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ'
    (fun a => integrable_bigCell_of_cpt hP (JC.parLev P0 j) (T.bs j) X μ L st l0 hD hl1 hlk _ _ (hN a) (hFc' a)) hPic hΦ'
  refine Eq.trans ?_ h.symm
  simp only [Complex.ofReal_one, one_mul]
  rfl

end GlobalTheory.CptBesselPairing

end

noncomputable section

namespace GlobalTheory.CptBesselPairing

section wave

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.QuantumDeterminants

theorem uInv_eq_zero {Y Z : Type} [AddCommGroup Z] [Module ℂ Z] (s : ℂ) (g : Y) :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → Y → Z) (e : Wd.Ix (Fin w.length)),
      (∀ a, x a g = 0) → KB.uInv s w x e g = 0
  | [], _, e, h => h e
  | l :: w, x, e, h => by
    have h0 := uInv_eq_zero s g w (fun e' => x (Fin.cons 0 e')) (fun a => e a.succ) (fun a => h _)
    have h1 := uInv_eq_zero s g w (fun e' => x (Fin.cons 1 e')) (fun a => e a.succ) (fun a => h _)
    simp only [KB.uInv]
    by_cases h : e 0 = 0
    · simp only [if_pos h]
      exact h0
    · simp only [if_neg h, Pi.add_apply, Pi.smul_apply]
      rw [h0, h1, smul_zero, add_zero]

theorem waveG_cptCoef {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) (hx : ∀ e, KB.CptCoef Bs (x e))
    (e : Wd.Ix (Fin w.length)) : KB.CptCoef Bs (KB.waveG Bs s w x e) := by
  obtain ⟨ε, hε, hn⟩ := PBO.nice_common Bs hx
  have hw := PBFV.waveG_nice Bs ε s w x hn e
  refine ⟨hw.1, ?_, ε, hε, hw.2.2⟩
  choose R hR using fun a => (hx a).2.1
  refine ⟨∑ a, |R a|, fun g hg hne => ?_⟩
  by_cases h0 : ∀ a, x a g = 0
  · exact absurd (by simp only [KB.waveG]; rw [uInv_eq_zero s g w x e h0, smul_zero]) hne
  · push Not at h0
    obtain ⟨a, ha⟩ := h0
    exact ((hR a g hg ha).trans (le_abs_self _)).trans
      (Finset.single_le_sum (f := fun a => |R a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a))

end wave

section head

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBP
open scoped ComplexConjugate

theorem radHead_of_cpt (hOne : FormConstOneCpt) (hZN : PBO.ZetaNormExists) (hHP : HeadPic) : KB.RadHead := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h h' hh hh' X μ L st Φ Φ' hD hZ hF hw hΦ hΦ' t ht
  let jF : Fin (P.r + 1) := ⟨j + 1, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨Xs⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨Ls, sts, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl Xs p.l0
  obtain ⟨μs, hμs⟩ := hZN P.k (P.r - (j + 1)) Wp Wq (p.T.bs (j + 1))
  have hDs : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' Xs μs Ls sts p.l0 :=
    ⟨hPl, hμs.1, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨T, hT, hph⟩ :=
    Formalism.FourierDecayAlt.P.radial_transport_plus Wp Wq P p j hj X μ L st Xs μs Ls sts hD hZ hDs hμs t ht
  refine (hph (Fin w.length) (D.positionted w) Φ Φ' (fun _ => 1) 0).trans ?_
  have hl := isLocPt_snoc hh ht
  have hl' := isLocPt_snoc hh' ht

  set x2 := KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) hl.2 with hx2def
  set x2' := KB.slv p.T F (j + 1) hj w (h' ++ [(1, t)]) hl'.2 with hx2'def
  have hc2 : ∀ e, KB.CptCoef (p.T.bs (j + 1)) (x2 e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F (j + 1) hj w _ hl hF e
  have hc2' : ∀ e, KB.CptCoef (p.T.bs (j + 1)) (x2' e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F (j + 1) hj w _ hl' hF e

  set lam : ℝ := ‖t‖ ^ (2 * (P.r - j) + P.k) with hlam
  have hlam0 : lam ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 ht)
  have hlamC : ((lam : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hlam0
  let b0 : Fin (JC.parLev P j).r := ⟨0, by change 0 < P.r - j; omega⟩
  let Φ2 := fun e => (((lam⁻¹ : ℝ)) : ℂ) • T (P5.act (P5.bTl L b0 (D.positionted w)) Φ e)
  let Φ2' := fun e => (((lam⁻¹ : ℝ)) : ℂ) • T (P5.act (P5.bTl L b0 (D.positionted w)) Φ' e)
  have hpic : ∀ (hh₀ : C.LPt) (hhh : D.IsLocPt hh₀ j) (Ψ : Wd.Ix (Fin w.length) →
      Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π'),
      (∀ e, Top.IsRadOf (JC.parLev P j) (p.T.bs j) (Ψ e) (KB.slv p.T F j (by omega) w hh₀ hhh.2 e)) →
      ∀ e, ∀ y ∈ Q.DomR (JC.parLev P jF).k (JC.parLev P jF).r (p.T.bs jF).z (p.T.bs jF).z',
        Subtype.val ((((lam⁻¹ : ℝ)) : ℂ) • T (P5.act (P5.bTl L b0 (D.positionted w)) Ψ e)) y.1 y.2 =
          Q.resG (JC.parLev P jF).k (JC.parLev P jF).r (Fin.last _)
            (B.JF (p.T.bs jF) (KB.slv p.T F (j + 1) hj w (hh₀ ++ [(1, t)]) (isLocPt_snoc hhh ht).2 e)) y.1 y.2 := by
    intro hh₀ hhh Ψ hΨ e y hy
    have e1 := hT (P5.act (P5.bTl L b0 (D.positionted w)) Ψ e) y.1 y.2
    have e2 := hHP Wp Wq P p F j hj w hh₀ hhh X μ L st Ψ hD hF hw hΨ t (isLocPt_snoc hhh ht) e y hy
    have hcl : ∀ v : Wq →L[ℂ] Wp, ((lam⁻¹ : ℝ) : ℂ) • (((lam : ℝ) : ℂ) • v) = v := fun v => by
      rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam0, Complex.ofReal_one, one_smul]
    exact (congrArg (fun v => ((lam⁻¹ : ℝ) : ℂ) • v) (e1.trans e2)).trans (hcl _)
  have hΦ2 := hpic h hh Φ hΦ
  have hΦ2' := hpic h' hh' Φ' hΦ'
  have hOne' := hOne Wp Wq P p.T jF Xs μs Ls sts p.l0 hDs hμs p.hl.1 p.hl.2.1 w x2 x2' Φ2 Φ2' hc2 hc2' hΦ2 hΦ2'
  have hTΦ : (fun a => T (P5.act (P5.bTl L b0 (D.positionted w)) Φ a)) = fun a => ((lam : ℝ) : ℂ) • Φ2 a := by
    funext a
    simp only [Φ2, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hlam0, Complex.ofReal_one, one_smul]
  have hTΦ' : (fun a => T (P5.act (P5.bTl L b0 (D.positionted w)) Φ' a)) = fun a => ((lam : ℝ) : ℂ) • Φ2' a := by
    funext a
    simp only [Φ2', smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hlam0, Complex.ofReal_one, one_smul]
  rw [hTΦ, hTΦ']
  have hRR : p.RR F (j + 1) w (h ++ [(1, t)]) (h' ++ [(1, t)]) = D.formLev p.T (M.sgn P p.l0) jF w x2 x2' := by
    unfold KB.Pl.RR D.RRplace
    rw [dif_pos ⟨hl, hl'⟩, dif_pos hj]
    rfl
  have key : P5.RRform Ls sts μs 0 (D.positionted w) Φ2 Φ2' 0 = D.formLev p.T (M.sgn P p.l0) jF w x2 x2' := hOne'.symm
  calc _ = ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ((lam : ℂ) * conj (lam : ℂ) * P5.RRform Ls sts μs 0 (D.positionted w) Φ2 Φ2' 0) :=
        congrArg _ (rrform_smul Ls sts μs 0 (D.positionted w) Φ2 Φ2' 0 (lam : ℂ))
    _ = ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ((lam : ℂ) * conj (lam : ℂ) * D.formLev p.T (M.sgn P p.l0) jF w x2 x2') := by
        rw [key]
    _ = _ := by
        rw [hRR, ← levW_below P j hj ht, Complex.conj_ofReal, hlam]
        push_cast
        ring

end head

section formula

open Matrix MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5
  Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBO

theorem planeWave_top (hP : P5.ThmPActualCpt) (hHT : KB.HeadTop) (hOne : FormConstOneCpt) (hZN : ZetaNormExists)
    (hTC : TopContOn) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (h h' : C.LPt) (hh : D.IsLocPt h P.r)
    (hh' : D.IsLocPt h' P.r) (Cb : ℝ) (hθ : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hF : KB.CptCoef p.T.base F)
    (hw : KB.CutWord P p.l0 w) :
    ∃ φ : ℂ → ℂ, Continuous φ ∧ Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (KB.levW P (P.r + 1) c : ℂ) * p.RR F (P.r + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form P.r le_rfl w (KB.waveG (p.T.bs P.r) s w (KB.slv p.T F P.r le_rfl w h hh.2))
          (KB.slv p.T F P.r le_rfl w h' hh'.2) := by
  classical
  obtain ⟨hl1, hlk, hk2⟩ := p.hl
  have hr0 : P.r - P.r = 0 := Nat.sub_self _
  let jF : Fin (P.r + 1) := ⟨P.r, Nat.lt_succ_self _⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ, hμ⟩ := hZN P.k (P.r - P.r) Wp Wq (p.T.bs P.r)
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X μ L st p.l0 :=
    ⟨hPl, hμ.1, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨K, hThm, -, -, hJ⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  have hwOK := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 w hw.1 hw.2
  set x := KB.slv p.T F P.r le_rfl w h hh.2 with hxdef
  set x' := KB.slv p.T F P.r le_rfl w h' hh'.2 with hx'def
  have hcx : ∀ e, KB.CptCoef (p.T.bs P.r) (x e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F P.r le_rfl w h hh hF e
  have hcx' : ∀ e, KB.CptCoef (p.T.bs P.r) (x' e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F P.r le_rfl w h' hh' hF e
  obtain ⟨ε₁, hε₁, hx⟩ := nice_common (p.T.bs P.r) hcx
  obtain ⟨ε₂, hε₂, hx'⟩ := nice_common (p.T.bs P.r) hcx'
  set ε := min ε₁ ε₂ with hεdef
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hxn : ∀ e, JC.NiceCoef (p.T.bs P.r) ε (x e) := fun e =>
    ⟨(hx e).1, (hx e).2.1, fun g hg h0 => le_trans (min_le_left _ _) ((hx e).2.2 g hg h0)⟩
  have hxn' : ∀ e, JC.NiceCoef (p.T.bs P.r) ε (x' e) := fun e =>
    ⟨(hx' e).1, (hx' e).2.1, fun g hg h0 => le_trans (min_le_right _ _) ((hx' e).2.2 g hg h0)⟩
  choose Φ hΦK hΦ using fun a => pic_cpt (p.T.bs P.r) (K 0) hJ (hcx a)
  choose Φ' hΦ'K hΦ' using fun a => pic_cpt (p.T.bs P.r) (K 0) hJ (hcx' a)
  have hHTa := hHT Wp Wq P p F w h h' hh hh' X μ L st Cb Φ Φ' hD hθ hF hw hΦ hΦ'

  let c0 : Fin (JC.parLev P jF).r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX (JC.parLev P jF).r := fun _ => one_ne_zero
  obtain ⟨hint, hs⟩ := topPart_zero (JC.parLev P jF) _ _ _ _ μ L st K (D.positionted w) (hThm (D.positionted w) hwOK).1 hr0
    Φ Φ' hΦK hΦ'K c0 hc0
  have hTz : Tz P.k (P.r - P.r) (p.T.bs P.r).z = P.T := hPl.2.2.2.1
  have hTz' : Tz P.k (P.r - P.r) (p.T.bs P.r).z' = P.T' := hPl.2.2.2.2.1

  set R : ℂ → ℂ := fun c => p.RR F (P.r + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)]) with hRdef
  set U : Set ℂ := {c | P.T * P.T' < Complex.normSq c} with hUdef
  set ψ : ℂ → ℂ := U.piecewise R 0 with hψdef
  have hRc : ContinuousOn R U := hTC Wp Wq P p F w h h' hh hh' Cb hθ hF hw
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_normSq
  have hψm : Measurable ψ := hRc.measurable_piecewise continuousOn_const hUo.measurableSet
  have hae : ∀ᵐ g ∂μ, topDens L st (D.positionted w) Φ Φ' c0 (Matrix.of g) =
      ψ (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) (Matrix.of g)) := by
    filter_upwards [Formalism.FourierDecayAlt.P.B7.ae_mem hμ.1] with g hg
    by_cases hG : 0 < GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of g)
    · have hdom : (c0, Matrix.of g) ∈ DomR P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' := ⟨hc0, hg, hG⟩
      rw [hHTa (c0, Matrix.of g) hdom]
      have hU' : Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) (Matrix.of g) ∈ U := by
        unfold GGl at hG
        rw [hTz, hTz'] at hG
        show P.T * P.T' < _
        linarith
      rw [hψdef, Set.piecewise_eq_of_mem _ _ _ hU']
      rfl
    · have hnd : (c0, Matrix.of g) ∉ DomR P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' := fun hd => hG hd.2.2
      have hU' : Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) (Matrix.of g) ∉ U := by
        intro hm
        apply hG
        unfold GGl
        rw [hTz, hTz']
        have : P.T * P.T' < _ := hm
        linarith
      rw [hψdef, Set.piecewise_eq_of_notMem _ _ _ hU']
      unfold topDens
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [(act (Fr.ofWord L st (D.positionted w)).F Φ' e).2.1 (c0, Matrix.of g) hnd, hsInner_zero_right']

  set φ : ℂ → ℂ := fun c => (KB.levW P (P.r + 1) c : ℂ) * R c with hφdef
  have hlev : ∀ c, KB.levW P (P.r + 1) c = B2.zWeight P.k P.T P.T' c := fun c => by simp [KB.levW]
  have hφψ : ∀ c, (B2.zWeight P.k P.T P.T' c : ℂ) * ψ c = φ c := by
    intro c
    rw [hφdef]
    simp only [hlev]
    by_cases hc : c ∈ U
    · rw [hψdef, Set.piecewise_eq_of_mem _ _ _ hc]
    · rw [hψdef, Set.piecewise_eq_of_notMem _ _ _ hc]
      have hz : B2.zWeight P.k P.T P.T' c = 0 := by
        unfold B2.zWeight
        split_ifs with hle
        · have hcU : ¬ P.T * P.T' < Complex.normSq c := hc
          have he : Complex.normSq c - P.T * P.T' = 0 := by linarith
          rw [he, zero_pow (by omega)]
        · rfl
      rw [hz]; simp
  refine ⟨φ, ?_, ?_, fun c _ => rfl, fun s => ?_⟩
  · exact (phi_top_cont hTC P p F w h h' hh hh' Cb hθ hF hw).congr fun c => by rw [hφdef]; simp only [hlev]; rfl
  · have hi := zetaNorm_integrable hμ ψ hψm (hint.congr hae)
    rw [hTz, hTz'] at hi
    exact hi.congr (Filter.Eventually.of_forall hφψ)
  · obtain ⟨Wv, hW⟩ := waveZExists Wp Wq P.k (P.r - P.r) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' s
    obtain ⟨Wv', hW'⟩ := waveZExists Wp Wq P.k (P.r - P.r) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π
      (p.T.bs jF).π' (-s)
    have key := hs s Wv Wv' hW hW'
    have hm : ∀ y ∈ DomR P.k (P.r - P.r) (p.T.bs jF).z (p.T.bs jF).z',
        (fun (_ : Fin (P.r - P.r) → ℂ) (g : Mx P.k (P.r - P.r)) => fsv s (P5.zeta P.k (P.r - P.r) (p.T.bs jF).z
          (p.T.bs jF).z' g)) y.1 y.2 =
          fsv s (Dmin P.k (P.r - P.r) (p.T.bs jF).z (p.T.bs jF).z' (wCell P.k (P.r - P.r) (Fin.last _) y.1 * y.2)
            ⟨1, by omega⟩) := fun y hy => by
      simp only []
      rw [Formalism.FourierDecayAlt.P.PBFV.first_minor_top_eq_zeta hr0]
    have hΨ := Formalism.FourierDecayAlt.P.PBFV.radPic_wave (p.T.bs jF) ε s w x hxn Φ hΦ _ (by omega) hm Wv Wv' hW
    have hform := hOne Wp Wq P p.T jF X μ L st p.l0 hD hμ hl1 hlk w _ _ _ _ (waveG_cptCoef _ s w x hcx) hcx' hΨ hΦ'
    have hmeas : Measurable fun ζ => fsv s ζ * ψ ζ := (continuous_fsv s).measurable.mul hψm
    have hlaw := zetaNorm_integral hμ (fun ζ => fsv s ζ * ψ ζ) hmeas
    rw [hTz, hTz'] at hlaw
    calc ∫ c, fsv s c * φ c = ∫ ζ, (B2.zWeight P.k P.T P.T' ζ : ℂ) * (fsv s ζ * ψ ζ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
          simp only []
          rw [← hφψ c]; ring
      _ = ∫ g, fsv s (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) (Matrix.of g)) *
            ψ (Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) (Matrix.of g)) ∂μ := hlaw.symm
      _ = ∫ g, fsv s (P5.zeta P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of g)) *
            topDens L st (D.positionted w) Φ Φ' c0 (Matrix.of g) ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hae] with g hg
          rw [hg]; rfl
      _ = P5.form μ 0 (P5.act (RRi L st 0 (D.positionted w)) (act (Vw (mkP Wv Wv') s (D.positionted w)) Φ)) Φ' c0 := key
      _ = P5.form μ 0 (P5.act (RRi L st 0 (D.positionted w)) (act (Vw (mkP Wv Wv') s (D.positionted w)) Φ)) Φ' 0 :=
          Formalism.FourierDecayAlt.P.JCx2.form_zero_indep μ _ _ _ 0
      _ = _ := hform.symm

theorem planeWave_below (hP : P5.ThmPActualCpt) (hRH : KB.RadHead) (hOne : FormConstOneCpt) (hZN : ZetaNormExists)
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r) (hjr : j < P.r) (w : List C.Letter)
    (h h' : C.LPt) (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (hF : KB.CptCoef p.T.base F)
    (hw : KB.CutWord P p.l0 w) :
    ∃ φ : ℂ → ℂ, Continuous φ ∧ Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h' hh'.2) := by
  obtain ⟨hl1, hlk, -⟩ := p.hl
  have hr : 0 < P.r - j := by omega
  let jF : Fin (P.r + 1) := ⟨j, by omega⟩
  have hPl := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T jF p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ, hμ⟩ := hZN P.k (P.r - j) Wp Wq (p.T.bs j)
  have hD : IsData (JC.parLev P jF) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π' X μ L st p.l0 :=
    ⟨hPl, hμ.1, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨K, hThm, -, -, hJ⟩ := hP Wp Wq (Fin w.length) (JC.parLev P jF) _ _ _ _ X μ L st p.l0
    (p.T.bs jF) _ _ hD hl1 hlk rfl rfl rfl rfl le_rfl le_rfl
  have hwOK := Formalism.FourierDecayAlt.P.JCTx5.wordOK_of (JC.parLev P jF) _ _ _ _ st p.l0 hPl.1 hl1 hlk h3 h4 w hw.1 hw.2

  set x := KB.slv p.T F j hj w h hh.2 with hxdef
  set x' := KB.slv p.T F j hj w h' hh'.2 with hx'def
  have hcx : ∀ e, KB.CptCoef (p.T.bs j) (x e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w h hh hF e
  have hcx' : ∀ e, KB.CptCoef (p.T.bs j) (x' e) := fun e =>
    Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w h' hh' hF e
  obtain ⟨ε₁, hε₁, hx⟩ := nice_common (p.T.bs j) hcx
  obtain ⟨ε₂, hε₂, hx'⟩ := nice_common (p.T.bs j) hcx'
  set ε := min ε₁ ε₂ with hεdef
  have hε : 0 < ε := lt_min hε₁ hε₂
  have mono : ∀ {ε' : ℝ} {G : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)}, ε ≤ ε' → JC.NiceCoef (p.T.bs j) ε' G →
      JC.NiceCoef (p.T.bs j) ε G := fun hle hG => ⟨hG.1, hG.2.1, fun g hg h0 => le_trans hle (hG.2.2 g hg h0)⟩
  have hxn : ∀ e, JC.NiceCoef (p.T.bs j) ε (x e) := fun e => mono (min_le_left _ _) (hx e)
  have hxn' : ∀ e, JC.NiceCoef (p.T.bs j) ε (x' e) := fun e => mono (min_le_right _ _) (hx' e)
  choose Φ hΦK hΦ using fun a => pic_cpt (p.T.bs j) (K 0) hJ (hcx a)
  choose Φ' hΦ'K hΦ' using fun a => pic_cpt (p.T.bs j) (K 0) hJ (hcx' a)

  have hstep := (hThm (D.positionted w) hwOK).2.1 ⟨0, hr⟩
  have hl : (⟨0, hr⟩ : Fin (JC.parLev P jF).r).castSucc = 0 := Fin.ext rfl
  unfold StepP at hstep
  obtain ⟨φ, hφc, hφ, ⟨Cφ, hCφ⟩, hφs⟩ := hstep Φ Φ' (fun a => hΦK a)
    (fun a => hΦ'K a) (fun _ => 1) (fun _ => one_ne_zero)
  refine ⟨φ, hφc, integrable_of_decay4 hφc hCφ, fun c hc => ?_, fun s => ?_⟩
  · rw [hφ c hc]
    exact hRH Wp Wq P p F j (by omega) w h h' hh hh' X μ L st Φ Φ' hD hμ hF hw hΦ hΦ' c hc
  · obtain ⟨Wv, hW⟩ := waveCExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      ⟨0, hr⟩ s
    obtain ⟨Wv', hW'⟩ := waveCExists Wp Wq P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (p.T.bs jF).π (p.T.bs jF).π'
      ⟨0, hr⟩ (-s)
    have hm : ∀ y ∈ DomR P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z',
        (fun (c : Fin (P.r - j) → ℂ) (_ : Mx P.k (P.r - j)) => fsv s (c ⟨0, hr⟩)) y.1 y.2 =
          fsv s (Dmin P.k (P.r - j) (p.T.bs jF).z (p.T.bs jF).z' (wCell P.k (P.r - j) (Fin.last _) y.1 * y.2)
            ⟨1, by omega⟩) := fun y hy => by
      simp only []
      rw [Formalism.FourierDecayAlt.P.PBFV.first_minor_cell_eq_coord (p.T.bs jF).z_mem (p.T.bs jF).z'_mem hr y.1 hy.2.1]
    have hΨ := Formalism.FourierDecayAlt.P.PBFV.radPic_wave (p.T.bs jF) ε s w x hxn Φ hΦ _ (by omega) hm Wv Wv' hW
    rw [hφs s Wv Wv' hW hW']
    show _ = D.formLev p.T (M.sgn P p.l0) jF w (KB.waveG (p.T.bs j) s w x) x'
    rw [hOne Wp Wq P p.T jF X μ L st p.l0 hD hμ hl1 hlk w _ _ _ _ (waveG_cptCoef _ s w x hcx) hcx' hΨ hΦ']
    unfold RRform
    exact Formalism.FourierDecayAlt.P.JCx2.form_zero_indep μ _ _ _ 0

theorem planeWave_of_parts (hP : P5.ThmPActualCpt) (hRH : KB.RadHead) (hHT : KB.HeadTop) (hOne : FormConstOneCpt)
    (hZN : ZetaNormExists) (hTC : TopContOn) :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ →
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∃ φ : ℂ → ℂ, Continuous φ ∧ Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h' hh'.2) := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h h' hh hh' Cb hθ hF hw
  by_cases hjr : j < P.r
  · exact planeWave_below hP hRH hOne hZN P p F j hj hjr w h h' hh hh' hF hw
  · have e : j = P.r := by omega
    subst e
    exact planeWave_top hP hHT hOne hZN hTC P p F w h h' hh hh' Cb hθ hF hw

theorem planeWave_formula (hP : P5.ThmPActualCpt) :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h h' : C.LPt)
    (hh : D.IsLocPt h j) (hh' : D.IsLocPt h' j) (Cb : ℝ), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ →
    KB.CptCoef p.T.base F → KB.CutWord P p.l0 w →
    ∃ φ : ℂ → ℂ, Continuous φ ∧ MeasureTheory.Integrable φ ∧
      (∀ c : ℂ, c ≠ 0 → φ c = (KB.levW P (j + 1) c : ℂ) * p.RR F (j + 1) w (h ++ [(1, c)]) (h' ++ [(1, c)])) ∧
      ∀ s : ℂ, ∫ c, P5.fsv s c * φ c =
        p.form j hj w (KB.waveG (p.T.bs j) s w (KB.slv p.T F j hj w h hh.2)) (KB.slv p.T F j hj w h' hh'.2) :=
  planeWave_of_parts hP
    (radHead_of_cpt (formConstOneCpt hP) exists_zeta_normalized_haar head_picture) head_top
    (formConstOneCpt hP) exists_zeta_normalized_haar (topContOn_of hP head_top)

end formula

end GlobalTheory.CptBesselPairing

end

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory.LevelIntegralStep

theorem uInv_at_zero {X : Type} [AddCommGroup X] [Module ℂ X] :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → X), KB.uInv 0 w x = x
  | [], x => rfl
  | l :: w, x => by
    funext e
    have key : ∀ a : Fin 2, e (0 : Fin (w.length + 1)) = a →
        (Fin.cons a (fun b : Fin w.length => e b.succ) : Fin (w.length + 1) → Fin 2) = e := by
      intro a ha
      funext b
      refine Fin.cases ?_ (fun b => ?_) b
      · simp [ha]
      · simp
    simp only [KB.uInv, uInv_at_zero w, map_zero, ite_self, zero_smul, add_zero]
    split_ifs with h0
    · exact congrArg x (key 0 h0)
    · refine congrArg x (key 1 ?_)
      have : ∀ a : Fin 2, a ≠ 0 → a = 1 := by decide
      exact this _ h0

theorem fsv_at_zero (t : ℂ) : P5.fsv 0 t = 1 := by simp [P5.fsv]

theorem waveG_at_zero {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) : KB.waveG Bs 0 w x = x := by
  funext e g
  simp only [KB.waveG, fsv_at_zero, one_smul, uInv_at_zero]

theorem levelForm_eq_integral : P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (Cb : ℝ) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (j : ℕ) (h : C.LPt), KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base H → KB.CutWord P p.l0 w → j ≤ P.r → D.IsLocPt h j → Integrable (fun t : ℂ => (KB.levW P (j + 1) t : ℂ) * p.RR H (j + 1) w (h ++ [(1, t)]) (h ++ [(1, t)])) ∧ p.RR H j w h h = ∫ t : ℂ, (KB.levW P (j + 1) t : ℂ) * p.RR H (j + 1) w (h ++ [(1, t)]) (h ++ [(1, t)]) := by
  intro hP Wp Wq _ _ _ _ _ _ P p Cb H w j h hCb hH hw hj hh
  obtain ⟨φ, -, hφi, hφe, hφs⟩ := GlobalTheory.CptBesselPairing.planeWave_formula hP Wp Wq P p H j hj w h h hh hh Cb hCb hH hw
  have hae : φ =ᵐ[volume] fun t : ℂ =>
      (KB.levW P (j + 1) t : ℂ) * p.RR H (j + 1) w (h ++ [(1, t)]) (h ++ [(1, t)]) := by
    have h0 : ∀ᵐ t : ℂ, t ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with t ht using hφe t ht
  refine ⟨hφi.congr hae, ?_⟩
  have h1 := hφs 0
  simp only [fsv_at_zero, one_mul, waveG_at_zero] at h1
  rw [Formalism.FourierDecayAlt.P.PBL.rr_eq_form p H j hj w h h hh hh, ← h1]
  exact integral_congr_ae hae

end GlobalTheory.LevelIntegralStep
