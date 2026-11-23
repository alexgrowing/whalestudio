import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JReproA

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.ReproducingFormula

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ}

theorem first_pointwise_bound (hCG : IsClosedSubgroup (GV k r)) (hL : ∀ g ∈ GV k r, 1 ≤ gN g) {a : ℝ} (ha : 0 ≤ a)
    {s y : Mat k r} (hs : s ∈ GV k r) (hy : y ∈ GV k r) {c1 c2 C1 C2 : ℝ}
    (h1 : c1 ≤ C1 * gN y ^ (-a)) (h2 : c2 ≤ C2 * gN (s * y) ^ (-a)) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) :
    c1 * c2 ≤ C1 * C2 * KH k r ^ (a / 2) * (gN y ^ (-(a / 2)) * gN s ^ (-(a / 2))) := by
  have hK := KH_pos hCG hL
  have hsy : s * y ∈ GV k r := hCG.mul_mem _ hs _ hy
  have hX : gN s ≤ KH k r * (gN y * gN (s * y)) := by
    have e : s * y * y⁻¹ = s := by rw [Matrix.mul_assoc, GV_mul_inv hy, Matrix.mul_one]
    calc gN s = gN (s * y * y⁻¹) := by rw [e]
      _ ≤ gN (s * y) * gN y⁻¹ := gN_mul_le _ _
      _ ≤ gN (s * y) * (KH k r * gN y) := mul_le_mul_of_nonneg_left (gN_inv_le hy) (gN_nonneg _)
      _ = KH k r * (gN y * gN (s * y)) := by ring
  have hkb := key_bound (hL y hy) (hL _ hsy) (hL s hs) hK ha hX
  calc c1 * c2 ≤ (C1 * gN y ^ (-a)) * (C2 * gN (s * y) ^ (-a)) :=
        mul_le_mul h1 h2 hc2 (le_trans hc1 h1)
    _ = C1 * C2 * (gN y ^ (-a) * gN (s * y) ^ (-a)) := by ring
    _ ≤ C1 * C2 * (KH k r ^ (a / 2) * (gN y ^ (-(a / 2)) * gN s ^ (-(a / 2)))) :=
        mul_le_mul_of_nonneg_left hkb (mul_nonneg hC1 hC2)
    _ = _ := by ring

theorem second_pointwise_bound (hCG : IsClosedSubgroup (GV k r)) (hL : ∀ g ∈ GV k r, 1 ≤ gN g) {a : ℝ} (ha : 0 ≤ a)
    {s y : Mat k r} (hs : s ∈ GV k r) (hy : y ∈ GV k r) {c1 c2 C1 C2 : ℝ}
    (h1 : c1 ≤ C1 * gN y ^ (-a)) (h2 : c2 ≤ C2 * gN (s⁻¹ * y) ^ (-a)) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) :
    c1 * c2 ≤ C1 * C2 * KH k r ^ (a / 2) * KH k r ^ (a / 2) * (gN y ^ (-(a / 2)) * gN s ^ (-(a / 2))) := by
  have hK := KH_pos hCG hL
  have hsi : s⁻¹ ∈ GV k r := inv_mem_G hCG hs
  have h3 := first_pointwise_bound hCG hL ha hsi hy h1 h2 hc1 hc2 hC1 hC2
  have h4 : gN s⁻¹ ^ (-(a / 2)) ≤ KH k r ^ (a / 2) * gN s ^ (-(a / 2)) :=
    rpow_inv_le (by linarith [hL s hs]) hK (by linarith) (gN_le_inv hCG hs)
  have h5 : 0 ≤ gN y ^ (-(a / 2)) := Real.rpow_nonneg (gN_nonneg _) _
  have h6 : 0 ≤ C1 * C2 * KH k r ^ (a / 2) := mul_nonneg (mul_nonneg hC1 hC2) (Real.rpow_nonneg hK.le _)
  calc c1 * c2 ≤ C1 * C2 * KH k r ^ (a / 2) * (gN y ^ (-(a / 2)) * gN s⁻¹ ^ (-(a / 2))) := h3
    _ ≤ C1 * C2 * KH k r ^ (a / 2) * (gN y ^ (-(a / 2)) * (KH k r ^ (a / 2) * gN s ^ (-(a / 2)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 h5) h6
    _ = _ := by ring

theorem int_G (hGI : GNIntSharp) (μ : Measure (Mt k r)) (hμ : IsHaarOn (GV k r) μ) {b : ℝ} (hb : AB k r ≤ b) :
    Integrable (fun y : Mt k r => gN (Matrix.of y) ^ (-b)) μ := by
  have hlt := hGI k r μ b hμ hb
  have hm : Measurable (fun y : Mt k r => gN (Matrix.of y) ^ (-b)) :=
    Measurable.pow_const (show Continuous (fun y : Mt k r => gN (Matrix.of y)) from continuous_gN).measurable _
  have := integrable_toReal_of_lintegral_ne_top hm.ennreal_ofReal.aemeasurable hlt.ne
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  exact ENNReal.toReal_ofReal (Real.rpow_nonneg (gN_nonneg _) _)

def EE (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Set (Mt k r × (Mt k r × Mt k r)) :=
  {q | Matrix.of q.1 ∈ GV k r ∧ Matrix.of q.2.1 ∈ UWset k r z ∧ Matrix.of q.2.2 ∈ Nset k r}

theorem EE_closed (z : Fin (2 * r + k + 1) → ℂ) (hCG : IsClosedSubgroup (GV k r))
    (hCW : IsClosedSubgroup (UWset k r z)) (hCN : IsClosedSubgroup (Nset k r)) : IsClosed (EE k r z) :=
  (hCG.closed.preimage continuous_fst).inter ((hCW.closed.preimage (continuous_fst.comp continuous_snd)).inter
    (hCN.closed.preimage (continuous_snd.comp continuous_snd)))

section setting

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem ae_EE (D : RealPlaceData k r Wp Wp) :
    ∀ᵐ q ∂(D.μG.prod (D.μW.prod D.μN)), q ∈ EE k r D.z := by
  have hG : ∀ᵐ y ∂D.μG, Matrix.of y ∈ GV k r := ae_iff.2 (measure_mono_null (fun y hy => hy) D.haarG.conc)
  have hW : ∀ᵐ y ∂D.μW, Matrix.of y ∈ UWset k r D.z :=
    ae_iff.2 (measure_mono_null (fun y hy => hy) D.haarW.conc)
  have hN : ∀ᵐ y ∂D.μN, Matrix.of y ∈ Nset k r := ae_iff.2 (measure_mono_null (fun y hy => hy) D.haarN.conc)
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := D.μG) (ν := D.μW.prod D.μN)).ae hG
  have hW' := (Measure.quasiMeasurePreserving_fst (μ := D.μW) (ν := D.μN)).ae hW
  have hN' := (Measure.quasiMeasurePreserving_snd (μ := D.μW) (ν := D.μN)).ae hN
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := D.μG) (ν := D.μW.prod D.μN)).ae (hW'.and hN')
  filter_upwards [h1, h2] with q hq1 hq2
  exact ⟨hq1, hq2.1, hq2.2⟩

theorem pi_inv (D : RealPlaceData k r Wp Wp) (hCW : IsClosedSubgroup (UWset k r D.z)) {h : Mat k r}
    (hh : h ∈ UWset k r D.z) : D.π h⁻¹ = ContinuousLinearMap.adjoint (D.π h) :=
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  rep_inv_eq_adjoint D.π_rep D.π_unitary hh (hCW.inv_mem _ hh) (Matrix.mul_nonsing_inv _ (hCW.unit _ hh))

theorem cont_adj_pi (D : RealPlaceData k r Wp Wp) :
    ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) => ContinuousLinearMap.adjoint (D.π (Matrix.of q.2.1)))
      (EE k r D.z) :=
  haveI : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  (ContinuousLinearMap.adjoint : (Wp →L[ℂ] Wp) ≃ₗᵢ⋆[ℂ] (Wp →L[ℂ] Wp)).continuous.comp_continuousOn
    (D.π_cont.comp (continuous_fst.comp continuous_snd).continuousOn fun q hq => hq.2.1)

theorem cont_psi (D : RealPlaceData k r Wp Wp) :
    Continuous (fun q : Mt k r × (Mt k r × Mt k r) => star (psiD D (Matrix.of q.2.2))) :=
  continuous_star.comp ((psi_cont D.z cStd).comp (continuous_snd.comp continuous_snd))

theorem cont_sig_fst (X : SigData k r) (z : Fin (2 * r + k + 1) → ℂ) (x : X.Hs) :
    ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) => X.σ (Matrix.of q.1) x) (EE k r z) :=
  (X.rep.2.2 x).comp continuous_fst.continuousOn fun q hq => hq.1

theorem representation_continuousOn_product (X : SigData k r) (z : Fin (2 * r + k + 1) → ℂ) (hCG : IsClosedSubgroup (GV k r)) (x : X.Hs) :
    ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) => X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) x) (EE k r z) := by
  have hm : Continuous (fun q : Mt k r × (Mt k r × Mt k r) => (Matrix.of q.2.2 * Matrix.of q.2.1 : Mat k r)) :=
    (continuous_snd.comp continuous_snd).matrix_mul (continuous_fst.comp continuous_snd)
  exact (X.rep.2.2 x).comp hm.continuousOn fun _ hq => hCG.mul_mem _ hq.2.2.1 _ hq.2.1.1

theorem cont_sig_sy (X : SigData k r) (z : Fin (2 * r + k + 1) → ℂ) (hCG : IsClosedSubgroup (GV k r)) (x : X.Hs) :
    ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) =>
      X.σ (Matrix.of q.2.2 * Matrix.of q.2.1 * Matrix.of q.1) x) (EE k r z) := by
  have hm : Continuous (fun q : Mt k r × (Mt k r × Mt k r) =>
      (Matrix.of q.2.2 * Matrix.of q.2.1 * Matrix.of q.1 : Mat k r)) :=
    ((continuous_snd.comp continuous_snd).matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul continuous_fst
  exact (X.rep.2.2 x).comp hm.continuousOn fun _ hq =>
    hCG.mul_mem _ (hCG.mul_mem _ hq.2.2.1 _ hq.2.1.1) _ hq.1

end setting

section reproducing_fst

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem first_joint_integrable (D : RealPlaceData k r Wp Wp) (X : SigData k r)
    (hCG : IsClosedSubgroup (GV k r)) (hCW : IsClosedSubgroup (UWset k r D.z)) (hCN : IsClosedSubgroup (Nset k r))
    (hL : ∀ g ∈ GV k r, 1 ≤ gN g) (ha : 0 ≤ X.a)
    (hIG : Integrable (fun y : Mt k r => gN (Matrix.of y) ^ (-(X.a / 2))) D.μG)
    (hIS : Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-(X.a / 2)))
      (D.μW.prod D.μN))
    {u v : X.Hs} (hu : u ∈ Vfl X) (hv : v ∈ Vfl X) :
    Integrable (fun q : Mt k r × (Mt k r × Mt k r) =>
      ⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ • beInt D X (X.σ (Matrix.of q.1) X.w) v q.2) (D.μG.prod (D.μW.prod D.μN)) := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : IsFiniteMeasureOnCompacts D.μG := ⟨fun _ hK => D.haarG.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μW := ⟨fun _ hK => D.haarW.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun _ hK => D.haarN.finite_compact _ hK⟩
  obtain ⟨Cu, hCu0, hCu⟩ := dec_adj X hCG hL ha hu
  obtain ⟨Cv, hCv0, hCv⟩ := dec_adj X hCG hL ha hv

  have hform : ∀ q ∈ EE k r D.z,
      ⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ • beInt D X (X.σ (Matrix.of q.1) X.w) v q.2 =
        ⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ • ((⟪v, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1 * Matrix.of q.1) X.w⟫_ℂ *
          star (psiD D (Matrix.of q.2.2))) • ContinuousLinearMap.adjoint (D.π (Matrix.of q.2.1))) := by
    intro q hq
    obtain ⟨hy, hh, hn⟩ := hq
    have hs : Matrix.of q.2.2 * Matrix.of q.2.1 ∈ GV k r := hCG.mul_mem _ hn.1 _ hh.1
    have e1 : X.σ (Matrix.of q.2.2 * Matrix.of q.2.1) (X.σ (Matrix.of q.1) X.w) =
        X.σ (Matrix.of q.2.2 * Matrix.of q.2.1 * Matrix.of q.1) X.w := by
      rw [X.rep.1.2 _ hs _ hy]; rfl
    simp only [beInt, mc]
    rw [e1, pi_inv D hCW hh]
  have hcont : ContinuousOn (fun q : Mt k r × (Mt k r × Mt k r) =>
      ⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ • beInt D X (X.σ (Matrix.of q.1) X.w) v q.2) (EE k r D.z) := by
    refine ContinuousOn.congr ?_ hform
    exact (ContinuousOn.inner (𝕜 := ℂ) (cont_sig_fst X D.z X.w) continuousOn_const).smul
      (((ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (cont_sig_sy X D.z hCG X.w)).mul
        (cont_psi D).continuousOn).smul (cont_adj_pi D))
  have hmeas : AEStronglyMeasurable (fun q : Mt k r × (Mt k r × Mt k r) =>
      ⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ • beInt D X (X.σ (Matrix.of q.1) X.w) v q.2)
      (D.μG.prod (D.μW.prod D.μN)) := by
    have := hcont.aestronglyMeasurable (μ := D.μG.prod (D.μW.prod D.μN)) (EE_closed D.z hCG hCW hCN).measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (ae_EE D)] at this
  have hbd : ∀ᵐ q ∂(D.μG.prod (D.μW.prod D.μN)),
      ‖⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ • beInt D X (X.σ (Matrix.of q.1) X.w) v q.2‖ ≤
        Cu * Cv * KH k r ^ (X.a / 2) *
          (gN (Matrix.of q.1) ^ (-(X.a / 2)) * gN (Matrix.of q.2.2 * Matrix.of q.2.1) ^ (-(X.a / 2))) := by
    filter_upwards [ae_EE D] with q hq
    rw [hform q hq]
    obtain ⟨hy, hh, hn⟩ := hq
    have hs : Matrix.of q.2.2 * Matrix.of q.2.1 ∈ GV k r := hCG.mul_mem _ hn.1 _ hh.1
    have A1 : ‖⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ‖ ≤ Cu * gN (Matrix.of q.1) ^ (-X.a) := by
      rw [norm_inner_symm]; exact hCu _ hy
    have A2 : ‖⟪v, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1 * Matrix.of q.1) X.w⟫_ℂ‖ ≤
        Cv * gN (Matrix.of q.2.2 * Matrix.of q.2.1 * Matrix.of q.1) ^ (-X.a) :=
      hCv _ (hCG.mul_mem _ hs _ hy)
    have B := first_pointwise_bound hCG hL ha hs hy A1 A2 (norm_nonneg _) (norm_nonneg _) hCu0 hCv0
    have hT : ‖ContinuousLinearMap.adjoint (D.π (Matrix.of q.2.1))‖ ≤ 1 := by
      rw [LinearIsometryEquiv.norm_map]; exact opNorm_le_one_of_iso (D.π_unitary _ hh)
    have hψ : ‖star (psiD D (Matrix.of q.2.2))‖ ≤ 1 := by rw [norm_star]; exact norm_psi_le _ _ _
    rw [norm_smul, norm_smul, norm_mul]
    calc ‖⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ‖ * (‖⟪v, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1 * Matrix.of q.1) X.w⟫_ℂ‖ *
          ‖star (psiD D (Matrix.of q.2.2))‖ * ‖ContinuousLinearMap.adjoint (D.π (Matrix.of q.2.1))‖)
        ≤ ‖⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ‖ *
          (‖⟪v, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1 * Matrix.of q.1) X.w⟫_ℂ‖ * 1 * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hψ (norm_nonneg _)) hT
            (norm_nonneg _) (by positivity)) (norm_nonneg _)
      _ = ‖⟪X.σ (Matrix.of q.1) X.w, u⟫_ℂ‖ *
          ‖⟪v, X.σ (Matrix.of q.2.2 * Matrix.of q.2.1 * Matrix.of q.1) X.w⟫_ℂ‖ := by ring
      _ ≤ _ := B
  exact ((hIG.mul_prod hIS).const_mul (Cu * Cv * KH k r ^ (X.a / 2))).mono' hmeas hbd

theorem reproducing_fst (D : RealPlaceData k r Wp Wp) (X : SigData k r)
    (hCG : IsClosedSubgroup (GV k r)) (hCW : IsClosedSubgroup (UWset k r D.z)) (hCN : IsClosedSubgroup (Nset k r))
    (hL : ∀ g ∈ GV k r, 1 ≤ gN g) (ha : 0 ≤ X.a)
    (hIG : Integrable (fun y : Mt k r => gN (Matrix.of y) ^ (-(X.a / 2))) D.μG)
    (hIS : Integrable (fun p : Mt k r × Mt k r => gN (Matrix.of p.2 * Matrix.of p.1) ^ (-(X.a / 2)))
      (D.μW.prod D.μN))
    {d : ℝ} (hd : IsFdegG D X d) {u v : X.Hs} (hu : u ∈ Vfl X) (hv : v ∈ Vfl X) :
    beOp D X u v = (d : ℂ) •
      ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have : IsFiniteMeasureOnCompacts D.μG := ⟨fun _ hK => D.haarG.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μW := ⟨fun _ hK => D.haarW.finite_compact _ hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun _ hK => D.haarN.finite_compact _ hK⟩
  have hint := first_joint_integrable D X hCG hCW hCN hL ha hIG hIS hu hv
  have hpt : ∀ p : Mt k r × Mt k r,
      ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beInt D X (X.σ (Matrix.of y) X.w) v p ∂D.μG =
        ((d : ℂ)⁻¹) • beInt D X u v p := by
    intro p
    simp only [beInt, smul_smul]
    rw [integral_smul_const]
    congr 1
    have e : ∀ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
        (mc X (X.σ (Matrix.of y) X.w) v (Matrix.of p.2 * Matrix.of p.1) * star (psiD D (Matrix.of p.2))) =
        ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ *
          ⟪ContinuousLinearMap.adjoint (X.σ (Matrix.of p.2 * Matrix.of p.1)) v, X.σ (Matrix.of y) X.w⟫_ℂ *
          star (psiD D (Matrix.of p.2)) := by
      intro y; rw [mc, ContinuousLinearMap.adjoint_inner_left]; ring
    simp_rw [e]
    rw [integral_mul_const, schur_pt D X hd, ContinuousLinearMap.adjoint_inner_left, mc]
    ring
  have hsw := swap_smul D.μG (D.μW.prod D.μN) (fun y : Mt k r => ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ)
    (fun (y : Mt k r) (p : Mt k r × Mt k r) => beInt D X (X.σ (Matrix.of y) X.w) v p) hint
  have key : ∫ y : Mt k r, ⟪X.σ (Matrix.of y) X.w, u⟫_ℂ • beOp D X (X.σ (Matrix.of y) X.w) v ∂D.μG =
      ((d : ℂ)⁻¹) • beOp D X u v := by
    simp only [beOp]
    rw [hsw]
    simp_rw [hpt]
    rw [integral_smul]
  have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.1.ne'
  rw [key, smul_smul, mul_inv_cancel₀ hd0, one_smul]

end reproducing_fst

end ReciprocityTheory.ChartRestriction.DS.Mult1.ReproducingFormula
