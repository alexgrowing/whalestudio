import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HpkMulVecMulVec

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem gv_closed : IsClosed (GV k r) := by
  unfold GV UH Hpk
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const

theorem cont_of : Continuous (fun g : Mt k r => (Matrix.of g : Mat k r)) := by
  exact continuous_id

theorem gv_measurable : @MeasurableSet (Mt k r) _ (GV k r) := by
  exact (show IsClosed (X := Mt k r) (GV k r) from gv_closed).measurableSet

theorem gN_cont : Continuous (fun g : Mt k r => gN (Matrix.of g : Mat k r)) := by
  unfold gN
  first
  | fun_prop
  | continuity

theorem ae_G (D : RealPlaceData k r Wp Wp) : ∀ᵐ x ∂D.μG, Matrix.of x ∈ GV k r := by
  exact ae_iff.mpr D.haarG.conc

theorem aesm_G {E : Type} [NormedAddCommGroup E] (D : RealPlaceData k r Wp Wp) {f : Mt k r → E}
    (hf : ContinuousOn f (GV k r : Set (Mt k r))) : AEStronglyMeasurable f D.μG := by
  have hr : D.μG.restrict (GV k r : Set (Mt k r)) = D.μG := Measure.restrict_eq_self_of_ae_mem (ae_G D)
  rw [← hr]
  exact hf.aestronglyMeasurable gv_measurable

theorem test_cont {φ : Mat k r → ℂ} (hφ : IsTestG φ) : ContinuousOn φ (GV k r) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg₀U, hf', hφf⟩ := hφ.1 g₀ hg₀
  have hc : ContinuousAt f' g₀ := hf'.continuousOn.continuousAt (hU.mem_nhds hg₀U)
  refine hc.continuousWithinAt.congr_of_eventuallyEq ?_ (hφf g₀ hg₀U hg₀)
  filter_upwards [inter_mem_nhdsWithin (GV k r) (hU.mem_nhds hg₀U)] with g hg using hφf g hg.2 hg.1

theorem test_bound {φ : Mat k r → ℂ} (hφ : IsTestG φ) :
    ∃ K : Set (Mat k r), IsCompact K ∧ ∃ M : ℝ, 0 ≤ M ∧ ∃ R : ℝ, 0 ≤ R ∧ (∀ x ∈ K, gN x ≤ R) ∧
      ∀ x ∈ GV k r, ‖φ x‖ ≤ M * K.indicator 1 x := by
  obtain ⟨K, hK, hK0⟩ := hφ.2
  have hKc : IsCompact (K ∩ GV k r) := hK.inter_right gv_closed
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn ((test_cont hφ).mono Set.inter_subset_right)
  have hgN : ContinuousOn (fun x : Mat k r => gN x) (K ∩ GV k r) :=
    (show Continuous (fun x : Mat k r => gN x) from gN_cont).continuousOn
  obtain ⟨R, hR⟩ := hKc.exists_bound_of_continuousOn hgN
  refine ⟨K ∩ GV k r, hKc, max M 0, le_max_right _ _, max R 0, le_max_right _ _, fun x hx => ?_, fun x hx => ?_⟩
  · have h1 := hR x hx
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans (h1.trans (le_max_left _ _))
  · by_cases hxK : x ∈ K
    · have hx' : x ∈ K ∩ GV k r := ⟨hxK, hx⟩
      rw [Set.indicator_of_mem hx', Pi.one_apply, mul_one]
      exact (hM x hx').trans (le_max_left _ _)
    · rw [hK0 x hx hxK]
      simp [Set.indicator_apply, hxK]

theorem int_ind (D : RealPlaceData k r Wp Wp) {K : Set (Mat k r)} (hK : IsCompact K) :
    Integrable (fun x : Mt k r => K.indicator (1 : Mat k r → ℝ) (Matrix.of x)) D.μG := by
  have hm : @MeasurableSet (Mt k r) _ K := (show IsClosed (X := Mt k r) K from hK.isClosed).measurableSet
  have hfin : D.μG K < ⊤ := D.haarG.finite_compact K hK
  have he : (fun x : Mt k r => K.indicator (1 : Mat k r → ℝ) (Matrix.of x)) = @Set.indicator (Mt k r) ℝ _ K 1 := rfl
  rw [he]
  refine (integrable_indicator_iff hm).2 ?_
  first
  | exact integrableOn_const.2 (Or.inr hfin)
  | exact integrableOn_const hfin.ne
  | exact integrableOn_const (C := (1 : ℝ)) hfin.ne

theorem gN_integrable (D : RealPlaceData k r Wp Wp) (hGN : GNIntSharp) {A : ℝ} (hA : AB k r ≤ A) :
    Integrable (fun y : Mt k r => gN (Matrix.of y) ^ (-A)) D.μG := by
  unfold GNIntSharp AB at *
  refine ⟨(gN_cont.measurable.pow_const (-A)).aestronglyMeasurable, ?_⟩
  refine (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => ?_)).2 (hGN k r D.μG A D.haarG hA)
  show 0 ≤ gN (Matrix.of y) ^ (-A)
  exact Real.rpow_nonneg (by unfold gN; exact Real.sqrt_nonneg _) _

theorem orbit_bound (X : SigData k r) (ha0 : 0 ≤ X.a) {x y : Mat k r} (hx : x ∈ GV k r) (hy : y ∈ GV k r) :
    ‖⟪X.σ y X.w, X.σ x X.w⟫_ℂ‖ ≤ X.Cw * ((KH k r ^ 2 * gN x) ^ X.a * gN y ^ (-X.a)) := by
  have hyx : y⁻¹ * x ∈ GV k r := gv_mul (gv_inv_mem hy) hx
  rw [sig_inner X hy, ← ContinuousLinearMap.comp_apply, ← sig_mul X (gv_inv_mem hy) hx]
  have h1 : gN y ≤ (KH k r ^ 2 * gN x) * gN (y⁻¹ * x) := by
    calc gN y ≤ KH k r * gN y⁻¹ := gN_le_inv hy
      _ = KH k r * gN (y⁻¹ * x * x⁻¹) := by rw [Matrix.mul_assoc, gv_mul_inv hx, Matrix.mul_one]
      _ ≤ KH k r * (gN (y⁻¹ * x) * gN x⁻¹) := mul_le_mul_of_nonneg_left (gN_mul_le _ _) KH_pos.le
      _ ≤ KH k r * (gN (y⁻¹ * x) * (KH k r * gN x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (gN_inv_le hx) (gN_nonneg _)) KH_pos.le
      _ = _ := by unfold KH; ring
  calc ‖⟪X.w, X.σ (y⁻¹ * x) X.w⟫_ℂ‖ ≤ X.Cw * gN (y⁻¹ * x) ^ (-X.a) := X.dec _ hyx
    _ ≤ _ := mul_le_mul_of_nonneg_left
        (rpow_neg_le (gN_pos hy) (mul_pos (pow_pos KH_pos 2) (gN_pos hx)) ha0 h1)
        (C_nonneg X.dec)

theorem sig_aesm (D : RealPlaceData k r Wp Wp) (X : SigData k r) (v : X.Hs) :
    AEStronglyMeasurable (fun y : Mt k r => X.σ (Matrix.of y) v) D.μG :=
  aesm_G D (X.rep.2.2 v)

theorem sigInt_integrable (D : RealPlaceData k r Wp Wp) (X : SigData k r) {φ : Mat k r → ℂ} (hφ : IsTestG φ) :
    Integrable (fun g : Mt k r => φ (Matrix.of g) • X.σ (Matrix.of g) X.w) D.μG := by
  obtain ⟨K, hK, M, hM0, R, hR0, hKR, hb⟩ := test_bound hφ
  refine Integrable.mono' ((int_ind D hK).const_mul M) ?_ ?_
  · exact aesm_G D ((test_cont hφ).smul (X.rep.2.2 X.w))
  · filter_upwards [ae_G D] with g hg
    rw [norm_smul, X.rep.2.1 _ hg, X.w_norm, mul_one]
    exact hb _ hg

theorem dd_mem (D : RealPlaceData k r Wp Wp) (X : SigData k r) (ha0 : 0 ≤ X.a) {φ : Mat k r → ℂ}
    (hφ : IsTestG φ) : sigInt D X φ X.w ∈ Vfl X := by
  obtain ⟨K, hK, M, hM0, R, hR0, hRK, hM⟩ := test_bound hφ
  have hint := sigInt_integrable D X hφ
  have hCw := C_nonneg X.dec
  refine ⟨M * X.Cw * (KH k r * R) ^ X.a * ∫ g : Mt k r, K.indicator (1 : Mat k r → ℝ) (Matrix.of g) ∂D.μG,
    fun x hx => ?_⟩
  have e1 : mc X (sigInt D X φ X.w) X.w x =
      ∫ g : Mt k r, ⟪X.w, X.σ x (φ (Matrix.of g) • X.σ (Matrix.of g) X.w)⟫_ℂ ∂D.μG := by
    unfold mc sigInt
    rw [← (X.σ x).integral_comp_comm hint, integral_inner ((X.σ x).integrable_comp hint)]
  rw [e1]
  have hb : ∀ᵐ g ∂D.μG, ‖⟪X.w, X.σ x (φ (Matrix.of g) • X.σ (Matrix.of g) X.w)⟫_ℂ‖ ≤
      (M * X.Cw * (KH k r * R) ^ X.a * gN x ^ (-X.a)) * K.indicator (1 : Mat k r → ℝ) (Matrix.of g) := by
    filter_upwards [ae_G D] with g hg
    rw [map_smul, inner_smul_right, norm_mul, ← ContinuousLinearMap.comp_apply, ← sig_mul X hx hg]
    by_cases hgK : Matrix.of g ∈ K
    · have hi : K.indicator (1 : Mat k r → ℝ) (Matrix.of g) = 1 := by simp [Set.indicator, hgK]
      have hφg : ‖φ (Matrix.of g)‖ ≤ M := by simpa [hi] using hM _ hg
      have h1 : gN x ≤ (KH k r * R) * gN (x * Matrix.of g) := by
        calc gN x = gN (x * Matrix.of g * (Matrix.of g)⁻¹) := by
              rw [Matrix.mul_assoc, gv_mul_inv hg, Matrix.mul_one]
          _ ≤ gN (x * Matrix.of g) * gN (Matrix.of g)⁻¹ := gN_mul_le _ _
          _ ≤ gN (x * Matrix.of g) * (KH k r * R) := by
              refine mul_le_mul_of_nonneg_left ((gN_inv_le hg).trans ?_) (gN_nonneg _)
              exact mul_le_mul_of_nonneg_left (hRK _ hgK) KH_pos.le
          _ = _ := mul_comm _ _
      have h2 : ‖⟪X.w, X.σ (x * Matrix.of g) X.w⟫_ℂ‖ ≤ X.Cw * ((KH k r * R) ^ X.a * gN x ^ (-X.a)) :=
        (X.dec _ (gv_mul hx hg)).trans (mul_le_mul_of_nonneg_left
          (rpow_neg_le (gN_pos hx) (mul_pos KH_pos ((gN_pos hg).trans_le (hRK _ hgK))) ha0 h1) hCw)
      rw [hi, mul_one]
      calc ‖φ (Matrix.of g)‖ * ‖⟪X.w, X.σ (x * Matrix.of g) X.w⟫_ℂ‖
          ≤ M * (X.Cw * ((KH k r * R) ^ X.a * gN x ^ (-X.a))) :=
            mul_le_mul hφg h2 (norm_nonneg _) hM0
        _ = _ := by ring
    · have hi : K.indicator (1 : Mat k r → ℝ) (Matrix.of g) = 0 := by simp [Set.indicator, hgK]
      have hφg : φ (Matrix.of g) = 0 := by
        have := hM _ hg; rw [hi, mul_zero] at this; exact norm_le_zero_iff.1 this
      rw [hi, hφg]; simp
  calc ‖∫ g : Mt k r, ⟪X.w, X.σ x (φ (Matrix.of g) • X.σ (Matrix.of g) X.w)⟫_ℂ ∂D.μG‖
      ≤ ∫ g : Mt k r, (M * X.Cw * (KH k r * R) ^ X.a * gN x ^ (-X.a)) *
          K.indicator (1 : Mat k r → ℝ) (Matrix.of g) ∂D.μG :=
        norm_integral_le_of_norm_le ((int_ind D hK).const_mul _) hb
    _ = _ := by rw [integral_const_mul]; ring

theorem test_of_contDiff {g : Mt k r → ℝ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgc : HasCompactSupport g) :
    IsTestG (fun x : Mat k r => ((g x : ℝ) : ℂ)) := by
  unfold IsTestG CkOn
  refine ⟨fun g₀ _ => ⟨Set.univ, fun x => ((g x : ℝ) : ℂ), isOpen_univ, Set.mem_univ _, ?_, fun _ _ _ => rfl⟩,
    tsupport g, hgc, fun x _ hx => ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp hg).contDiffOn
  · have h0 : g x = 0 := by
      first
      | exact image_eq_zero_of_notMem_tsupport hx
      | exact image_eq_zero_of_nmem_tsupport hx
    simp [h0]

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

theorem mulVec_cont (v : Fin (2 * r + k + 1) → ℂ) : Continuous (fun g : Mat k r => g *ᵥ v) := by
  fun_prop

theorem uw_closed (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (UWset k r z) := by
  unfold UWset
  simp only [Set.setOf_and, Set.setOf_forall, Set.setOf_mem_eq]
  have hc : ∀ v : Fin (2 * r + k + 1) → ℂ, IsClosed {g : Mat k r | g *ᵥ v = v} :=
    fun v => isClosed_eq (mulVec_cont v) continuous_const
  exact gv_closed.inter ((isClosed_iInter fun a => (hc _).inter (hc _)).inter (hc z))

theorem n_closed : IsClosed (Nset k r) := by
  unfold Nset
  have he : ∀ (i j : Fin (2 * r + k + 1)) (c : ℂ), IsClosed {g : Mat k r | g i j = c} :=
    fun i j c => isClosed_eq (continuous_id.matrix_elem i j) continuous_const
  simp only [Set.setOf_and, Set.setOf_forall, Set.setOf_mem_eq]
  exact gv_closed.inter ((isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ => he _ _ _).inter
    (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => he _ _ _))

theorem psi_cont (z : Fin (2 * r + k + 1) → ℂ) : Continuous (fun m : Mat k r => psi k r z cStd m) := by
  unfold psi ell
  have hs : Continuous fun m : Mat k r => ∑ a : Fin r, (if h : (a : ℕ) + 1 < r then m (eI k r a) (eI k r ⟨(a : ℕ) + 1, h⟩)
      else (m *ᵥ z) (eI k r a)) := by
    refine continuous_finset_sum _ fun a _ => ?_
    by_cases h : (a : ℕ) + 1 < r
    · simp only [dif_pos h]
      exact continuous_id.matrix_elem _ _
    · simp only [dif_neg h]
      show Continuous ((fun v : Fin (2 * r + k + 1) → ℂ => v (eI k r a)) ∘ fun m : Mat k r => m *ᵥ z)
      exact (continuous_apply (eI k r a)).comp (mulVec_cont z)
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.mul hs))))

theorem be_aesm (D : RealPlaceData k r Wp Wp) (X : SigData k r) (v : X.Hs) :
    AEStronglyMeasurable (fun y : Mt k r => beOp D X (X.σ (Matrix.of y) X.w) v) D.μG := by
  have sW := (⟨fun K hK => D.haarW.finite_compact K hK⟩ : IsFiniteMeasureOnCompacts D.μW)
  have sN := (⟨fun K hK => D.haarN.finite_compact K hK⟩ : IsFiniteMeasureOnCompacts D.μN)
  have sG := (⟨fun K hK => D.haarG.finite_compact K hK⟩ : IsFiniteMeasureOnCompacts D.μG)
  set S3 : Set (Mt k r × (Mt k r × Mt k r)) := {z | Matrix.of z.1 ∈ GV k r ∧
    Matrix.of z.2.1 ∈ UWset k r D.z ∧ Matrix.of z.2.2 ∈ Nset k r} with hS3
  have hS3c : IsClosed S3 :=
    IsClosed.inter (gv_closed.preimage (cont_of.comp continuous_fst))
      (IsClosed.inter ((uw_closed D.z).preimage (cont_of.comp (continuous_fst.comp continuous_snd)))
        (n_closed.preimage (cont_of.comp (continuous_snd.comp continuous_snd))))
  have hae : ∀ᵐ z ∂(D.μG.prod (D.μW.prod D.μN)), z ∈ S3 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_G D),
      Measure.quasiMeasurePreserving_snd.ae (ae_UN D)] with z h1 h2
    exact ⟨h1, h2.1, h2.2⟩
  set G : Mt k r × (Mt k r × Mt k r) → (Wp →L[ℂ] Wp) := fun z =>
    (⟪v, X.σ (Matrix.of z.2.2 * Matrix.of z.2.1 * Matrix.of z.1) X.w⟫_ℂ *
      star (psiD D (Matrix.of z.2.2))) • D.π (Hpk k r * (Matrix.of z.2.1)ᴴ * Hpk k r) with hG
  have hGc : ContinuousOn G S3 := by
    have hm : Continuous (fun z : Mt k r × (Mt k r × Mt k r) =>
        (Matrix.of z.2.2 * Matrix.of z.2.1 * Matrix.of z.1 : Mat k r)) :=
      ((cont_of.comp (continuous_snd.comp continuous_snd)).matrix_mul
        (cont_of.comp (continuous_fst.comp continuous_snd))).matrix_mul (cont_of.comp continuous_fst)
    have c1 : ContinuousOn (fun z : Mt k r × (Mt k r × Mt k r) =>
        X.σ (Matrix.of z.2.2 * Matrix.of z.2.1 * Matrix.of z.1) X.w) S3 :=
      (X.rep.2.2 X.w).comp hm.continuousOn fun z hz => gv_mul (gv_mul (n_gv hz.2.2) (uw_gv hz.2.1)) hz.1
    have c2 : Continuous (fun z : Mt k r × (Mt k r × Mt k r) => star (psiD D (Matrix.of z.2.2))) :=
      continuous_star.comp ((psi_cont D.z).comp (cont_of.comp (continuous_snd.comp continuous_snd)))
    have hi : Continuous (fun z : Mt k r × (Mt k r × Mt k r) => Hpk k r * (Matrix.of z.2.1 : Mat k r)ᴴ * Hpk k r) :=
      (continuous_const.matrix_mul (cont_of.comp (continuous_fst.comp continuous_snd)).matrix_conjTranspose).matrix_mul
        continuous_const
    have c3 : ContinuousOn (fun z : Mt k r × (Mt k r × Mt k r) => D.π (Hpk k r * (Matrix.of z.2.1)ᴴ * Hpk k r)) S3 :=
      D.π_cont.comp hi.continuousOn fun z hz => by
        have := uw_inv_mem hz.2.1
        rwa [gv_inv_eq (uw_gv hz.2.1)] at this
    exact ((continuousOn_const.inner c1).mul c2.continuousOn).smul c3
  have hGm : AEStronglyMeasurable G (D.μG.prod (D.μW.prod D.μN)) := by
    have h := ContinuousOn.aestronglyMeasurable (μ := D.μG.prod (D.μW.prod D.μN)) hGc hS3c.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem hae] at h
  have hFm : AEStronglyMeasurable (fun z : Mt k r × (Mt k r × Mt k r) =>
      beInt D X (X.σ (Matrix.of z.1) X.w) v z.2) (D.μG.prod (D.μW.prod D.μN)) := by
    refine hGm.congr ?_
    filter_upwards [hae] with z hz
    have hs : Matrix.of z.2.2 * Matrix.of z.2.1 ∈ GV k r := gv_mul (n_gv hz.2.2) (uw_gv hz.2.1)
    simp only [hG, beInt, mc]
    rw [sig_mul X hs hz.1, ContinuousLinearMap.comp_apply, gv_inv_eq (uw_gv hz.2.1)]
  exact hFm.integral_prod_right'

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH
