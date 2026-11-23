import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfI
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCurry
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralFlagDensityFibreBoundedDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorFlagDensityGlueLowerUnitriangular
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorBlockDecomposition
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralPiFibreMeasurePreserving
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingFlagFibreChartCoordinates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAndFderivMoebI
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsMixedProj

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open Matrix Formalism.DegreeFormula Formalism.MJ GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ENNReal ComplexOrder

namespace GlobalTheory.KernelIntegral

theorem lminor_glue {r p q : ℕ} {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) {A : Matrix (Fin r) (Fin r) ℂ}
    (hA : reindex e e A = -Formalism.UG.Jpq p q) (w : (Fin p × Fin q → ℂ) × (Low q → ℂ) × (Low p → ℂ))
    (hw : toMat w.1 ∈ hcDom p q) (i : Fin (r + 1)) (hi : (i : ℕ) = q) :
    lminor ((uni (glue e w))ᴴ * A * uni (glue e w)) i = (hQ (toMat w.1)).det := by
  set H := (uni (glue e w))ᴴ * A * uni (glue e w) with hH
  have hR := reindex_conj_glue he A w
  have hS : shear (reindex e e A) (toMat w.1) =
      fromBlocks (-1) (-(toMat w.1)) (-(toMat w.1)ᴴ) (hQ (toMat w.1)) := by
    rw [hA]; exact GlobalTheory.FlagFibreInt.shear_neg_J _
  have h22 : (reindex e e H).toBlocks₂₂ = (uni w.2.1)ᴴ * hQ (toMat w.1) * uni w.2.1 := by
    rw [hR, blockDiag_conj, toBlocks_fromBlocks₂₂, hS, toBlocks_fromBlocks₂₂]
  have hd : (reindex e e H).toBlocks₂₂.det = (hQ (toMat w.1)).det := by
    rw [h22, det_mul, det_mul, det_conjTranspose, det_uni]; simp
  have hpd : (hQ (toMat w.1)).PosDef := hw
  have hu : IsUnit (reindex e e H).toBlocks₂₂.det := by
    rw [hd]; exact hpd.det_pos.ne'.isUnit
  rw [(GlobalTheory.FlagFibre.lminor_block r p q e he H hu).2 i 0 (by simp [hi]), hd]
  simp [lminor]

theorem lminor_base {r p q : ℕ} {e : Fin r ≃ Fin p ⊕ Fin q} (he : IsBlockSL2Embedding e) {A : Matrix (Fin r) (Fin r) ℂ}
    (hA : reindex e e A = -Formalism.UG.Jpq p q) (y : Low r → ℂ) (hy : toMat (base e y) ∈ hcDom p q)
    (i : Fin (r + 1)) (hi : (i : ℕ) = q) :
    lminor ((uni y)ᴴ * A * uni y) i = (hQ (toMat (base e y))).det := by
  obtain ⟨w, rfl⟩ := glue_surjective he y
  rw [base_glue he] at hy ⊢
  exact lminor_glue he hA w hy i hi

theorem measurableSet_hc (p q : ℕ) : MeasurableSet {v : Fin p × Fin q → ℂ | toMat v ∈ hcDom p q} := by
  have h : {v : Fin p × Fin q → ℂ | toMat v ∈ hcDom p q} =
      (fun v : Fin p × Fin q → ℂ => fun x : Unit × Fin p × Fin q => v x.2) ⁻¹' DomFlat Unit p q := by
    ext v
    exact ⟨fun h _ => h, fun h => h ()⟩
  rw [h]
  exact (GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat.preimage (by fun_prop)).measurableSet

theorem det_hQ_pos {p q : ℕ} {Z : Matrix (Fin p) (Fin q) ℂ} (hZ : Z ∈ hcDom p q) :
    0 < (hQ Z).det.re ∧ (hQ Z).det.re ≤ 1 := by
  have hpd : (hQ Z).PosDef := hZ
  refine ⟨(ExhA.det_re_pos_im hpd).1, ?_⟩
  have h : hQ Z = 1 - Zᴴ * Zᴴᴴ := by rw [conjTranspose_conjTranspose]; rfl
  rw [h] at hpd ⊢
  exact ExhA.det_re_le_one hpd

theorem norm_le_one_of_hc {p q : ℕ} {v : Fin p × Fin q → ℂ} (hv : toMat v ∈ hcDom p q) (x : Fin p × Fin q) :
    ‖v x‖ ≤ 1 := by
  have hpd : (1 - (toMat v)ᴴ * toMat v).PosDef := hv
  have h := hpd.diag_pos (i := x.2)
  have e : (1 - (toMat v)ᴴ * toMat v : Matrix (Fin q) (Fin q) ℂ) x.2 x.2 = ((1 - ∑ a, ‖v (a, x.2)‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply, conjTranspose_apply, toMat, Matrix.of_apply,
      RCLike.star_def, Complex.conj_mul']
    push_cast; ring
  rw [e, Complex.zero_lt_real] at h
  have h2 : ‖v x‖ ^ 2 ≤ ∑ a, ‖v (a, x.2)‖ ^ 2 :=
    Finset.single_le_sum (f := fun a => ‖v (a, x.2)‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ x.1)
  nlinarith [norm_nonneg (v x)]

end GlobalTheory.KernelIntegral

namespace GlobalTheory.KernelIntegral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

noncomputable def wt (p q : ℕ) (bb : ℝ) (v : Fin p × Fin q → ℂ) : ℝ≥0∞ :=
  {v : Fin p × Fin q → ℂ | toMat v ∈ hcDom p q}.indicator (fun v => ENNReal.ofReal ((hQ (toMat v)).det.re ^ bb)) v

theorem measurable_wt (p q : ℕ) (bb : ℝ) : Measurable (wt p q bb) := by
  refine Measurable.indicator ?_ (measurableSet_hc p q)
  have hc : Continuous fun v : Fin p × Fin q → ℂ => (hQ (toMat v)).det := by
    unfold hQ
    exact (continuous_const.sub (continuous_toMat.matrix_conjTranspose.matrix_mul continuous_toMat)).matrix_det
  exact ((Complex.continuous_re.comp hc).measurable.pow_const bb).ennreal_ofReal

theorem sgn_reindex (X : Data E r) {j : ℕ} (hj : j ≤ r) (hp : X.p0 = r - j) :
    reindex (idx hj) (idx hj) (sgnMat r X.p0) = -Formalism.UG.Jpq j (r - j) := by
  rw [sgnMat, hp]
  exact reindex_sgn hj

theorem dens_kaF_eq (X : Data E r) {j : ℕ} (hj : j ≤ r) (hp : X.p0 = r - j) (bb : ℝ) {z : V (nd X)}
    (hz : z ∈ OmF X (x0F X)) :
    ENNReal.ofReal (densF X (x0F X) z) * ENNReal.ofReal (kaF X (x0F X) bb z) =
      (∏ t, wt j (r - j) bb (base (idx hj) (coords X (Equiv.refl X.Ψ) z t))) *
        ∏ t, ENNReal.ofReal (dens (sgnMat r X.p0) (coords X (Equiv.refl X.Ψ) z t)) := by
  set κ := Equiv.refl X.Ψ
  have hx : cpt X (x0F X) z ∈ X.dom := hz
  have hD := domPt_mem X hj κ hp hx
  have hmat : ∀ t, toMat (base (idx hj) (coords X κ z t)) = domPt X hj κ (cpt X (x0F X) z) t := fun t => by
    ext a b
    exact (proj_eq X hj κ z t (a, b)).symm
  have hc : ∀ t, toMat (base (idx hj) (coords X κ z t)) ∈ hcDom j (r - j) := fun t => by
    rw [hmat t]; exact hD t
  have hmin : ∀ t : X.Ψ, dmin X.Gm (cpt X (x0F X) z) t ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ =
      (hQ (toMat (base (idx hj) (coords X κ z t)))).det := fun t =>
    (dmin_cpt X κ z t _).trans (lminor_base (isBlockOrderedSumEquiv_trueIndex hj) (sgn_reindex X hj hp) _ (hc t) _ hp)
  have hk : kaF X (x0F X) bb z = ∏ t, (hQ (toMat (base (idx hj) (coords X κ z t)))).det.re ^ bb := by
    simp only [kaF, rhF, hmin]
    rw [neg_mul_neg, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun t _ => ?_
    have hpd : (hQ (toMat (base (idx hj) (coords X κ z t)))).PosDef := hc t
    rw [ExF.norm_of_pos hpd.det_pos, Real.rpow_def_of_pos (det_hQ_pos (hc t)).1, mul_comm]
  rw [densF_eq X κ, hk, ENNReal.ofReal_prod_of_nonneg fun _ _ => dens_nonneg _ _,
    ENNReal.ofReal_prod_of_nonneg fun t _ => Real.rpow_nonneg (det_hQ_pos (hc t)).1.le _, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [wt, Set.indicator_of_mem (show base (idx hj) (coords X κ z t) ∈
    {v : Fin j × Fin (r - j) → ℂ | toMat v ∈ hcDom j (r - j)} from hc t)]

end GlobalTheory.KernelIntegral

namespace GlobalTheory.KernelIntegral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def cube (p q : ℕ) : Set (Fin p × Fin q → ℂ) := Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) 1

theorem fibre_bound (X : Data E r) {j : ℕ} (hj : j ≤ r) (hp : X.p0 = r - j) {bb : ℝ} (hbb : (r : ℝ) ≤ bb)
    (v : Fin j × Fin (r - j) → ℂ) :
    wt j (r - j) bb v * ∫⁻ b : (Low (r - j) → ℂ) × (Low j → ℂ), ENNReal.ofReal (dens (sgnMat r X.p0) (glue (idx hj) (v, b)))
      ≤ ENNReal.ofReal (1 / (flagConst j * flagConst (r - j))) * (cube j (r - j)).indicator 1 v := by
  by_cases hv : toMat v ∈ hcDom j (r - j)
  · have hc : v ∈ cube j (r - j) := fun x _ => by
      rw [Metric.mem_closedBall, dist_zero_right]; exact norm_le_one_of_hc hv x
    rw [wt, Set.indicator_of_mem (show v ∈ {v : Fin j × Fin (r - j) → ℂ | toMat v ∈ hcDom j (r - j)} from hv),
      Set.indicator_of_mem hc, Pi.one_apply, mul_one,
      GlobalTheory.FlagFibreInt.lintegral_dens_glue r j (r - j) (idx hj) (isBlockOrderedSumEquiv_trueIndex hj) _ (sgn_reindex X hj hp) v hv,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (det_hQ_pos hv).1.le _)]
    refine ENNReal.ofReal_le_ofReal ?_
    obtain ⟨h0, h1⟩ := det_hQ_pos hv
    have hc0 : 0 < flagConst j * flagConst (r - j) := mul_pos (flagConst_pos _) (flagConst_pos _)
    set d := (hQ (toMat v)).det.re
    have hN : (((j + (r - j) : ℕ) : ℤ) : ℝ) = r := by
      rw [Nat.add_sub_cancel' hj]; simp
    have e : d ^ bb * d ^ (-((j + (r - j) : ℕ) : ℤ)) = d ^ (bb - r) := by
      rw [← Real.rpow_intCast, Int.cast_neg, hN, ← Real.rpow_add h0, sub_eq_add_neg]
    rw [← mul_div_assoc, e, div_le_div_iff_of_pos_right hc0]
    exact Real.rpow_le_one h0.le h1 (by linarith)
  · rw [wt, Set.indicator_of_notMem (show v ∉ {v : Fin j × Fin (r - j) → ℂ | toMat v ∈ hcDom j (r - j)} from hv),
      zero_mul]
    exact zero_le'

theorem lintegral_x0F_le (X : Data E r) {j : ℕ} (hj : j ≤ r) (hp : X.p0 = r - j) {bb : ℝ} (hbb : (r : ℝ) ≤ bb) :
    ∫⁻ z, ENNReal.ofReal (kaF X (x0F X) bb z) ∂muF X (x0F X) ≤
      (ENNReal.ofReal (1 / (flagConst j * flagConst (r - j))) * volume (cube j (r - j))) ^ X.Ψ.card := by
  set κ := Equiv.refl X.Ψ
  set e := idx hj
  set D : (Low r → ℂ) → ℝ≥0∞ := fun y => ENNReal.ofReal (dens (sgnMat r X.p0) y) with hDdef
  set φ : (X.Ψ → Fin j × Fin (r - j) → ℂ) → ℝ≥0∞ := fun a => ∏ t, wt j (r - j) bb (a t) with hφdef
  set G : (X.Ψ → Low r → ℂ) → ℝ≥0∞ := fun c => φ (fun t => base e (c t)) * ∏ t, D (c t) with hGdef
  have hDm : Measurable D := (measurable_dens _).ennreal_ofReal
  have hφm : Measurable φ := Finset.measurable_prod _ fun t _ => (measurable_wt _ _ _).comp (measurable_pi_apply t)
  have hGm : Measurable G :=
    (hφm.comp (measurable_pi_lambda _ fun t => (measurable_base _).comp (measurable_pi_apply t))).mul
      (Finset.measurable_prod _ fun t _ => hDm.comp (measurable_pi_apply t))
  have hco := GlobalTheory.FlagFibre.measurePreserving_coords_sorted E r X X.Ψ κ
  have hdm : Measurable fun z => ENNReal.ofReal (densF X (x0F X) z) := by
    have e1 : (fun z => ENNReal.ofReal (densF X (x0F X) z)) = fun z => ∏ t, D (coords X κ z t) := by
      funext z
      rw [densF_eq X κ, ENNReal.ofReal_prod_of_nonneg fun _ _ => dens_nonneg _ _]
    rw [e1]
    exact Finset.measurable_prod _ fun t _ => hDm.comp ((measurable_pi_apply t).comp hco.measurable)
  have key := GlobalTheory.ProdFibre.lintegral_pi_fibre X.Ψ _ _ _ (glue e) (base e) D φ (GlobalTheory.T.measurePreserving_glueLowerUnitriangularBlocks _ _ _ _ (isBlockOrderedSumEquiv_trueIndex hj))
    (measurable_base _) (base_glue (isBlockOrderedSumEquiv_trueIndex hj)) hDm hφm
  set K := ENNReal.ofReal (1 / (flagConst j * flagConst (r - j)))
  have hcube : MeasurableSet (cube j (r - j)) :=
    MeasurableSet.univ_pi fun _ => Metric.isClosed_closedBall.measurableSet
  calc ∫⁻ z, ENNReal.ofReal (kaF X (x0F X) bb z) ∂muF X (x0F X)
      ≤ ∫⁻ z in OmF X (x0F X), ((fun z => ENNReal.ofReal (densF X (x0F X) z)) *
          fun z => ENNReal.ofReal (kaF X (x0F X) bb z)) z :=
        lintegral_withDensity_le_lintegral_mul _ hdm _
    _ ≤ ∫⁻ z in OmF X (x0F X), G (coords X κ z) :=
        setLIntegral_mono (hGm.comp hco.measurable) fun z hz => (dens_kaF_eq X hj hp bb hz).le
    _ ≤ ∫⁻ z, G (coords X κ z) := setLIntegral_le_lintegral _ _
    _ = ∫⁻ c, G c := hco.lintegral_comp hGm
    _ = ∫⁻ a, φ a * ∏ t, ∫⁻ b, D (glue e (a t, b)) := key
    _ ≤ ∫⁻ a, K ^ X.Ψ.card * (Set.univ.pi fun _ : X.Ψ => cube j (r - j)).indicator 1 a := by
        refine lintegral_mono fun a => ?_
        rw [hφdef]
        simp only
        rw [← Finset.prod_mul_distrib]
        calc ∏ t, wt j (r - j) bb (a t) * ∫⁻ b, D (glue e (a t, b))
            ≤ ∏ t : X.Ψ, K * (cube j (r - j)).indicator 1 (a t) :=
              Finset.prod_le_prod' fun t _ => fibre_bound X hj hp hbb (a t)
          _ = K ^ X.Ψ.card * (Set.univ.pi fun _ : X.Ψ => cube j (r - j)).indicator 1 a := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe]
              congr 1
              by_cases h : a ∈ Set.univ.pi fun _ : X.Ψ => cube j (r - j)
              · rw [Set.indicator_of_mem h, Pi.one_apply]
                exact Finset.prod_eq_one fun t _ => by
                  rw [Set.indicator_of_mem (h t (Set.mem_univ _)), Pi.one_apply]
              · rw [Set.indicator_of_notMem h]
                simp only [Set.mem_univ_pi, not_forall] at h
                obtain ⟨t, ht⟩ := h
                exact Finset.prod_eq_zero (Finset.mem_univ t) (by rw [Set.indicator_of_notMem ht])
    _ = (K * volume (cube j (r - j))) ^ X.Ψ.card := by
        rw [lintegral_const_mul _ (measurable_one.indicator (MeasurableSet.univ_pi fun _ => hcube)),
          lintegral_indicator_one (MeasurableSet.univ_pi fun _ => hcube), volume_pi_pi, Finset.prod_const,
          Finset.card_univ, Fintype.card_coe, mul_pow]

end GlobalTheory.KernelIntegral

namespace GlobalTheory.KernelIntegral

theorem one_div_flagConst_le (m : ℕ) : 1 / flagConst m ≤ Real.pi ^ (m * m) := by
  have hπ1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have h : (Real.pi ^ (m * m))⁻¹ ≤ flagConst m := by
    have e : (Real.pi ^ (m * m))⁻¹ = ∏ _i ∈ Finset.range m, (Real.pi ^ m)⁻¹ := by
      rw [Finset.prod_const, Finset.card_range, pow_mul, inv_pow]
    rw [e, flagConst]
    refine Finset.prod_le_prod (fun _ _ => by positivity) fun i hi => ?_
    have hi' : i ≤ m := (Finset.mem_range.1 hi).le
    have h1 : (1 : ℝ) ≤ i.factorial := by exact_mod_cast i.factorial_pos
    calc (Real.pi ^ m)⁻¹ ≤ (Real.pi ^ i)⁻¹ :=
          inv_anti₀ (pow_pos Real.pi_pos _) (pow_le_pow_right₀ hπ1 hi')
      _ = 1 / Real.pi ^ i := (one_div _).symm
      _ ≤ (i.factorial : ℝ) / Real.pi ^ i := div_le_div_of_nonneg_right h1 (pow_pos Real.pi_pos _).le
  calc 1 / flagConst m ≤ 1 / (Real.pi ^ (m * m))⁻¹ :=
        one_div_le_one_div_of_le (inv_pos.2 (pow_pos Real.pi_pos _)) h
    _ = Real.pi ^ (m * m) := by rw [one_div, inv_inv]

theorem bound_num (r j f : ℕ) (hj : j ≤ r) :
    (ENNReal.ofReal (1 / (flagConst j * flagConst (r - j))) * volume (cube j (r - j))) ^ f ≤
      ENNReal.ofReal (Real.exp (3 * ((f : ℝ) * r) ^ 8)) := by
  have hv : volume (cube j (r - j)) = ENNReal.ofReal (Real.pi ^ (j * (r - j))) := by
    rw [cube, volume_pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, Complex.volume_closedBall, ENNReal.ofReal_one, one_pow, one_mul,
      ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi, ENNReal.ofReal_pow Real.pi_pos.le]
  have hc0 : 0 < flagConst j * flagConst (r - j) := mul_pos (flagConst_pos _) (flagConst_pos _)
  rw [hv, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hπ1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hπe : Real.pi ≤ Real.exp 3 := by linarith [Real.pi_le_four, Real.add_one_le_exp 3]
  obtain ⟨k, rfl⟩ : ∃ k, r = j + k := ⟨r - j, (Nat.add_sub_cancel' hj).symm⟩
  rw [Nat.add_sub_cancel_left]
  have h1 : 1 / (flagConst j * flagConst k) * Real.pi ^ (j * k) ≤ Real.pi ^ ((j + k) * (j + k)) :=
    calc 1 / (flagConst j * flagConst k) * Real.pi ^ (j * k)
        = (1 / flagConst j) * (1 / flagConst k) * Real.pi ^ (j * k) := by rw [one_div_mul_one_div]
      _ ≤ Real.pi ^ (j * j) * Real.pi ^ (k * k) * Real.pi ^ (j * k) := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_pos Real.pi_pos _).le
          exact mul_le_mul (one_div_flagConst_le j) (one_div_flagConst_le k)
            (one_div_pos.2 (flagConst_pos k)).le (pow_pos Real.pi_pos _).le
      _ = Real.pi ^ (j * j + k * k + j * k) := by rw [pow_add, pow_add]
      _ ≤ Real.pi ^ ((j + k) * (j + k)) := pow_le_pow_right₀ hπ1 (by nlinarith)
  have hn : ((j + k) * (j + k) * f : ℕ) ≤ (f * (j + k)) ^ 8 := by
    rcases Nat.eq_zero_or_pos (f * (j + k)) with h | h
    · rcases Nat.mul_eq_zero.1 h with h' | h' <;> simp [h']
    · calc (j + k) * (j + k) * f ≤ (f * (j + k)) ^ 2 := by
            have hf : 1 ≤ f := Nat.pos_of_ne_zero fun h0 => by simp [h0] at h
            nlinarith
        _ ≤ (f * (j + k)) ^ 8 := Nat.pow_le_pow_right h (by norm_num)
  calc (1 / (flagConst j * flagConst k) * Real.pi ^ (j * k)) ^ f
      ≤ (Real.pi ^ ((j + k) * (j + k))) ^ f := pow_le_pow_left₀
        (mul_pos (one_div_pos.2 (mul_pos (flagConst_pos j) (flagConst_pos k))) (pow_pos Real.pi_pos _)).le h1 f
    _ ≤ (Real.exp 3 ^ ((j + k) * (j + k))) ^ f :=
        pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ Real.pi_pos.le hπe _) f
    _ = Real.exp (3 * (((j + k) * (j + k) * f : ℕ) : ℝ)) := by
        rw [← pow_mul, ← Real.exp_nat_mul, mul_comm]
    _ ≤ Real.exp (3 * ((f : ℝ) * ((j + k : ℕ) : ℝ)) ^ 8) := by
        refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (by norm_num))
        exact_mod_cast hn

theorem lintegral_kaF_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r →
    ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y →
    ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z)
      ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) := by
  refine ⟨3, by norm_num, ?_⟩
  intro E _ _ _ r X y _ _ hy
  have hj : r - X.p0 ≤ r := Nat.sub_le _ _
  have hp : X.p0 = r - (r - X.p0) := (Nat.sub_sub_self X.p0_le).symm
  have hf : (1 : ℝ) ≤ X.Ψ.card := by
    have := Finset.card_pos.2 (Finset.nonempty_coe_sort.1 (psi_nonempty X))
    exact_mod_cast this
  have hbb : (r : ℝ) ≤ 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1 := by
    have hr : (r : ℝ) ≤ (r : ℝ) ^ 2 := by
      have : r ≤ r * r := Nat.le_mul_self r
      rw [sq]; exact_mod_cast this
    nlinarith [sq_nonneg (r : ℝ)]
  have hka : kaF X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) =
      kaF X (x0F X) (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) := by
    funext z
    simp only [kaF, GlobalTheory.Up.PoleValue.rhF_eq (isOrth_x0F X) hy]
  rw [hka, GlobalTheory.Up.PoleValue.muF_eq (isOrth_x0F X) hy]
  exact (lintegral_x0F_le X hj hp hbb).trans (bound_num r (r - X.p0) X.Ψ.card hj)

end GlobalTheory.KernelIntegral
