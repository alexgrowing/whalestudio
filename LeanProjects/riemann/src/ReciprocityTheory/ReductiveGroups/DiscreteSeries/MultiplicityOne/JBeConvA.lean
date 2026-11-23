import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDefs
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

theorem bc_gN_eq_frob (g : Mat k r) :
    gN g = @Norm.norm _ (Matrix.frobeniusSeminormedAddCommGroup).toNorm g := by
  unfold gN
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq, Real.rpow_two]

theorem bc_gN_mul_le (a b : Mat k r) : gN (a * b) ≤ gN a * gN b := by
  rw [bc_gN_eq_frob, bc_gN_eq_frob, bc_gN_eq_frob]
  exact Matrix.frobenius_norm_mul a b

theorem bc_gN_nonneg (g : Mat k r) : 0 ≤ gN g := Real.sqrt_nonneg _

theorem bc_gN_pos_of_ne {g : Mat k r} (hg : g ≠ 0) : 0 < gN g := by
  obtain ⟨i, j, hij⟩ : ∃ i j, g i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (Matrix.ext h)
  unfold gN
  apply Real.sqrt_pos.mpr
  apply lt_of_lt_of_le (Complex.normSq_pos.mpr hij)
  calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
        Finset.single_le_sum (fun j' _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
          (fun i' _ => Finset.sum_nonneg fun j' _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

theorem bc_gN_zero : gN (0 : Mat k r) = 0 := by
  simp [gN]

theorem bc_gN_continuous : Continuous (fun g : Mat k r => gN g) := by
  unfold gN
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))

theorem bc_measurable_invM : Measurable (invM (k := k) (r := r)) := by
  have h1 : Continuous fun x : Mt k r => (Matrix.of x : Mat k r).det := continuous_id.matrix_det
  have h2 : Continuous fun x : Mt k r => (Matrix.of x : Mat k r).adjugate := continuous_id.matrix_adjugate
  have he : ∀ (x : Mt k r) (i j : Fin (2 * r + k + 1)),
      invM x i j = ((Matrix.of x : Mat k r).det)⁻¹ * (Matrix.of x : Mat k r).adjugate i j := by
    intro x i j
    simp only [invM, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [he]
  exact h1.measurable.inv.mul ((continuous_apply j).comp ((continuous_apply i).comp h2)).measurable

theorem bc_AB_le_of (b : ℝ) (hb : AS k r + 1 ≤ b) : AB k r ≤ b := by
  unfold AB
  unfold AS nR at hb
  push_cast at hb
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  nlinarith [sq_nonneg ((k : ℝ) + r), sq_nonneg ((r : ℝ) + 1),
    mul_nonneg (sq_nonneg (2 * (r : ℝ) + k + 1)) (by positivity : (0 : ℝ) ≤ 2 * r + k)]

theorem bc_gN_cont_mt : Continuous (fun g : Mt k r => gN (Matrix.of g : Mat k r)) := bc_gN_continuous

def bcPow (A : ℝ) (g : Mt k r) : ℝ≥0∞ := ENNReal.ofReal (gN (Matrix.of g : Mat k r) ^ (-A))

theorem bc_measurable_pow (A : ℝ) : Measurable (bcPow (k := k) (r := r) A) := ENNReal.measurable_ofReal.comp (bc_gN_cont_mt.measurable.pow_const (-A))

theorem bc_continuous_mulM : Continuous (mulM (k := k) (r := r)) := by
  unfold mulM
  exact continuous_fst.matrix_mul continuous_snd

theorem bc_isHaarOn_sigmaFinite {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    SigmaFinite μ := by
  have _ : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

theorem bc_isHaarOn_ae_mem {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    ∀ᵐ x ∂μ, (Matrix.of x : Mat k r) ∈ U := by
  rw [ae_iff]
  exact h.conc

theorem bc_ae_prod_and {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [SFinite ν] {P : α → Prop} {Q : β → Prop} (hP : ∀ᵐ x ∂μ, P x)
    (hQ : ∀ᵐ y ∂ν, Q y) : ∀ᵐ p ∂(μ.prod ν), P p.1 ∧ Q p.2 := ((Measure.quasiMeasurePreserving_fst.ae hP).and (Measure.quasiMeasurePreserving_snd.ae hQ))

theorem bc_pow_pos_of_mem (hGL : GNLower) {g : Mat k r} (hg : g ∈ GV k r) (A : ℝ) :
    0 < bcPow A (g : Mt k r) := by
  have h1 : 1 ≤ gN (Matrix.of g : Mat k r) := hGL k r g hg
  unfold bcPow
  exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)

theorem bc_lintegral_pow_ne_zero {α : Type*} [MeasurableSpace α] (hGL : GNLower) {μ : Measure α}
    (hμ : μ ≠ 0) (φ : α → Mt k r) (hφ : Measurable φ) (hmem : ∀ᵐ x ∂μ, (Matrix.of (φ x) : Mat k r) ∈ GV k r)
    (A : ℝ) : (∫⁻ x, bcPow A (φ x) ∂μ) ≠ 0 := by
  intro h0
  have h0' := (lintegral_eq_zero_iff ((bc_measurable_pow A).comp hφ)).mp h0
  have hF : ∀ᵐ x ∂μ, False := by
    filter_upwards [h0', hmem] with x hx hxm
    have hx' : bcPow A (φ x) = 0 := by simpa using hx
    exact (bc_pow_pos_of_mem hGL hxm A).ne' hx'
  exact hμ (ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hF))

theorem bc_pow_zero {A : ℝ} (hA : A ≠ 0) : bcPow A ((0 : Mat k r) : Mt k r) = 0 := by
  show ENNReal.ofReal (gN (0 : Mat k r) ^ (-A)) = 0
  rw [bc_gN_zero, Real.zero_rpow (neg_ne_zero.mpr hA), ENNReal.ofReal_zero]

theorem norm_power_product_lower_bound {a g b : Mat k r} (ha : IsUnit a) (hb : IsUnit b) (hg : g ≠ 0) {A : ℝ} (hA : 0 ≤ A) :
    bcPow A (g : Mt k r) * (bcPow A (a : Mt k r) * bcPow A (b : Mt k r)) ≤ bcPow A ((a * g * b : Mat k r) : Mt k r) := by
  have hagb : a * g * b ≠ 0 := by
    intro h0
    exact hg ((ha.mul_right_eq_zero).mp ((hb.mul_left_eq_zero).mp h0))
  have pa := bc_gN_pos_of_ne ha.ne_zero
  have pb := bc_gN_pos_of_ne hb.ne_zero
  have pg := bc_gN_pos_of_ne hg
  have pagb := bc_gN_pos_of_ne hagb
  have hle : gN (a * g * b) ≤ gN a * gN g * gN b :=
    calc gN (a * g * b) ≤ gN (a * g) * gN b := bc_gN_mul_le _ _
      _ ≤ gN a * gN g * gN b := mul_le_mul_of_nonneg_right (bc_gN_mul_le _ _) pb.le
  show ENNReal.ofReal (gN g ^ (-A)) * (ENNReal.ofReal (gN a ^ (-A)) * ENNReal.ofReal (gN b ^ (-A))) ≤
    ENNReal.ofReal (gN (a * g * b) ^ (-A))
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg pa.le _), ← ENNReal.ofReal_mul (Real.rpow_nonneg pg.le _)]
  apply ENNReal.ofReal_le_ofReal
  calc gN g ^ (-A) * (gN a ^ (-A) * gN b ^ (-A)) = (gN a * gN g * gN b) ^ (-A) := by
        rw [Real.mul_rpow (mul_nonneg pa.le pg.le) pb.le, Real.mul_rpow pa.le pg.le]
        ring
    _ ≤ gN (a * g * b) ^ (-A) := Real.rpow_le_rpow_of_nonpos pagb hle (by linarith)

theorem bc_lintegral_S_pow_AB (hM : UnitaryGroupStructuralFacts) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (hW : D.μW' = D.μW) :
    (∫⁻ p : Mt k r × Mt k r, bcPow (AB k r) (mulM (p.2, p.1)) ∂(D.μW.prod D.μN)) < ∞ := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hGI, hGL, -, -, -, hCG, -, -, -, -, -, -, -⟩,
    -, -, -, -, -, -, -, -, -, -, -, -, -, hINB, -, -, -⟩ := hM
  obtain ⟨c, ⟨hc, hF⟩, -⟩ := hINB k r Wp Wq D
  set A := AB k r with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    unfold AB
    positivity
  have hA : A ≠ 0 := by
    rw [hAdef]
    unfold AB
    positivity
  have _ := bc_isHaarOn_sigmaFinite D.haarW
  have _ := bc_isHaarOn_sigmaFinite D.haarN
  have _ := bc_isHaarOn_sigmaFinite D.haarW'
  let f : Mt k r → ℝ≥0∞ := bcPow A
  have hfm : Measurable f := bc_measurable_pow A
  let Fa : Mt k r × Mt k r → Mt k r := fun p => mulM (invM p.1, invM p.2)
  let Gb : Mt k r × Mt k r → Mt k r := fun p => mulM (p.2, p.1)
  have hFa : Measurable Fa := bc_continuous_mulM.measurable.comp (bc_measurable_invM.prodMap bc_measurable_invM)
  have hGb : Measurable Gb := bc_continuous_mulM.measurable.comp measurable_swap
  have hae1 : ∀ᵐ p ∂(D.μW.prod D.μN), (Matrix.of p.1 : Mat k r) ∈ UWset k r D.z ∧
      (Matrix.of p.2 : Mat k r) ∈ Nset k r :=
    bc_ae_prod_and (bc_isHaarOn_ae_mem D.haarW) (bc_isHaarOn_ae_mem D.haarN)
  have hae2 : ∀ᵐ p ∂(D.μW'.prod D.μN), (Matrix.of p.1 : Mat k r) ∈ UWset k r D.z' ∧
      (Matrix.of p.2 : Mat k r) ∈ Nset k r :=
    bc_ae_prod_and (bc_isHaarOn_ae_mem D.haarW') (bc_isHaarOn_ae_mem D.haarN)
  have haeSS := bc_ae_prod_and (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN) hae1 hae2
  have hunitG : ∀ x ∈ GV k r, IsUnit x := fun x hx =>
    (Matrix.isUnit_iff_isUnit_det x).mpr ((hCG k r).unit x hx)
  have hL : (∫⁻ p, f (Fa p) ∂(D.μW.prod D.μN)) ≠ 0 := by
    refine bc_lintegral_pow_ne_zero hGL ?_ Fa hFa ?_ A
    · rw [← Measure.measure_univ_ne_zero, ← Set.univ_prod_univ, Measure.prod_prod]
      exact mul_ne_zero (Measure.measure_univ_ne_zero.mpr D.haarW.ne_zero)
        (Measure.measure_univ_ne_zero.mpr D.haarN.ne_zero)
    · filter_upwards [hae1] with p hp
      exact (hCG k r).mul_mem _ ((hCG k r).inv_mem _ hp.1.1) _ ((hCG k r).inv_mem _ hp.2.1)
  have hlow : ∀ g : Mat k r, g ≠ 0 →
      f g * ((∫⁻ p, f (Fa p) ∂(D.μW.prod D.μN)) * ∫⁻ p, f (Gb p) ∂(D.μW'.prod D.μN)) ≤
        ∫⁻ p, f (sgs p g) ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) := by
    intro g hg
    have hprod : ∫⁻ z, f (Fa z.1) * f (Gb z.2) ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) =
        (∫⁻ p, f (Fa p) ∂(D.μW.prod D.μN)) * ∫⁻ p, f (Gb p) ∂(D.μW'.prod D.μN) :=
      lintegral_prod_mul (hfm.comp hFa).aemeasurable (hfm.comp hGb).aemeasurable
    have hcm : ∫⁻ z, f g * (f (Fa z.1) * f (Gb z.2)) ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) =
        f g * ∫⁻ z, f (Fa z.1) * f (Gb z.2) ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    refine (congrArg (f g * ·) hprod.symm).trans_le (hcm.symm.trans_le (lintegral_mono_ae ?_))
    filter_upwards [haeSS] with p hp
    have ha : IsUnit ((Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹) :=
      hunitG _ ((hCG k r).mul_mem _ ((hCG k r).inv_mem _ hp.1.1.1) _ ((hCG k r).inv_mem _ hp.1.2.1))
    have hb : IsUnit ((Matrix.of p.2.2 : Mat k r) * (Matrix.of p.2.1 : Mat k r)) :=
      hunitG _ ((hCG k r).mul_mem _ hp.2.2.1 _ hp.2.1.1)
    have hs : sgs p g = (Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ * g *
        ((Matrix.of p.2.2 : Mat k r) * Matrix.of p.2.1) := by
      simp only [sgs, Matrix.mul_assoc]
    exact (norm_power_product_lower_bound ha hb hg hA0).trans_eq (congrArg f hs.symm)
  by_contra hK
  rw [not_lt, top_le_iff] at hK
  have hK' : ∫⁻ p, f (Gb p) ∂(D.μW'.prod D.μN) = ⊤ := by
    rw [hW]
    exact hK
  have hGfin : ∫⁻ g, f g ∂D.μG < ⊤ := hGI k r D.μG A D.haarG le_rfl
  have hGne : ∫⁻ g, f g ∂D.μG ≠ 0 :=
    bc_lintegral_pow_ne_zero hGL D.haarG.ne_zero id measurable_id (bc_isHaarOn_ae_mem D.haarG) A
  let h : (Fin r → ℂ) × ℂ → ℝ≥0∞ := fun q => ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q) *
      ∫⁻ p, f (sgs p (bigCell k r q.1 (D.μsec q.2))) ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN))
  have hIF : c • ∫⁻ g, f g ∂D.μG = ∫⁻ q, h q := by
    rw [← lintegral_smul_measure]
    exact hF f hfm
  have h2 : ∀ q, h q = 2 * h q := by
    intro q
    by_cases hw : ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q) = 0
    · simp only [h, hw, zero_mul, mul_zero]
    by_cases hb0 : bigCell k r q.1 (D.μsec q.2) = 0
    · have hz : ∀ p, f (sgs p (bigCell k r q.1 (D.μsec q.2))) = 0 := by
        intro p
        rw [hb0]
        simp only [sgs, Matrix.mul_zero, Matrix.zero_mul]
        exact bc_pow_zero hA
      simp only [h, hz, lintegral_zero, mul_zero]
    · have hpos : f (bigCell k r q.1 (D.μsec q.2)) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (bc_gN_pos_of_ne hb0) _)).ne'
      have hinf := hlow _ hb0
      rw [hK', ENNReal.mul_top hL, ENNReal.mul_top hpos, top_le_iff] at hinf
      show ENNReal.ofReal _ * _ = 2 * (ENNReal.ofReal _ * _)
      rw [hinf, ENNReal.mul_top hw, ENNReal.mul_top two_ne_zero]
  have hfin : ∫⁻ q, h q ≠ ⊤ := by
    rw [← hIF, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hGfin.ne
  have hdouble : ∫⁻ q, h q = 2 * ∫⁻ q, h q := by
    rw [← lintegral_const_mul' 2 h (by norm_num)]
    exact lintegral_congr fun q => h2 q
  have hzero : ∫⁻ q, h q = 0 := by
    have ht : (∫⁻ q, h q).toReal = 2 * (∫⁻ q, h q).toReal := by
      conv_lhs => rw [hdouble]
      simp [ENNReal.toReal_mul]
    have h0 : (∫⁻ q, h q).toReal = 0 := by linarith
    rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h0 | h0
    · exact h0
    · exact absurd h0 hfin
  rw [← hIF, ENNReal.smul_def, smul_eq_mul] at hzero
  rcases mul_eq_zero.mp hzero with h0 | h0
  · exact hc.ne' (ENNReal.coe_eq_zero.mp h0)
  · exact hGne h0

end ReciprocityTheory.ChartRestriction.DS.Mult1
