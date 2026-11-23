import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SecondProjectionOrthogonalComplement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropASt

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

def ctU (q : ℕ) (b : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) : EuclideanSpace ℂ ι → ℂ :=
  fun t => cexp (q * Real.pi * Hf t b - q * Real.pi * Hf b b / 2) * F (t - b)

def ctY (Y : GT ι) (w : EuclideanSpace ℂ ι) : GT ι where
  b := Y.b
  integral := Y.integral
  perfect := Y.perfect
  ka := fun t => Y.ka t * cexp (2 * Real.pi * (Hf t w).im * I)
  ka_abs := by
    intro x hx
    rw [norm_mul, Y.ka_abs x hx, one_mul, Complex.norm_exp]
    simp

theorem twisted_firstMinimum (Y : GT ι) (w : EuclideanSpace ℂ ι) : (ctY Y w).la1 = Y.la1 := rfl

theorem ctY_lat (Y : GT ι) (w : EuclideanSpace ℂ ι) : lat (ctY Y w).b = lat Y.b := rfl

private theorem Hf_add_left_euclidean (a b c : EuclideanSpace ℂ ι) : Hf (a + b) c = Hf a c + Hf b c := by
  simp [Hf, add_mul, Finset.sum_add_distrib]

private theorem Hf_sub_leftSquareIntegrability (a b c : EuclideanSpace ℂ ι) : Hf (a - b) c = Hf a c - Hf b c := by
  simp [Hf, sub_mul, Finset.sum_sub_distrib]

private theorem Hf_add_right_euclidean (a b c : EuclideanSpace ℂ ι) : Hf a (b + c) = Hf a b + Hf a c := by
  simp [Hf, mul_add, Finset.sum_add_distrib]

private theorem Hf_sub_right' (a b c : EuclideanSpace ℂ ι) : Hf a (b - c) = Hf a b - Hf a c := by
  simp [Hf, mul_sub, Finset.sum_sub_distrib]

private theorem Hf_smul_right' (a b : EuclideanSpace ℂ ι) (c : ℂ) :
    Hf a (c • b) = (starRingEnd ℂ) c * Hf a b := by
  simp only [Hf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp <;> ring

private theorem Hf_swap_eq_conj' (a b : EuclideanSpace ℂ ι) : Hf b a = (starRingEnd ℂ) (Hf a b) := by
  simp only [Hf, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem norm_sq_eq_re_Hf_self (v : EuclideanSpace ℂ ι) : ‖v‖ ^ 2 = (Hf v v).re := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp only [Hf, Complex.re_sum, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  all_goals rfl

private theorem Hf_neg_left' (a c : EuclideanSpace ℂ ι) : Hf (-a) c = -Hf a c := by
  simp [Hf, Finset.sum_neg_distrib]

private theorem Hf_neg_right' (a c : EuclideanSpace ℂ ι) : Hf a (-c) = -Hf a c := by
  simp [Hf, Finset.sum_neg_distrib]

private theorem Hf_eq_inner_swap_euclidean (v w : EuclideanSpace ℂ ι) : Hf v w = @inner ℂ _ _ w v := by
  simp [Hf, PiLp.inner_apply, mul_comm]

private theorem Hf_finset_sum_right {κ : Type} (s : Finset κ) (v : EuclideanSpace ℂ ι)
    (f : κ → EuclideanSpace ℂ ι) : Hf v (∑ k ∈ s, f k) = ∑ k ∈ s, Hf v (f k) :=
  map_sum (AddMonoidHom.mk' (fun w => Hf v w) (Hf_add_right_euclidean v)) f s

private theorem Hf_real_smul_right (v w : EuclideanSpace ℂ ι) (r : ℝ) :
    Hf v (r • w) = (r : ℂ) * Hf v w := by
  simp only [Hf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp <;> ring

theorem ctY_coc (Y : GT ι) (w : EuclideanSpace ℂ ι) (q : ℕ) (h : Y.Coc q) : (ctY Y w).Coc q := by
  intro γ hγ γ' hγ'
  show Y.ka (γ + γ') * cexp (2 * Real.pi * (Hf (γ + γ') w).im * I) =
    Y.ka γ * cexp (2 * Real.pi * (Hf γ w).im * I) * (Y.ka γ' * cexp (2 * Real.pi * (Hf γ' w).im * I)) *
      cexp (-(Real.pi * q * (Hf γ γ').im) * I)
  rw [h γ hγ γ' hγ', Col.Hf_add_l, Complex.add_im]
  have e : cexp (2 * Real.pi * (((Hf γ w).im + (Hf γ' w).im : ℝ) : ℂ) * I) =
      cexp (2 * Real.pi * (Hf γ w).im * I) * cexp (2 * Real.pi * (Hf γ' w).im * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e]; ring

theorem ctU_mem (Y : GT ι) (w : EuclideanSpace ℂ ι) {q : ℕ} (hq : 1 ≤ q) {F : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ (ctY Y w).Sec q) : ctU q (-((1 / (q : ℂ)) • w)) F ∈ Y.Sec q := by
  obtain ⟨hFd, hFe⟩ := hF
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  generalize hb : -((1 / (q : ℂ)) • w) = b
  change Differentiable ℂ (ctU q b F) ∧ ∀ γ ∈ lat Y.b, ∀ v, ctU q b F (v + γ) =
    Y.ka γ * cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) * ctU q b F v
  refine ⟨?_, ?_⟩
  · have hd : Differentiable ℂ (fun t : EuclideanSpace ℂ ι => Hf t b) := by
      have hfun : (fun t : EuclideanSpace ℂ ι => Hf t b) = fun t => innerSL ℂ b t := by
        funext t
        simp [Hf_eq_inner_swap_euclidean]
      rw [hfun]
      exact (innerSL ℂ b).differentiable
    unfold ctU
    exact (((hd.const_mul _).sub_const _).cexp).mul (hFd.comp (differentiable_id.sub_const _))
  · intro γ hγ v
    have hγb : Hf γ b = -(1 / (q : ℂ)) * Hf γ w := by
      rw [← hb, Hf_neg_right', Hf_smul_right']
      simp
    have hbγ : Hf b γ = -(1 / (q : ℂ)) * (starRingEnd ℂ) (Hf γ w) := by
      rw [Hf_swap_eq_conj' γ b, hγb]
      simp
    have hsub : Hf γ w - (starRingEnd ℂ) (Hf γ w) = 2 * ((Hf γ w).im : ℂ) * I := by
      apply Complex.ext <;> simp <;> ring
    have hc : (q : ℂ) * (1 / (q : ℂ)) = 1 := mul_one_div_cancel hq0
    have key : cexp (q * Real.pi * Hf (v + γ) b - q * Real.pi * Hf b b / 2) *
        cexp (2 * Real.pi * (Hf γ w).im * I) *
        cexp (q * Real.pi * Hf (v - b) γ + q * Real.pi * Hf γ γ / 2) =
        cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) *
        cexp (q * Real.pi * Hf v b - q * Real.pi * Hf b b / 2) := by
      simp only [← Complex.exp_add]
      congr 1
      rw [Hf_add_left_euclidean, Hf_sub_leftSquareIntegrability, hγb, hbγ]
      linear_combination (-(Real.pi : ℂ) * (Hf γ w - (starRingEnd ℂ) (Hf γ w))) * hc +
        (-(Real.pi : ℂ)) * hsub
    have hka : (ctY Y w).ka γ = Y.ka γ * cexp (2 * Real.pi * (Hf γ w).im * I) := rfl
    have hv : v + γ - b = (v - b) + γ := by abel
    simp only [ctU]
    rw [hv, hFe γ hγ (v - b), hka]
    linear_combination (Y.ka γ * F (v - b)) * key

theorem pointNormSq_translate (Y : GT ι) (q : ℕ) (b : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ)
    (t : EuclideanSpace ℂ ι) : Y.ptN2 q (ctU q b F) t = Y.ptN2 q F (t - b) := by
  have e1 : ‖t - b‖ ^ 2 = ‖t‖ ^ 2 - 2 * (Hf t b).re + ‖b‖ ^ 2 := by
    rw [norm_sq_eq_re_Hf_self (t - b), norm_sq_eq_re_Hf_self t, norm_sq_eq_re_Hf_self b, Hf_sub_leftSquareIntegrability, Hf_sub_right', Hf_sub_right',
      Hf_swap_eq_conj' t b]
    simp only [Complex.sub_re, Complex.conj_re]
    ring
  have hA : ((q : ℂ) * (Real.pi : ℂ) * Hf t b - (q : ℂ) * (Real.pi : ℂ) * Hf b b / 2) =
      ((q * Real.pi : ℝ) : ℂ) * Hf t b - ((q * Real.pi / 2 : ℝ) : ℂ) * Hf b b := by
    push_cast
    ring
  simp only [GT.ptN2, ctU]
  rw [hA, norm_mul, Complex.norm_exp, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    ← norm_sq_eq_re_Hf_self b, e1]
  rw [mul_pow, mul_comm (Real.exp _ ^ 2), mul_assoc]
  congr 1
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem pointNormSq_periodic (Y : GT ι) {q : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ Y.Sec q)
    {γ : EuclideanSpace ℂ ι} (hγ : γ ∈ lat Y.b) (t : EuclideanSpace ℂ ι) :
    Y.ptN2 q F (t + γ) = Y.ptN2 q F t := by
  obtain ⟨_, hFe⟩ := hF
  have e1 : ‖t + γ‖ ^ 2 = ‖t‖ ^ 2 + 2 * (Hf t γ).re + ‖γ‖ ^ 2 := by
    rw [norm_sq_eq_re_Hf_self (t + γ), norm_sq_eq_re_Hf_self t, norm_sq_eq_re_Hf_self γ, Hf_add_left_euclidean, Hf_add_right_euclidean, Hf_add_right_euclidean,
      Hf_swap_eq_conj' t γ]
    simp only [Complex.add_re, Complex.conj_re]
    ring
  have hA : ((q : ℂ) * (Real.pi : ℂ) * Hf t γ + (q : ℂ) * (Real.pi : ℂ) * Hf γ γ / 2) =
      ((q * Real.pi : ℝ) : ℂ) * Hf t γ + ((q * Real.pi / 2 : ℝ) : ℂ) * Hf γ γ := by
    push_cast
    ring
  simp only [GT.ptN2]
  rw [hFe γ hγ t, hA, norm_mul, norm_mul, Y.ka_abs γ hγ, one_mul, Complex.norm_exp, Complex.add_re,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul, ← norm_sq_eq_re_Hf_self γ, e1]
  rw [mul_pow, mul_comm (Real.exp _ ^ 2), mul_assoc]
  congr 1
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

instance ctCnt (Y : GT ι) : Countable (Submodule.span ℤ (Set.range Y.b)).toAddSubgroup :=
  inferInstanceAs (Countable (Submodule.span ℤ (Set.range Y.b)))

theorem ct_avg_trans (Y : GT ι) (g : EuclideanSpace ℂ ι → ℝ)
    (hper : ∀ γ ∈ lat Y.b, ∀ v, g (v + γ) = g v) (a : EuclideanSpace ℂ ι) :
    (⨍ v in ZSpan.fundamentalDomain Y.b, g (v - a)) = ⨍ v in ZSpan.fundamentalDomain Y.b, g v := by
  have hD := ZSpan.isAddFundamentalDomain Y.b volume
  have hT : IsAddFundamentalDomain (Submodule.span ℤ (Set.range Y.b)).toAddSubgroup
      ((fun u => u + a) ⁻¹' ZSpan.fundamentalDomain Y.b) volume :=
    hD.preimage_of_equiv (measurePreserving_add_right volume a).quasiMeasurePreserving
      Function.bijective_id fun _ _ => add_assoc _ _ _
  have hg : ∀ (γ : (Submodule.span ℤ (Set.range Y.b)).toAddSubgroup) (x : EuclideanSpace ℂ ι),
      g (γ +ᵥ x) = g x := by
    rintro ⟨γ, hγ⟩ x
    have h := hper γ hγ x
    rw [add_comm] at h
    exact h
  simp only [MeasureTheory.setAverage_eq]
  congr 1
  have h1 := (measurePreserving_add_right volume a).setIntegral_preimage_emb
    (MeasurableEquiv.addRight a).measurableEmbedding (fun y => g (y - a)) (ZSpan.fundamentalDomain Y.b)
  simp only [add_sub_cancel_right] at h1
  rw [← h1]
  exact hT.setIntegral_eq hD hg

theorem l2_ctU_eq_l2_ctY (Y : GT ι) (w : EuclideanSpace ℂ ι) {q : ℕ} {F : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ (ctY Y w).Sec q) :
    Y.l2 q (ctU q (-((1 / (q : ℂ)) • w)) F) = (ctY Y w).l2 q F := by
  have hper : ∀ γ ∈ lat Y.b, ∀ v, Y.ptN2 q F (v + γ) = Y.ptN2 q F v :=
    fun γ hγ v => pointNormSq_periodic (ctY Y w) hF hγ v
  simp only [GT.l2, pointNormSq_translate]
  exact ct_avg_trans Y _ hper _

end

end ReciprocityTheory.ChartRestriction.G.I2

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

theorem ctU_cancel (q : ℕ) (b : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) :
    ctU q b (ctU q (-b) F) = F := by
  funext t
  have e : (q * Real.pi * Hf t b - q * Real.pi * Hf b b / 2 : ℂ) +
      (q * Real.pi * Hf (t - b) (-b) - q * Real.pi * Hf (-b) (-b) / 2) = 0 := by
    simp only [Hf_sub_leftSquareIntegrability, Hf_neg_right', Hf_neg_left', neg_neg]
    ring
  simp only [ctU]
  rw [← mul_assoc, ← Complex.exp_add, e, Complex.exp_zero, one_mul, sub_neg_eq_add, sub_add_cancel]

variable {K : Submodule ℝ (EuclideanSpace ℂ ι)} (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
include hK

theorem ct_Hf_uc (v a : EuclideanSpace ℂ ι) :
    Hf v (Col.uc K a) = ∑ k, ((Col.z K k a).im : ℂ) * Col.z K k v := by
  simp only [Col.uc]
  rw [Hf_finset_sum_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Hf_real_smul_right]
  rfl

theorem translate_zeroModeLift_formula (q : ℕ) (β : EuclideanSpace ℂ (Fin (Col.gB K)) → ℂ) (a v : EuclideanSpace ℂ ι) :
    cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) *
        (cexp ((q * Real.pi / 2 : ℂ) * Col.S K (v - a)) * β (Col.wmap K (v - a))) =
      cexp ((q * Real.pi / 2 : ℂ) * Col.S K a - q * Real.pi * Hf a a / 2 +
          q * Real.pi * Hf (Col.wmap K a) (Col.wmap K a) / 2) *
        cexp (-(2 * Real.pi * q : ℂ) * I * Hf v (Col.uc K a)) *
        (cexp ((q * Real.pi / 2 : ℂ) * Col.S K v) * ctU q (Col.wmap K a) β (Col.wmap K v)) := by
  have hz : ∀ k, Col.z K k (v - a) = Col.z K k v - Col.z K k a := fun k => Col.Hf_sub_l _ _ _
  have hS : Col.S K (v - a) = ∑ k, (Col.z K k v - Col.z K k a) ^ 2 := by
    unfold Col.S; simp only [hz]
  have hk : ∀ k, (q : ℂ) * Real.pi * (Col.z K k v * (starRingEnd ℂ) (Col.z K k a)) +
      (q * Real.pi / 2 : ℂ) * (Col.z K k v - Col.z K k a) ^ 2 =
      (q * Real.pi / 2 : ℂ) * Col.z K k a ^ 2 + (q * Real.pi / 2 : ℂ) * Col.z K k v ^ 2 +
        (-(2 * Real.pi * q : ℂ) * I) * (((Col.z K k a).im : ℂ) * Col.z K k v) := by
    intro k
    have hc : (starRingEnd ℂ) (Col.z K k a) = Col.z K k a - 2 * ((Col.z K k a).im : ℂ) * I := by
      apply Complex.ext <;> simp <;> ring
    rw [hc]; ring_nf
  have hsum := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hk k)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hdec := Col.Hf_decomp hK v a
  have hw : Col.wmap K (v - a) = Col.wmap K v - Col.wmap K a := map_sub _ _ _
  have hww := Col.Hf_wmap hK v a
  unfold ctU
  rw [hw, ct_Hf_uc hK]
  have E : (q : ℂ) * Real.pi * Hf v a - q * Real.pi * Hf a a / 2 +
      (q * Real.pi / 2 : ℂ) * Col.S K (v - a) =
      ((q * Real.pi / 2 : ℂ) * Col.S K a - q * Real.pi * Hf a a / 2 +
          q * Real.pi * Hf (Col.wmap K a) (Col.wmap K a) / 2) +
        -(2 * Real.pi * q : ℂ) * I * ∑ k, ((Col.z K k a).im : ℂ) * Col.z K k v +
        ((q * Real.pi / 2 : ℂ) * Col.S K v +
          ((q : ℂ) * Real.pi * Hf (Col.wmap K v) (Col.wmap K a) -
            q * Real.pi * Hf (Col.wmap K a) (Col.wmap K a) / 2)) := by
    rw [hS, hdec, hww]
    unfold Col.S
    linear_combination hsum
  calc _ = cexp ((q : ℂ) * Real.pi * Hf v a - q * Real.pi * Hf a a / 2 +
        (q * Real.pi / 2 : ℂ) * Col.S K (v - a)) * β (Col.wmap K v - Col.wmap K a) := by
        rw [Complex.exp_add]; ring
    _ = _ := by rw [E]; simp only [Complex.exp_add, Complex.exp_sub]; ring

end

end ReciprocityTheory.ChartRestriction.G.I2
