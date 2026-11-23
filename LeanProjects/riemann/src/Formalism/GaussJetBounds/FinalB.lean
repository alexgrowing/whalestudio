import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffQuadSer
import Formalism.GaussJetBounds.GaussJetProofs.MfactEqProdUniv
import Formalism.GaussJetBounds.GaussJetProofs.OneRow
import Formalism.GaussJetBounds.GaussJetProofs.FirstRowMinorDegreeLeOne
import Formalism.GaussJetBounds.GaussJetProofs.IntegralOperatorsOnJets
import Formalism.GaussJetBounds.GaussJetProofs.GaussB

universe u

namespace Formalism.DworkPowerSeriesWeights

theorem matchings : Matchings.{u} := matching_existence
theorem pairJet : PairJet.{u} := pair_jet_bound
theorem oneRowBasis : OneRowBasis.{u} := by
  unfold OneRowBasis
  intro K _ _ N0 h0 x1 hx hx1
  obtain ⟨a0, ha0⟩ := hx1
  set z : Fin N0 := ⟨0, h0⟩ with hz
  have hu0 : x1 a0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha0
    exact zero_ne_one ha0
  have huinv : ‖(x1 a0)⁻¹‖ = 1 := by rw [norm_inv, ha0, inv_one]
  let σ : Equiv.Perm (Fin N0) := Equiv.swap z a0
  have hσz : σ z = a0 := Equiv.swap_apply_left z a0
  let d : Fin N0 → K := fun a => if a = z then (x1 a0)⁻¹ else 1
  let e : Fin N0 → K := fun a => if a = z then 0 else -(x1 (σ a) * (x1 a0)⁻¹)
  let g : Matrix (Fin N0) (Fin N0) K :=
    fun a b => (if a = b then d a else 0) + (if z = b then e a else 0)
  have hd : ∀ a, ‖d a‖ ≤ 1 := by
    intro a
    show ‖(if a = z then (x1 a0)⁻¹ else 1)‖ ≤ 1
    split_ifs
    · exact huinv.le
    · simp
  have he : ∀ a, ‖e a‖ ≤ 1 := by
    intro a
    show ‖(if a = z then 0 else -(x1 (σ a) * (x1 a0)⁻¹))‖ ≤ 1
    split_ifs
    · simp
    · rw [norm_neg, norm_mul, huinv, mul_one]
      exact hx _
  have hg : ∀ a b, ‖g a b‖ ≤ 1 := by
    intro a b
    show ‖(if a = b then d a else 0) + (if z = b then e a else 0)‖ ≤ 1
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · split_ifs
      · exact hd a
      · simp
    · split_ifs
      · exact he a
      · simp
  have htri : g.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    have h2 : ¬ z = j := by
      intro h
      have h3 : (z : ℕ) = (j : ℕ) := congrArg Fin.val h
      have h4 : (z : ℕ) = 0 := by rw [hz]
      have h5 : (i : ℕ) < (j : ℕ) := hij'
      omega
    show (if i = j then d i else 0) + (if z = j then e i else 0) = 0
    rw [if_neg (ne_of_lt hij'), if_neg h2, add_zero]
  have hdet : ‖g.det‖ = 1 := by
    rw [Matrix.det_of_lowerTriangular g htri, norm_prod]
    refine Finset.prod_eq_one (fun i _ => ?_)
    show ‖(if i = i then d i else 0) + (if z = i then e i else 0)‖ = 1
    rw [if_pos (rfl : i = i)]
    by_cases hi : z = i
    · subst hi
      show ‖(if z = z then (x1 a0)⁻¹ else 1) +
          (if z = z then 0 else -(x1 (σ z) * (x1 a0)⁻¹))‖ = 1
      rw [if_pos (rfl : z = z), if_pos (rfl : z = z), add_zero]
      exact huinv
    · rw [if_neg hi, add_zero]
      show ‖(if i = z then (x1 a0)⁻¹ else 1)‖ = 1
      rw [if_neg (fun h => hi h.symm)]
      simp
  refine ⟨g.submatrix id σ, fun a a' => hg a (σ a'), ?_, ?_⟩
  · rw [Matrix.det_permute', norm_mul, hdet, mul_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  · intro a
    have hsum : (∑ a', x1 a' * (g.submatrix id σ) a a') = ∑ b, x1 (σ b) * g a b :=
      Fintype.sum_equiv σ _ _ (fun a' => by simp [σ, Matrix.submatrix_apply])
    rw [hsum]
    show (∑ b, x1 (σ b) * ((if a = b then d a else 0) + (if z = b then e a else 0))) = _
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    by_cases ha : a = z
    · rw [if_pos ha, ha, hσz]
      show x1 a0 * (if z = z then (x1 a0)⁻¹ else 1) +
          x1 a0 * (if z = z then 0 else -(x1 (σ z) * (x1 a0)⁻¹)) = 1
      rw [if_pos (rfl : z = z), if_pos (rfl : z = z)]
      linear_combination mul_inv_cancel₀ hu0
    · rw [if_neg ha, hσz]
      show x1 (σ a) * (if a = z then (x1 a0)⁻¹ else 1) +
          x1 a0 * (if a = z then 0 else -(x1 (σ a) * (x1 a0)⁻¹)) = 0
      rw [if_neg ha, if_neg ha]
      linear_combination (-x1 (σ a)) * mul_inv_cancel₀ hu0
theorem oneRow : OneRow.{u} := one_row_bound
theorem thmB : ThmB.{u} := theorem_B
theorem sizesB : SizesB := by
  unfold SizesB
  intro H _ _ TT c wt wt' f k b b' hf hk hb hb' hc1 hc2 hw hw'
  have hf0 : 0 ≤ f := by
    have : (0:ℝ) ≤ (Fintype.card H : ℝ) := Nat.cast_nonneg _
    linarith
  constructor
  · have h1 : ∀ t, c t ≤ 4 * k * b' + (if t ∈ TT then 2 * b else 0) := by
      intro t
      by_cases ht : t ∈ TT
      · rw [if_pos ht]; exact hc2 t ht
      · rw [if_neg ht, add_zero]; exact hc1 t ht
    calc (∑ t, c t) ≤ ∑ t, (4 * k * b' + (if t ∈ TT then 2 * b else 0)) :=
          Finset.sum_le_sum (fun t _ => h1 t)
      _ = (Fintype.card H : ℝ) * (4 * k * b') + (TT.card : ℝ) * (2 * b) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_mem, Finset.univ_inter,
            Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ]
      _ = 2 * (TT.card : ℝ) * b + 2 * f * k * b' := by rw [hf]; ring
  · have hS0 : 0 ≤ ∑ t, min (wt t) (wt' t) :=
      Finset.sum_nonneg (fun t _ => le_min (hw t).1 (hw' t))
    have hS1 : ∑ t, min (wt t) (wt' t) ≤ f * b' := by
      calc ∑ t, min (wt t) (wt' t) ≤ ∑ _t : H, 2 * b' :=
            Finset.sum_le_sum (fun t _ => (min_le_left _ _).trans (hw t).2)
        _ = f * b' := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hf]; ring
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hS1), mul_nonneg hf0 hb',
        mul_nonneg (mul_nonneg hf0 hb') (by linarith : (0:ℝ) ≤ k + 1)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hk) hS0,
        mul_nonneg (mul_nonneg hf0 (by linarith : (0:ℝ) ≤ k)) hb']
theorem intOp : IntOp.{u} := by
  unfold IntOp
  intro K _ _ ι Th hTh P hP
  unfold jetPair
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
  intro κ _
  rw [mul_assoc, norm_mul]
  exact mul_le_one₀ (hP κ) (norm_nonneg _) (hTh κ)
private theorem norm_polar_le_one_of_norm_le_one {K : Type u} [NormedField K] [IsUltrametricDist K]
    {ι : Type} [Fintype ι] (c : ι → ι → K) (L L' : ι → K) (hc : ∀ x y, ‖c x y‖ ≤ 1)
    (hL : ∀ x, ‖L x‖ ≤ 1) (hL' : ∀ x, ‖L' x‖ ≤ 1) : ‖polar c L L'‖ ≤ 1 := by
  unfold polar
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun x _ => ?_)
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun y _ => ?_)
  rw [norm_mul]
  refine mul_le_one₀ (hc x y) (norm_nonneg _) ?_
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]; exact mul_le_one₀ (hL x) (norm_nonneg _) (hL' y)
  · rw [norm_mul]; exact mul_le_one₀ (hL y) (norm_nonneg _) (hL' x)

private theorem norm_coeff_prod_linForm_le_one {K : Type u} [NormedField K] [IsUltrametricDist K]
    {ι : Type} [Fintype ι] {n : ℕ} (L : Fin n → ι → K) (hL : ∀ i x, ‖L i x‖ ≤ 1)
    (s : Finset (Fin n)) : ∀ m, ‖MvPolynomial.coeff m (∏ i ∈ s, linForm (L i))‖ ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro m
    rw [Finset.prod_empty, MvPolynomial.coeff_one]
    split_ifs <;> simp
  | @insert a s ha ih =>
    intro m
    rw [Finset.prod_insert ha, MvPolynomial.coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun p _ => ?_)
    rw [norm_mul]
    refine mul_le_one₀ ?_ (norm_nonneg _) (ih p.2)
    unfold linForm
    rw [MvPolynomial.coeff_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one (fun x _ => ?_)
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X', norm_mul]
    refine mul_le_one₀ (hL a x) (norm_nonneg _) ?_
    split_ifs <;> simp

theorem matchBound : MatchBound.{u} := by
  unfold MatchBound
  intro K _ _ _ pi hpi0 hpi1 ι _ c S sg n L hc hS hsg hL M hM
  have hm : Matchings.{u} := matchings
  unfold Matchings at hm
  have hI : IntOp.{u} := intOp
  unfold IntOp at hI
  rw [hm K ι c S sg n L]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hpi0.le _) ?_
  intro σ hσ
  rw [Finset.mem_filter] at hσ
  by_cases hz : ∀ i, i < σ i → polar c (L i) (L (σ i)) ≠ 0
  · have hcard := hM σ hσ.2 hz
    rw [norm_mul, norm_prod]
    have hJ := hI K ι sg hsg _
      (norm_coeff_prod_linForm_le_one L hL (Finset.univ.filter (fun i => σ i = i)))
    have hP : ∏ i ∈ Finset.univ.filter (fun i => i < σ i), ‖-S * polar c (L i) (L (σ i))‖ ≤
        pi ^ (-(1 / 2 : ℝ) * ((Finset.univ.filter (fun i => i < σ i)).card : ℝ)) := by
      calc ∏ i ∈ Finset.univ.filter (fun i => i < σ i), ‖-S * polar c (L i) (L (σ i))‖
          ≤ ∏ _i ∈ Finset.univ.filter (fun i => i < σ i), pi ^ (-(1 / 2 : ℝ)) := by
            refine Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ?_)
            rw [norm_mul, norm_neg]
            calc ‖S‖ * ‖polar c (L i) (L (σ i))‖ ≤ ‖S‖ * 1 :=
                  mul_le_mul_of_nonneg_left
                    (norm_polar_le_one_of_norm_le_one c (L i) (L (σ i)) hc (hL i) (hL (σ i))) (norm_nonneg _)
              _ ≤ pi ^ (-(1 / 2 : ℝ)) := by rw [mul_one]; exact hS
        _ = pi ^ (-(1 / 2 : ℝ) * ((Finset.univ.filter (fun i => i < σ i)).card : ℝ)) := by
            rw [Finset.prod_const, Real.rpow_mul hpi0.le, Real.rpow_natCast]
    have hmono : pi ^ (-(1 / 2 : ℝ) * ((Finset.univ.filter (fun i => i < σ i)).card : ℝ)) ≤
        pi ^ (-(1 / 2 : ℝ) * (M : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_ge hpi0 hpi1.le
      have : ((Finset.univ.filter (fun i => i < σ i)).card : ℝ) ≤ (M : ℝ) := by
        exact_mod_cast hcard
      linarith
    refine (mul_le_mul hP hJ (norm_nonneg _) (Real.rpow_nonneg hpi0.le _)).trans ?_
    rw [mul_one]
    exact hmono
  · push_neg at hz
    obtain ⟨i, hi, hpol⟩ := hz
    have h0 : (∏ i ∈ Finset.univ.filter (fun i => i < σ i), (-S * polar c (L i) (L (σ i)))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩) (by rw [hpol, mul_zero])
    rw [h0, zero_mul, norm_zero]
    exact Real.rpow_nonneg hpi0.le _
theorem sizesE : SizesE := by
  unfold SizesE
  intro H _ _ TT c wt wt' f k b b' hf hk hb hb' hc0 hc1 hc2 hw hw'
  have hB : SizesB := sizesB
  unfold SizesB at hB
  obtain ⟨hsum, habs⟩ := hB H TT c wt wt' f k b b' hf hk hb hb' hc1 hc2 hw hw'
  have hf0 : 0 ≤ f := by
    have : (0:ℝ) ≤ (Fintype.card H : ℝ) := Nat.cast_nonneg _
    linarith
  have hC0 : 0 ≤ ∑ t, c t := Finset.sum_nonneg (fun t _ => hc0 t)
  have hT0 : (0:ℝ) ≤ (TT.card : ℝ) * b := mul_nonneg (Nat.cast_nonneg _) hb
  have hF0 : 0 ≤ f * k * b' := mul_nonneg (mul_nonneg hf0 (by linarith)) hb'
  rw [abs_le] at habs ⊢
  obtain ⟨h1, h2⟩ := habs
  constructor <;> linarith
theorem thmBGauss : ThmBGauss := theorem_B_gauss_sums

end Formalism.DworkPowerSeriesWeights
