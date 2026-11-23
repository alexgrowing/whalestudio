import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds

open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate

namespace Formalism.HermitianLatticeCounting.P

theorem sesqFormSumExpansion : CommonLiftExpand := by
  intro V _ _ h r e e' l₁ l₂ α α' h1 h2
  have hA : ∀ x, h (∑ a, α a • e a) x = ∑ a, α a * h (e a) x := by
    intro x
    simp [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  have hB : ∀ x, h x (∑ b, α' b • e' b) = ∑ b, conj (α' b) * h x (e' b) := by
    intro x
    simp [map_sum, map_smulₛₗ]
  simp only [map_add, LinearMap.add_apply, hA, hB, h1, h2, mul_zero, Finset.sum_const_zero,
    zero_add, add_zero, Finset.mul_sum, mul_assoc]

theorem hermitianDefectBaseChange : PhiBaseChange := by
  intro n R _ _ _ _ S Y g hg
  have h1 : ∀ X : Matrix n n R, g⁻¹ * (g * X) = X := by
    intro X; rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul g hg, Matrix.one_mul]
  have h2 : ∀ X : Matrix n n R, gᴴ * ((g⁻¹)ᴴ * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul g hg,
      Matrix.conjTranspose_one, Matrix.one_mul]
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.Phi
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, h1, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem hermitianDefectConjTranspose : PhiInverse := by
  intro n R _ _ _ _ S Y hS hD
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.Phi at *
  have e1 : (1 + S * Yᴴ) * (1 + S * Y) = 1 := by
    have : (1 + S * Yᴴ) * (1 + S * Y) = 1 + S * (Y + Yᴴ + Yᴴ * S * Y) := by noncomm_ring
    rw [this, hD, Matrix.mul_zero, add_zero]
  have e2 : (1 + S * Y) * (1 + S * Yᴴ) = 1 := by
    rw [← Matrix.inv_eq_right_inv e1]
    exact Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse e1)
  have e3 : S * (Yᴴ + Y + Y * S * Yᴴ) = 0 := by
    have : S * (Yᴴ + Y + Y * S * Yᴴ) = (1 + S * Y) * (1 + S * Yᴴ) - 1 := by noncomm_ring
    rw [this, e2, sub_self]
  have key : Yᴴ + Y + Y * S * Yᴴ =
      (Y + Yᴴ + Yᴴ * S * Y) * (1 + S * Yᴴ) - Yᴴ * (S * (Yᴴ + Y + Y * S * Yᴴ)) := by
    noncomm_ring
  rw [Matrix.conjTranspose_conjTranspose, key, hD, e3]
  simp

theorem hyperbolicRatioSqLe : ChShSq := by
  intro sh ch hsh hch hc
  constructor
  · intro h1
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (ch - 1), mul_le_mul h1 h1 zero_le_one hsh.le]
  · intro h1
    nlinarith [sq_nonneg (ch - 1), mul_pos hsh (sub_pos.mpr h1)]

theorem prodMaxLeProdMaxDiv : PThreshold := by
  intro ι _ x H hH hx
  have hH0 : 0 < H := by linarith
  rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro v _; exact zero_le_one.trans (le_max_left _ _)
  · intro v _
    have e : H * (x v / H) = x v := by field_simp
    rw [mul_max_of_nonneg _ _ hH0.le, mul_one, e]
    exact max_le_max hH le_rfl

theorem powSubOneIdentities : PowSubOneIdentities := by
  intro T k f hT hk
  have hT1 : (1:ℝ) < T := by exact_mod_cast (by omega : 1 < T)
  have hTk : (0:ℝ) < (T:ℝ) ^ k := by positivity
  constructor
  · rw [mul_comm f k, pow_mul, ← mul_pow, mul_sub, mul_one, mul_inv_cancel₀ hTk.ne']
  · have key : (T:ℝ) ^ (k - 1) ≤ ((T:ℝ) ^ k - 1) / ((T:ℝ) - 1) := by
      rw [le_div_iff₀ (by linarith)]
      have e : (T:ℝ) ^ k = (T:ℝ) ^ (k - 1) * T := by
        rw [← pow_succ]; congr 1; omega
      rw [e]
      nlinarith [one_le_pow₀ hT1.le (n := k - 1)]
    rw [← pow_mul, mul_comm f (k - 1), pow_mul]
    exact pow_le_pow_left₀ (by positivity) key f

theorem eichlerTransformIsometry : EichlerIsometry := by
  intro R V _ _ _ _ h hh u σ τ huu huσ hτ x y
  have hσu : h σ u = 0 := by rw [hh u σ, huσ, star_zero]
  have e1 : h u y = star (h y u) := hh y u
  have e2 : h σ y = star (h y σ) := hh y σ
  simp only [map_sub, map_add, map_smul, map_smulₛₗ, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, huu, huσ, hσu, e1, e2, star_mul',
    star_sub, star_add, mul_zero, zero_mul, sub_zero, add_zero]
  linear_combination (-(h x u) * star (h y u)) * hτ

theorem powLeMaxMulMax : BlockScalarBound := by
  intro t x y s c ht hx hy hcs hts
  have hM : 1 ≤ max 1 x * max 1 (1 / y) :=
    one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)
  rcases le_or_gt 1 t with h1 | h1
  · calc t ^ c ≤ t ^ s := pow_le_pow_right₀ h1 hcs
      _ = x * (1 / y) := by rw [hts, div_eq_mul_one_div]
      _ ≤ max 1 x * max 1 (1 / y) :=
          mul_le_mul (le_max_right _ _) (le_max_right _ _) (by positivity)
            (zero_le_one.trans (le_max_left _ _))
  · calc t ^ c ≤ 1 := pow_le_one₀ ht.le h1.le
      _ ≤ _ := hM

private theorem one_le_finset_prod_of_forall_one_le {ι : Type*} (s : Finset ι) (y : ι → ℝ) (h : ∀ v ∈ s, 1 ≤ y v) :
    1 ≤ ∏ v ∈ s, y v := by
  calc (1:ℝ) = ∏ v ∈ s, (1:ℝ) := by simp
    _ ≤ ∏ v ∈ s, y v := Finset.prod_le_prod (fun _ _ => zero_le_one) h

theorem ratioPowLeProdMaxPow : Threshold := by
  intro N p D H₂ l hH hD hDl hlt
  have hQ1 : 1 < D l / H₂ := by rw [lt_div_iff₀ hH, one_mul]; exact hlt
  have hN : (0:ℝ) < N := Nat.cast_pos.mpr (Fin.pos l)
  have hN0 : (N:ℝ) ≠ 0 := hN.ne'
  have hP1 : 1 ≤ ∏ i, max 1 (D i / H₂) := one_le_finset_prod_of_forall_one_le _ _ (fun i _ => le_max_left _ _)
  have hPpos : 0 < ∏ i, max 1 (D i / H₂) := lt_of_lt_of_le one_pos hP1
  have hPQ : ∏ i, max 1 (D i / H₂) ≤ (D l / H₂) ^ N := by
    calc ∏ i, max 1 (D i / H₂) ≤ ∏ _i : Fin N, D l / H₂ :=
          Finset.prod_le_prod (fun _ _ => zero_le_one.trans (le_max_left _ _))
            (fun i _ => max_le hQ1.le (div_le_div_of_nonneg_right (hDl i) hH.le))
      _ = (D l / H₂) ^ N := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have ha : 0 ≤ 2 * (p:ℝ) / N := by positivity
  rw [Real.rpow_neg hPpos.le]
  have h2 : (∏ i, max 1 (D i / H₂)) ^ (2 * (p:ℝ) / N) ≤ (D l / H₂) ^ (2 * p) := by
    calc (∏ i, max 1 (D i / H₂)) ^ (2 * (p:ℝ) / N) ≤ ((D l / H₂) ^ N) ^ (2 * (p:ℝ) / N) :=
          Real.rpow_le_rpow hPpos.le hPQ ha
      _ = (D l / H₂) ^ (2 * p) := by
          rw [← Real.rpow_natCast (D l / H₂) N, ← Real.rpow_mul (by linarith),
            show (N:ℝ) * (2 * p / N) = ((2 * p : ℕ) : ℝ) by push_cast; field_simp,
            Real.rpow_natCast]
  calc (H₂ / D l) ^ (2 * p) = ((D l / H₂) ^ (2 * p))⁻¹ := by rw [← inv_pow, inv_div]
    _ ≤ ((∏ i, max 1 (D i / H₂)) ^ (2 * (p:ℝ) / N))⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos hPpos _) h2

theorem oneLeProdInfinitePlace : IntegerProductGeOne := by
  intro E _ _ a ha
  rw [NumberField.InfinitePlace.prod_eq_abs_norm, ← Algebra.coe_norm_int]
  have h : Algebra.norm ℤ a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
  have : (1:ℤ) ≤ |Algebra.norm ℤ a| := Int.one_le_abs h
  exact_mod_cast this

theorem centralTransvectionIsometry : CentreIsometry := by
  intro R V _ _ _ _ h hh r e c he hc x y
  have hc' : ∀ a a', star (c a a') = - c a' a := by
    intro a a'
    have := congrFun (congrFun hc a') a
    simpa [Matrix.conjTranspose_apply] using this
  have hL : ∀ (k : Fin r → Fin r → R) (z : V),
      h (∑ a, ∑ a', k a a' • e a) z = ∑ a, ∑ a', k a a' * h (e a) z := by
    intro k z; simp [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  have hR : ∀ (k : Fin r → Fin r → R) (z : V),
      h z (∑ a, ∑ a', k a a' • e a) = ∑ a, ∑ a', star (k a a') * h z (e a) := by
    intro k z; simp [map_sum, map_smulₛₗ, starRingEnd_apply]
  have hy : ∀ a, h (e a) y = star (h y (e a)) := fun a => hh y (e a)
  simp only [map_add, LinearMap.add_apply, hL, hR, he, hy, mul_zero, Finset.sum_const_zero,
    add_zero]
  have key : ∑ a, ∑ a', star (c a a' * h y (e a')) * h x (e a) =
      - ∑ a, ∑ a', c a a' * h x (e a') * star (h y (e a)) := by
    simp only [star_mul', hc']
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro a' _; ring
  linear_combination key

theorem hermitianDefectMulUnit : PhiUnit := by
  intro n R _ _ _ _ S Y
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.Phi
  noncomm_ring

theorem hermitianDefectConj : PhiGram := by
  intro n R _ _ _ _ S Y hS
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.Phi
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, hS]
  noncomm_ring

theorem hermitianDefectAdd : PhiDiff := by
  intro n R _ _ _ _ S Y Z hS
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.Phi
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_one,
    Matrix.conjTranspose_conjTranspose, hS]
  noncomm_ring

theorem hermitianDefectComposition : PhiProduct := by
  intro n R _ _ _ _ S Y Y' hS
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.Phi
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_one,
    Matrix.conjTranspose_conjTranspose, hS]
  noncomm_ring

theorem absMulLeWeightedMean : WeightedAMGM := by
  intro a b La hLa
  have hL0 : La ≠ 0 := hLa.ne'
  obtain ⟨t, ht⟩ : ∃ t, t = |b| / La := ⟨_, rfl⟩
  have hbt : |b| = La * t := by rw [ht]; first | (field_simp; ring) | field_simp
  have hb2 : b ^ 2 = La ^ 2 * t ^ 2 := by rw [← sq_abs b, hbt]; ring
  have hb2' : b ^ 2 / La = La * t ^ 2 := by
    rw [hb2, div_eq_iff hL0]; ring
  rw [abs_mul, hbt, hb2', ← sq_abs a]
  nlinarith [mul_nonneg hLa.le (sq_nonneg (|a| - t))]

theorem minLeSqrtMul : MinGeom := by
  intro a b ha hb
  have hm : 0 ≤ min a b := le_min ha hb
  have h2 : min a b ^ 2 ≤ a * b := by
    rw [sq]; exact mul_le_mul (min_le_left _ _) (min_le_right _ _) hm ha
  calc min a b = Real.sqrt (min a b ^ 2) := (Real.sqrt_sq hm).symm
    _ ≤ Real.sqrt (a * b) := Real.sqrt_le_sqrt h2

theorem rpowMulRpowNegLe : SizeCancel := by
  intro sz e q hsz hq
  rw [← Real.rpow_add (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hsz (by linarith)

theorem traceLowerBound : TraceLower := by
  intro ι _ a ha hprod
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hn | hn
  · rw [hn, Nat.cast_zero]; exact Finset.sum_nonneg (fun v _ => ha v)
  · have hn' : (0:ℝ) < Fintype.card ι := by exact_mod_cast hn
    have amgm := Real.geom_mean_le_arith_mean Finset.univ (fun _ => (1:ℝ)) a
      (fun _ _ => zero_le_one) (by simpa using hn') (fun v _ => ha v)
    simp only [Real.rpow_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one] at amgm
    have h1 : 1 ≤ (∏ v, a v) ^ ((Fintype.card ι : ℝ))⁻¹ :=
      Real.one_le_rpow hprod (by positivity)
    have := h1.trans amgm
    rwa [le_div_iff₀ hn', one_mul] at this

lemma one_le_finset_prod_real_of_forall_one_le {ι : Type*} (s : Finset ι) (y : ι → ℝ) (h : ∀ v ∈ s, 1 ≤ y v) :
    1 ≤ ∏ v ∈ s, y v := one_le_finset_prod_of_forall_one_le s y h

private theorem finset_prod_real_mono_of_subset_of_one_le {ι : Type*} (s t : Finset ι) (hst : s ⊆ t) (y : ι → ℝ)
    (h : ∀ v ∈ t, 1 ≤ y v) : ∏ v ∈ s, y v ≤ ∏ v ∈ t, y v := by
  classical
  rw [← Finset.prod_sdiff hst]
  have h1 : 1 ≤ ∏ v ∈ t \ s, y v :=
    one_le_finset_prod_of_forall_one_le _ _ (fun v hv => h v (Finset.mem_sdiff.mp hv).1)
  have h2 : 0 ≤ ∏ v ∈ s, y v :=
    Finset.prod_nonneg (fun v hv => zero_le_one.trans (h v (hst hv)))
  exact le_mul_of_one_le_left h2 h1

lemma finset_prod_le_prod_of_subset_of_one_le {ι : Type*} (s t : Finset ι) (hst : s ⊆ t) (y : ι → ℝ)
    (h : ∀ v ∈ t, 1 ≤ y v) : ∏ v ∈ s, y v ≤ ∏ v ∈ t, y v := finset_prod_real_mono_of_subset_of_one_le s t hst y h

private theorem finset_prod_max_one_nonneg {ι : Type*} (s : Finset ι) (y : ι → ℝ) :
    0 ≤ ∏ v ∈ s, max 1 (y v) :=
  Finset.prod_nonneg (fun _ _ => zero_le_one.trans (le_max_left _ _))

private theorem max_self_inv_le_max_one_mul_max_one_inv {x : ℝ} (hx : 0 < x) :
    max x (1 / x) ≤ max 1 x * max 1 (1 / x) := by
  have h0 : 0 ≤ max 1 (1 / x) := zero_le_one.trans (le_max_left _ _)
  apply max_le
  · calc x ≤ max 1 x := le_max_right _ _
      _ = max 1 x * 1 := (mul_one _).symm
      _ ≤ max 1 x * max 1 (1 / x) := mul_le_mul_of_nonneg_left (le_max_left _ _)
          (zero_le_one.trans (le_max_left _ _))
  · exact (le_max_right 1 (1 / x)).trans (le_mul_of_one_le_left h0 (le_max_left _ _))

theorem prodMaxInvLeSq : LemmaP := by
  intro ι _ x Sg hx hprod
  have hA : ∏ v, max 1 (1 / x v) ≤ ∏ v, max 1 (x v) := by
    have e : ∏ v, max 1 (x v) = (∏ v, x v) * ∏ v, max 1 (1 / x v) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro v _
      rw [mul_max_of_nonneg _ _ (hx v).le, mul_one, mul_one_div_cancel (hx v).ne']
      exact max_comm _ _
    rw [e]
    exact le_mul_of_one_le_left (finset_prod_max_one_nonneg _ _) hprod
  have hB : ∏ v ∈ Sg, max 1 (1 / x v) ≤ ∏ v, max 1 (1 / x v) :=
    finset_prod_real_mono_of_subset_of_one_le _ _ (Finset.subset_univ _) _ (fun v _ => le_max_left _ _)
  refine ⟨?_, hB.trans hA⟩
  calc ∏ v ∈ Sg, max (x v) (1 / x v) ≤ ∏ v ∈ Sg, (max 1 (x v) * max 1 (1 / x v)) :=
        Finset.prod_le_prod (fun v _ => (hx v).le.trans (le_max_left _ _))
          (fun v _ => max_self_inv_le_max_one_mul_max_one_inv (hx v))
    _ = (∏ v ∈ Sg, max 1 (x v)) * ∏ v ∈ Sg, max 1 (1 / x v) := Finset.prod_mul_distrib
    _ ≤ (∏ v, max 1 (x v)) * ∏ v, max 1 (x v) :=
        mul_le_mul (finset_prod_real_mono_of_subset_of_one_le _ _ (Finset.subset_univ _) _ (fun v _ => le_max_left _ _))
          (hB.trans hA) (finset_prod_max_one_nonneg _ _) (finset_prod_max_one_nonneg _ _)
    _ = (∏ v, max 1 (x v)) ^ 2 := (sq _).symm

lemma thresholdSize_eq_prod_comm {ι l : Type*} [Fintype ι] (E : Finset l) (D : l → ι → ℝ) (H₂ : ℝ) :
    size E D H₂ = ∏ i ∈ E, ∏ v, max 1 (D i v / H₂) := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.size
  exact Finset.prod_comm

lemma prod_prod_max_le_pow_mul_thresholdSize {ι l : Type} [Fintype ι] (E : Finset l) (D : l → ι → ℝ) (H₂ : ℝ) (hH : 1 ≤ H₂)
    (hD : ∀ i ∈ E, ∀ v, 0 < D i v) :
    ∏ i ∈ E, ∏ v, max 1 (D i v) ≤ H₂ ^ (Fintype.card ι * E.card) * size E D H₂ := by
  have h1 : ∀ i ∈ E, ∏ v, max 1 (D i v) ≤ H₂ ^ Fintype.card ι * ∏ v, max 1 (D i v / H₂) :=
    fun i hi => prodMaxLeProdMaxDiv ι (D i) H₂ hH (fun v => (hD i hi v).le)
  calc ∏ i ∈ E, ∏ v, max 1 (D i v)
        ≤ ∏ i ∈ E, (H₂ ^ Fintype.card ι * ∏ v, max 1 (D i v / H₂)) :=
        Finset.prod_le_prod (fun i _ => finset_prod_max_one_nonneg _ _) h1
    _ = H₂ ^ (Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul, thresholdSize_eq_prod_comm]

theorem prodMaxMulMaxInvLe : PiProd := by
  intro ι l _ E D H₂ hH hD hprod
  rw [Finset.prod_comm]
  have h1 : ∀ i ∈ E, ∏ v, (max 1 (D i v) * max 1 (1 / D i v)) ≤ (∏ v, max 1 (D i v)) ^ 2 := by
    intro i hi
    rw [Finset.prod_mul_distrib, sq]
    exact mul_le_mul_of_nonneg_left (prodMaxInvLeSq ι (D i) Finset.univ (hD i hi) (hprod i hi)).2
      (finset_prod_max_one_nonneg _ _)
  have hH0 : 0 ≤ H₂ := by linarith
  calc ∏ i ∈ E, ∏ v, (max 1 (D i v) * max 1 (1 / D i v))
        ≤ ∏ i ∈ E, (∏ v, max 1 (D i v)) ^ 2 :=
        Finset.prod_le_prod (fun i _ => Finset.prod_nonneg (fun v _ => mul_nonneg
          (zero_le_one.trans (le_max_left _ _)) (zero_le_one.trans (le_max_left _ _)))) h1
    _ = (∏ i ∈ E, ∏ v, max 1 (D i v)) ^ 2 := Finset.prod_pow _ _ _
    _ ≤ (H₂ ^ (Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂) ^ 2 :=
        pow_le_pow_left₀ (Finset.prod_nonneg (fun _ _ => finset_prod_max_one_nonneg _ _))
          (prod_prod_max_le_pow_mul_thresholdSize E D H₂ hH hD) 2
    _ = H₂ ^ (2 * Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂ ^ 2 := by ring

private theorem LatticeSumBounds_size_nonneg {ι l : Type*} [Fintype ι] (E : Finset l) (D : l → ι → ℝ) (H₂ : ℝ) :
    0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂ :=
  Finset.prod_nonneg (fun _ _ => finset_prod_max_one_nonneg _ _)

theorem prodLossBound : LossProd := by
  classical
  intro ι l _ E D G B H₂ e₁ e₂ l₀ Sg hB hH hl₀ hD hDprod hG hGprod hGD
  have hB0 : 0 ≤ B := by linarith
  have hH0 : 0 ≤ H₂ := by linarith
  have hthr := LatticeSumBounds_size_nonneg E D H₂
  have P1 : ∏ _v ∈ Sg, B ≤ B ^ Fintype.card ι := by
    rw [Finset.prod_const]; exact pow_le_pow_right₀ hB (Finset.card_le_univ Sg)
  have hT : ∏ v, max 1 (D l₀ v) ≤ H₂ ^ Fintype.card ι * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂ := by
    refine (prodMaxLeProdMaxDiv ι (D l₀) H₂ hH (fun v => (hD l₀ hl₀ v).le)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hH0 _)
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.size
    apply Finset.prod_le_prod (fun v _ => zero_le_one.trans (le_max_left _ _))
    intro v _
    rw [← Finset.mul_prod_erase E _ hl₀]
    exact le_mul_of_one_le_right (zero_le_one.trans (le_max_left _ _))
      (one_le_finset_prod_of_forall_one_le _ _ (fun i _ => le_max_left _ _))
  have hGm : ∏ v, max 1 (G v) ≤ (∏ v, max 1 (D l₀ v)) ^ 2 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_le_prod (fun v _ => zero_le_one.trans (le_max_left _ _))
    intro v _
    exact max_le (one_le_pow₀ (le_max_left _ _))
      ((hGD v).trans (pow_le_pow_left₀ (hD l₀ hl₀ v).le (le_max_right _ _) 2))
  have P2 : ∏ v ∈ Sg, max (G v) (1 / G v) ^ e₁ ≤
      (H₂ ^ Fintype.card ι * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂) ^ (4 * e₁) := by
    rw [Finset.prod_pow, pow_mul (H₂ ^ Fintype.card ι * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂) 4 e₁]
    apply pow_le_pow_left₀ (Finset.prod_nonneg (fun v _ => (hG v).le.trans (le_max_left _ _)))
    calc ∏ v ∈ Sg, max (G v) (1 / G v) ≤ (∏ v, max 1 (G v)) ^ 2 :=
          (prodMaxInvLeSq ι G Sg hG hGprod).1
      _ ≤ ((∏ v, max 1 (D l₀ v)) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (finset_prod_max_one_nonneg _ _) hGm 2
      _ ≤ ((H₂ ^ Fintype.card ι * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (by positivity)
            (pow_le_pow_left₀ (finset_prod_max_one_nonneg _ _) hT 2) 2
      _ = (H₂ ^ Fintype.card ι * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂) ^ 4 := by ring
  have P3 : ∏ v ∈ Sg, ∏ i ∈ E, max (D i v) (1 / D i v) ^ e₂ ≤
      (H₂ ^ (Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂) ^ (2 * e₂) := by
    simp only [Finset.prod_pow]
    rw [pow_mul (H₂ ^ (Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂) 2 e₂]
    apply pow_le_pow_left₀ (Finset.prod_nonneg (fun v _ => Finset.prod_nonneg
      (fun i hi => (hD i hi v).le.trans (le_max_left _ _))))
    calc ∏ v ∈ Sg, ∏ i ∈ E, max (D i v) (1 / D i v)
          ≤ ∏ v ∈ Sg, ∏ i ∈ E, (max 1 (D i v) * max 1 (1 / D i v)) := by
          apply Finset.prod_le_prod (fun v _ => Finset.prod_nonneg
            (fun i hi => (hD i hi v).le.trans (le_max_left _ _)))
          intro v _
          exact Finset.prod_le_prod (fun i hi => (hD i hi v).le.trans (le_max_left _ _))
            (fun i hi => max_self_inv_le_max_one_mul_max_one_inv (hD i hi v))
      _ ≤ ∏ v, ∏ i ∈ E, (max 1 (D i v) * max 1 (1 / D i v)) :=
          finset_prod_real_mono_of_subset_of_one_le _ _ (Finset.subset_univ _) _ (fun v _ => one_le_finset_prod_of_forall_one_le _ _
            (fun i _ => one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)))
      _ ≤ H₂ ^ (2 * Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂ ^ 2 :=
          prodMaxMulMaxInvLe ι l E D H₂ hH hD hDprod
      _ = (H₂ ^ (Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂) ^ 2 := by ring
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  exact mul_le_mul (mul_le_mul P1 P2
      (Finset.prod_nonneg (fun v _ => pow_nonneg ((hG v).le.trans (le_max_left _ _)) _))
      (pow_nonneg hB0 _)) P3
    (Finset.prod_nonneg (fun v _ => Finset.prod_nonneg
      (fun i hi => pow_nonneg ((hD i hi v).le.trans (le_max_left _ _)) _)))
    (mul_nonneg (pow_nonneg hB0 _) (pow_nonneg (mul_nonneg (pow_nonneg hH0 _) hthr) _))

theorem hyperbolicRatioLe : ChShBound := by
  intro sh ch hsh hch hc
  have hch2 : ch ≤ sh + 1 := by nlinarith
  rcases le_or_gt 1 sh with h1 | h1
  · calc (1 + ch) / sh ≤ 3 := by rw [div_le_iff₀ hsh]; linarith
      _ ≤ 3 * max 1 (1 / sh) := by have := le_max_left 1 (1 / sh); linarith
  · have hc2 : ch ≤ 2 := by nlinarith
    calc (1 + ch) / sh ≤ 3 / sh := div_le_div_of_nonneg_right (by linarith) hsh.le
      _ = 3 * (1 / sh) := by ring
      _ ≤ 3 * max 1 (1 / sh) := by have := le_max_right 1 (1 / sh); linarith

theorem hyperbolicPairRatioLe : ChShPair := by
  intro sh₁ ch₁ sh₂ ch₂ h1 hc1 e1 h2 hc2 e2
  have key : ∀ sh ch : ℝ, 0 < sh → 0 ≤ ch → ch ^ 2 = sh ^ 2 + 1 → ch * min 1 sh ≤ 2 * sh := by
    intro sh ch hs hc e
    rcases le_or_gt 1 sh with h | h
    · rw [min_eq_left h, mul_one]; nlinarith
    · rw [min_eq_right h.le]
      have hc2 : ch ≤ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hc2 hs.le
  have m1 : 0 < min 1 sh₁ := lt_min one_pos h1
  have m2 : 0 < min 1 sh₂ := lt_min one_pos h2
  have k1 := key sh₁ ch₁ h1 hc1 e1
  have k2 := key sh₂ ch₂ h2 hc2 e2
  have l1 : min 1 sh₁ ≤ sh₁ := min_le_right _ _
  have l2 : min 1 sh₂ ≤ sh₂ := min_le_right _ _
  rw [div_le_iff₀ (mul_pos h1 h2), div_mul_eq_mul_div, le_div_iff₀ (mul_pos m1 m2)]
  nlinarith [mul_le_mul_of_nonneg_right k1 m2.le, mul_le_mul_of_nonneg_right k2 m1.le,
    mul_le_mul_of_nonneg_left l2 h1.le, mul_le_mul_of_nonneg_left l1 h2.le]

theorem expSumLe : ExpSumLe := by
  intro x hx
  have hE : Real.exp (-x / 6) * Real.exp (x / 6) = 1 := by
    rw [← Real.exp_add, show -x / 6 + x / 6 = (0:ℝ) by ring, Real.exp_zero]
  have h3 : 3 ≤ Real.exp (x / 6) := by linarith [Real.add_one_le_exp (x / 6)]
  have hpos := Real.exp_pos (-x / 6)
  have hA : Real.exp (-x / 6) ≤ 1 / 3 := by nlinarith
  have hsplit : Real.exp (-x / 2) = Real.exp (-x / 3) * Real.exp (-x / 6) := by
    rw [← Real.exp_add]; congr 1; ring
  have t1 : Real.exp (-4 * x) ≤ Real.exp (-x / 2) := Real.exp_le_exp.mpr (by linarith)
  have t2 : Real.exp (-x) ≤ Real.exp (-x / 2) := Real.exp_le_exp.mpr (by linarith)
  have hp3 := Real.exp_pos (-x / 3)
  have hm := mul_le_mul_of_nonneg_left hA hp3.le
  linarith

theorem invSqrtPowLeExp : GainSqrt := by
  intro k f b g hk hb hg
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0:ℝ) < k := by linarith
  have hk4pos : (0:ℝ) < (k:ℝ) ^ 4 := pow_pos hkpos 4
  have h8 : ((k:ℝ) ^ 4) ^ 2 ≤ g := by
    calc ((k:ℝ) ^ 4) ^ 2 = (k:ℝ) ^ 8 := by ring
      _ ≤ ((k:ℝ) * b) ^ 8 := pow_le_pow_left₀ hkpos.le (by nlinarith) 8
      _ ≤ g := hg
  have hk4 : (k:ℝ) ^ 4 ≤ Real.sqrt g := by
    calc (k:ℝ) ^ 4 = Real.sqrt (((k:ℝ) ^ 4) ^ 2) := (Real.sqrt_sq hk4pos.le).symm
      _ ≤ Real.sqrt g := Real.sqrt_le_sqrt h8
  have hinv : (Real.sqrt g)⁻¹ ≤ ((k:ℝ) ^ 4)⁻¹ := inv_anti₀ hk4pos hk4
  have e4 : Real.exp (4 * Real.log k) = (k:ℝ) ^ 4 := by
    rw [show (4:ℝ) * Real.log k = Real.log ((k:ℝ) ^ 4) by rw [Real.log_pow]; norm_num,
      Real.exp_log hk4pos]
  have heq : Real.exp (-4 * ((k:ℝ) * f * Real.log k)) = (((k:ℝ) ^ 4)⁻¹) ^ (k * f) := by
    rw [show -4 * ((k:ℝ) * f * Real.log k) = ((k * f : ℕ) : ℝ) * (-(4 * Real.log k)) by
      push_cast; try ring, Real.exp_nat_mul, Real.exp_neg, e4]
  rw [heq]
  exact pow_le_pow_left₀ (by positivity) hinv _

theorem powTwoDivLeExpLog : GainQuadratic := by
  intro k N b g hk hb hg
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hb0 : 0 < b := by linarith
  have hb7 : 0 < b ^ 7 := pow_pos hb0 7
  have hb8 : b ^ 8 ≤ g := le_trans (pow_le_pow_left₀ hb0.le (by nlinarith) 8) hg
  have hg0 : 0 < g := lt_of_lt_of_le (pow_pos hb0 8) hb8
  have h1 : 2 / g ≤ (b ^ 7)⁻¹ := by
    rw [div_le_iff₀ hg0]
    have e8 : b ^ 8 = b ^ 7 * b := by ring
    have h27 : b ^ 7 * 2 ≤ g := by nlinarith
    calc (2:ℝ) = (b ^ 7)⁻¹ * (b ^ 7 * 2) := (inv_mul_cancel_left₀ hb7.ne' 2).symm
      _ ≤ (b ^ 7)⁻¹ * g := mul_le_mul_of_nonneg_left h27 (by positivity)
  have e7 : Real.exp (7 * Real.log b) = b ^ 7 := by
    rw [show (7:ℝ) * Real.log b = Real.log (b ^ 7) by rw [Real.log_pow]; norm_num,
      Real.exp_log hb7]
  have heq : Real.exp (-7 * N * Real.log b) = ((b ^ 7)⁻¹) ^ N := by
    rw [show -7 * (N:ℝ) * Real.log b = (N:ℝ) * (-(7 * Real.log b)) by ring, Real.exp_nat_mul,
      Real.exp_neg, e7]
  rw [heq]
  exact pow_le_pow_left₀ (by positivity) h1 N

theorem volumeExponentAssembly : SWArith := by
  intro k f de₀ G₀ NT v cf hk hde hdG hNT hv hcf
  have hde0 : 0 < de₀ := by linarith
  have hG0 : 0 < G₀ := by linarith
  have hNT0 : 0 < NT := by linarith
  have hde' : de₀ ≠ 0 := hde0.ne'
  have hNT' : NT ≠ 0 := hNT0.ne'
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Real.rpow_add (div_pos hG0 hde0), Real.rpow_natCast]
  have hX0 : 0 ≤ (Real.exp 1 * Real.pi / (((j + 1 : ℕ) : ℝ) * v)) ^ ((j + 1) * f) := by positivity
  have hc : (G₀ / de₀) ^ cf ≤ G₀ ^ cf := Real.rpow_le_rpow (by positivity) (div_le_self hG0.le hde) hcf
  have hc0 : 0 ≤ (G₀ / de₀) ^ cf := by positivity
  have key : (de₀ / NT) ^ j * (G₀ / de₀) ^ (j + 1) = (G₀ / NT) ^ (j + 1) * NT / de₀ := by
    rw [div_pow, div_pow, div_pow, div_mul_div_comm, div_mul_eq_mul_div, div_div,
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  have hle : (G₀ / NT) ^ (j + 1) * NT / de₀ ≤ (G₀ / NT) ^ (j + 1) * NT :=
    div_le_self (by positivity) hde
  calc _ = ((de₀ / NT) ^ j * (G₀ / de₀) ^ (j + 1)) * (G₀ / de₀) ^ cf *
        (Real.exp 1 * Real.pi / (((j + 1 : ℕ) : ℝ) * v)) ^ ((j + 1) * f) := by ring
    _ = (G₀ / NT) ^ (j + 1) * NT / de₀ * (G₀ / de₀) ^ cf *
        (Real.exp 1 * Real.pi / (((j + 1 : ℕ) : ℝ) * v)) ^ ((j + 1) * f) := by rw [key]
    _ ≤ (G₀ / NT) ^ (j + 1) * NT * G₀ ^ cf *
        (Real.exp 1 * Real.pi / (((j + 1 : ℕ) : ℝ) * v)) ^ ((j + 1) * f) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hle hc hc0 (by positivity)) hX0
    _ = _ := by ring

theorem divPowMulPowLe : DivPowMulPowLe := by
  intro k de₀ j₀ t₁ t₂ De NT cf hde hj ht1 ht2 hNT hcf hDe
  have hde0 : 0 < de₀ := by linarith
  have hP1 : 1 ≤ j₀ * t₁ * t₂ :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hj ht1) ht2
  have hP0 : 0 < j₀ * t₁ * t₂ := by linarith
  have hPDe : j₀ * t₁ * t₂ ≤ De := by nlinarith
  have hDe0 : 0 < De := by linarith
  rw [Real.rpow_add hP0, Real.rpow_natCast]
  have h1 : (de₀ / NT) ^ k * (j₀ * t₁ * t₂) ^ k ≤ (De / NT) ^ k := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by nlinarith) hNT.le
  have h2 : (j₀ * t₁ * t₂) ^ cf ≤ De ^ cf := Real.rpow_le_rpow hP0.le hPDe hcf
  calc _ = ((de₀ / NT) ^ k * (j₀ * t₁ * t₂) ^ k) * (j₀ * t₁ * t₂) ^ cf := by ring
    _ ≤ (De / NT) ^ k * De ^ cf := mul_le_mul h1 h2 (by positivity) (by positivity)

theorem relIndexMonotone : SublatticeIndex := by
  intro A _ M Th La hML hne
  exact ⟨fun h => hne (AddSubgroup.relIndex_eq_zero_of_le_right hML h),
    AddSubgroup.relIndex_le_of_le_right hML hne⟩

theorem minBoundSecondZero : MinIIZero := by
  intro k r CT G T T' g v t loss JHS dim hr hk hG hT hT' hg hv ht hloss hdim hCT hkt hVF
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hg0 : 0 < g := by linarith
  have hg' : g ≠ 0 := hg0.ne'
  have hgp : 0 < g ^ (2 * r + 2) := pow_pos hg0 _
  have hkk : (k:ℝ) ≤ (k:ℝ) ^ (3 * r) := by
    calc (k:ℝ) = (k:ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (k:ℝ) ^ (3 * r) := pow_le_pow_right₀ hk1 (by omega)
  have h1 : (k:ℝ) ^ (3 * r) * g ^ (2 * r + 2) ≤ T' * t := by
    calc (k:ℝ) ^ (3 * r) * g ^ (2 * r + 2)
          ≤ (g⁻¹ ^ (2 * r + 2) * T' * t) * g ^ (2 * r + 2) :=
          mul_le_mul_of_nonneg_right hkt hgp.le
      _ = T' * t := by
          rw [show g⁻¹ ^ (2 * r + 2) * T' * t * g ^ (2 * r + 2) =
            (g ^ (2 * r + 2))⁻¹ * g ^ (2 * r + 2) * (T' * t) by ring, inv_mul_cancel₀ hgp.ne', one_mul]
  have hkey : (k:ℝ) * g ^ (2 * r + 2) ≤ T' * t :=
    (mul_le_mul_of_nonneg_right hkk hgp.le).trans h1
  have hCT' : T' ≤ CT * T := by rwa [div_le_iff₀ hT] at hCT
  have htT : 0 < t * T := mul_pos ht hT
  have hbase : (t * T)⁻¹ ≤ CT / (k * g ^ (2 * r + 2)) := by
    rw [le_div_iff₀ (mul_pos hk0 hgp)]
    calc (t * T)⁻¹ * (k * g ^ (2 * r + 2)) ≤ (t * T)⁻¹ * (CT * T * t) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (inv_nonneg.mpr htT.le)
      _ = CT := by
          rw [show CT * T * t = (t * T) * CT by ring, ← mul_assoc, inv_mul_cancel₀ htT.ne',
            one_mul]
  have hTi : 0 ≤ T⁻¹ ^ k := by positivity
  calc Formalism.HermitianLatticeCounting.LatticeSumBounds.nv k r G T g v * JHS ^ 2 * T⁻¹ ^ k / dim
        = (Formalism.HermitianLatticeCounting.LatticeSumBounds.nv k r G T g v * JHS ^ 2 / dim) * T⁻¹ ^ k := by ring
    _ ≤ (loss * t⁻¹ ^ k) * T⁻¹ ^ k := mul_le_mul_of_nonneg_right hVF hTi
    _ = loss * ((t * T)⁻¹) ^ k := by ring
    _ ≤ loss * (CT / (k * g ^ (2 * r + 2))) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase k) hloss

lemma gainExponent_nonneg (k r : ℕ) : 0 ≤ expo k r := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.expo
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma gainExponent_le (k r : ℕ) (hk : 1 ≤ k) : expo k r ≤ 2 * r := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.expo
  rw [div_le_iff₀ hk0]
  have h : 2 * r * (k - 2 - r) ≤ 2 * r * k := Nat.mul_le_mul_left _ (by omega)
  calc ((2 * r * (k - 2 - r) : ℕ) : ℝ) ≤ ((2 * r * k : ℕ) : ℝ) := by exact_mod_cast h
    _ = 2 * r * k := by push_cast; try ring

theorem minGainBaseLe : XTilde := by
  intro k r C ν T' t g hk hC hν hT' ht hg hkt
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hk0 : (0:ℝ) < k := by linarith
  rcases le_or_gt ν T' with h | h
  · rw [min_eq_left h]; exact min_le_right _ _
  · rw [min_eq_right h.le]
    apply (min_le_left _ _).trans
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.xv
    have hge : 0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.expo k r := gainExponent_nonneg k r
    have hle : Formalism.HermitianLatticeCounting.LatticeSumBounds.expo k r ≤ 2 * r := gainExponent_le k r (by omega)
    have h1 : ((k:ℝ) ^ (2 * r))⁻¹ ≤ (C / k) ^ Formalism.HermitianLatticeCounting.LatticeSumBounds.expo k r := by
      calc ((k:ℝ) ^ (2 * r))⁻¹ = (1 / (k:ℝ)) ^ ((2 * r : ℕ) : ℝ) := by
            rw [Real.rpow_natCast, one_div, inv_pow]
        _ ≤ (1 / (k:ℝ)) ^ Formalism.HermitianLatticeCounting.LatticeSumBounds.expo k r :=
            Real.rpow_le_rpow_of_exponent_ge (one_div_pos.mpr hk0)
              (by rw [div_le_one hk0]; exact hk1) (by push_cast; exact hle)
        _ ≤ (C / k) ^ Formalism.HermitianLatticeCounting.LatticeSumBounds.expo k r :=
            Real.rpow_le_rpow (one_div_pos.mpr hk0).le
              (div_le_div_of_nonneg_right hC hk0.le) hge
    have h2 : 1 ≤ (k:ℝ) ^ (3 * r) * ((k:ℝ) ^ (2 * r))⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hk0 _), one_mul]
      exact pow_le_pow_right₀ hk1 (by omega)
    calc (1:ℝ) ≤ (k:ℝ) ^ (3 * r) * ((k:ℝ) ^ (2 * r))⁻¹ := h2
      _ ≤ (g⁻¹ ^ (2 * r + 2) * T' * t) * (C / k) ^ Formalism.HermitianLatticeCounting.LatticeSumBounds.expo k r :=
          mul_le_mul hkt h1 (inv_nonneg.mpr (pow_nonneg hk0.le _)) (by positivity)
      _ = T' * t * g⁻¹ ^ (2 * r + 2) * (C / k) ^ Formalism.HermitianLatticeCounting.LatticeSumBounds.expo k r := by ring

lemma Icc_eq_Ico_add_one (a b : ℕ) : Finset.Icc a b = Finset.Ico a (b + 1) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_Ico]
  constructor <;> intro h <;> omega

theorem unitaryOrderRatioIdentity : ThetaRatio := by
  intro j e η q hej hq
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.theta
  obtain ⟨m, rfl⟩ : ∃ m, j = m + e := ⟨j - e, by omega⟩
  have hm : m + e - e = m := by omega
  rw [hm]
  simp only [Icc_eq_Ico_add_one]
  rw [← Finset.prod_Ico_consecutive _ (show 1 ≤ m + 1 by omega)
    (show m + 1 ≤ m + e + 1 by omega)]
  ring

theorem unitaryOrderRatioBound : ThetaBound := by
  intro j e η q hej hq hη
  have hfac : ∀ i ∈ Finset.Icc (j - e + 1) j,
      0 < 1 - η ^ i * (q ^ i)⁻¹ ∧ 1 - η ^ i * (q ^ i)⁻¹ ≤ 3 / 2 := by
    intro i hi
    have hi1 : 1 ≤ i := by simp only [Finset.mem_Icc] at hi; omega
    have hqi : 2 ≤ q ^ i := by
      calc (2:ℝ) ≤ q := hq
        _ = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ i := pow_le_pow_right₀ (by linarith) hi1
    have hx0 : 0 < (q ^ i)⁻¹ := inv_pos.mpr (by linarith)
    have hx : (q ^ i)⁻¹ ≤ 1 / 2 := by
      have := inv_anti₀ (by norm_num : (0:ℝ) < 2) hqi
      linarith [show (2:ℝ)⁻¹ = 1 / 2 by norm_num]
    have hs : η ^ i = 1 ∨ η ^ i = -1 := by
      rcases hη with rfl | rfl
      · left; exact one_pow i
      · exact neg_one_pow_eq_or ℝ i
    rcases hs with h | h <;> rw [h] <;> constructor <;> linarith
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.theta
  have hcard : (Finset.Icc (j - e + 1) j).card = e := by rw [Nat.card_Icc]; omega
  have hle : ∏ i ∈ Finset.Icc (j - e + 1) j, (1 - η ^ i * (q ^ i)⁻¹) ≤ (3 / 2) ^ e := by
    calc ∏ i ∈ Finset.Icc (j - e + 1) j, (1 - η ^ i * (q ^ i)⁻¹)
          ≤ ∏ _i ∈ Finset.Icc (j - e + 1) j, (3 / 2 : ℝ) :=
          Finset.prod_le_prod (fun i hi => (hfac i hi).1.le) (fun i hi => (hfac i hi).2)
      _ = (3 / 2) ^ e := by rw [Finset.prod_const, hcard]
  refine ⟨Finset.prod_pos (fun i hi => (hfac i hi).1), hle, hle.trans ?_⟩
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) e

theorem massRatioIdentity : XiIdentity := by
  intro mass mj k s hmj hm2 hrec hs hk
  have step : ∀ a n, 2 ≤ a → mass (a + n) = mass a * ∏ i ∈ Finset.Ioc a (a + n), mj i := by
    intro a n ha
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, Finset.prod_Ioc_succ_top (show a ≤ a + n by omega),
        hrec (a + n + 1) (by omega), Nat.add_sub_cancel, ih]
      ring
  have pos : ∀ n, 2 ≤ n → 0 < mass n := by
    intro n hn
    obtain ⟨d, rfl⟩ : ∃ d, n = 2 + d := ⟨n - 2, by omega⟩
    rw [step 2 d le_rfl]
    exact mul_pos hm2 (Finset.prod_pos (fun i _ => hmj i))
  have h1 : mass s = mass 2 * ∏ i ∈ Finset.Ioc 2 s, mj i := by
    obtain ⟨d, rfl⟩ : ∃ d, s = 2 + d := ⟨s - 2, by omega⟩
    exact step 2 d le_rfl
  have h2 : mass k = mass (k - s) * ∏ i ∈ Finset.Ioc (k - s) k, mj i := by
    have := step (k - s) s (by omega)
    rwa [Nat.sub_add_cancel (by omega)] at this
  have hks := pos (k - s) (by omega)
  have hP : 0 < ∏ i ∈ Finset.Ioc (k - s) k, mj i := Finset.prod_pos (fun i _ => hmj i)
  rw [h2, h1, div_eq_div_iff (mul_pos hks hP).ne' hP.ne']
  ring

theorem piPowDivFactorialLt : PiPowFactorial := by
  intro k hk
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
  rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega]
  have key : ∀ m : ℕ, (3.15:ℝ) ^ (m + 3 + 1) ≤ 17 * ((m + 3).factorial : ℝ) := by
    intro m
    induction m with
    | zero => norm_num [Nat.factorial]
    | succ m ih =>
      rw [show m + 1 + 3 = (m + 3) + 1 by ring, Nat.factorial_succ, pow_succ]
      push_cast at ih ⊢
      have hf : (0:ℝ) ≤ ((m + 3).factorial : ℝ) := Nat.cast_nonneg _
      nlinarith [mul_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m) hf]
  have bound : (3.15:ℝ) ^ (n + 1) ≤ 17 * (n.factorial : ℝ) := by
    rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with h | h | h
    · subst h; norm_num [Nat.factorial]
    · subst h; norm_num [Nat.factorial]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      exact key m
  have hlt : Real.pi ^ (n + 1) < (3.15:ℝ) ^ (n + 1) :=
    pow_lt_pow_left₀ hπ hπ0.le (Nat.succ_ne_zero n)
  rw [div_lt_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos n))]
  linarith

theorem invFactorialLeStirling : StirlingInv := by
  intro k hk
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hst := Stirling.sqrt_pi_le_stirlingSeq (show k ≠ 0 by omega)
  unfold Stirling.stirlingSeq at hst
  have hπ := Real.pi_pos
  have ha0 : 0 < (Real.exp 1 / k) ^ k := by positivity
  have hka : ((k:ℝ) / Real.exp 1) ^ k = ((Real.exp 1 / k) ^ k)⁻¹ := by
    rw [← inv_pow, inv_div]
  rw [hka] at hst
  have hs0 : 0 < Real.sqrt (2 * k) * ((Real.exp 1 / k) ^ k)⁻¹ := by positivity
  rw [le_div_iff₀ hs0] at hst
  have hF : ((k - 1).factorial : ℝ) = (k.factorial : ℝ) / k := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul,
      mul_div_cancel_left₀ _ (by positivity : ((m + 1 : ℕ) : ℝ) ≠ 0)]
  rw [hF, one_div, inv_div, div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos k))]
  have hsq : Real.sqrt (k / (2 * Real.pi)) * (Real.sqrt Real.pi * Real.sqrt (2 * k)) = k := by
    rw [← Real.sqrt_mul hπ.le, ← Real.sqrt_mul (by positivity)]
    rw [show (k:ℝ) / (2 * Real.pi) * (Real.pi * (2 * k)) = (k:ℝ) ^ 2 by
      rw [div_mul_eq_mul_div, div_eq_iff (by positivity)]; ring]
    exact Real.sqrt_sq hk0.le
  calc (k:ℝ) = Real.sqrt (k / (2 * Real.pi)) * (Real.sqrt Real.pi * Real.sqrt (2 * k)) := hsq.symm
    _ = ((Real.exp 1 / k) ^ k * ((Real.exp 1 / k) ^ k)⁻¹) *
          (Real.sqrt (k / (2 * Real.pi)) * (Real.sqrt Real.pi * Real.sqrt (2 * k))) := by
        rw [mul_inv_cancel₀ ha0.ne', one_mul]
    _ = (Real.exp 1 / k) ^ k * Real.sqrt (k / (2 * Real.pi)) *
          (Real.sqrt Real.pi * (Real.sqrt (2 * k) * ((Real.exp 1 / k) ^ k)⁻¹)) := by ring
    _ ≤ (Real.exp 1 / k) ^ k * Real.sqrt (k / (2 * Real.pi)) * (k.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left hst (by positivity)

lemma gainBase_pow (k r : ℕ) (C ν t g : ℝ) (hk : 1 ≤ k) (hC : 0 < C) :
    (xv k r C ν t g) ^ k =
      ν ^ k * t ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * (C / k) ^ (2 * r * (k - 2 - r)) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.xv Formalism.HermitianLatticeCounting.LatticeSumBounds.expo
  rw [mul_pow, mul_pow, mul_pow,
    ← Real.rpow_natCast ((C / (k:ℝ)) ^ (((2 * r * (k - 2 - r) : ℕ) : ℝ) / (k:ℝ))) k,
    ← Real.rpow_mul (by positivity), div_mul_cancel₀ _ hk0.ne', Real.rpow_natCast]

lemma volumeFactor_eq (k r : ℕ) (G T g v : ℝ) :
    nv k r G T g v =
      (Real.exp 1 * Real.pi / (k * v)) ^ k * (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.nv
  rw [← mul_pow, ← mul_pow]
  congr 1
  ring

lemma volumeFactor_mul_sq_div_le (k r : ℕ) (C G T g v Dr loss' JHS Jop dim : ℝ) (hk : 1 ≤ k)
    (hC : 0 < C) (hG : 0 < G) (hT : 0 < T) (hg : 0 < g) (hv : 0 < v) (hDr : 0 < Dr)
    (hdim : 0 < dim) (hJop : 0 ≤ Jop)
    (hABS : Jop ≤ loss' * (C / (k * v)) ^ (r * (k - 2 - r)) * Dr⁻¹ ^ (k - 2 - r))
    (hrank : JHS ^ 2 ≤ dim * Jop ^ 2) :
    nv k r G T g v * JHS ^ 2 / dim ≤
      (Real.exp 1 * Real.pi / (k * v)) ^ k * (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k *
        (loss' ^ 2 * (C / (k * v)) ^ (2 * r * (k - 2 - r)) *
          Dr⁻¹ ^ (2 * (k - 2 - r))) := by
  have hVF : 0 ≤ (Real.exp 1 * Real.pi / (k * v)) ^ k * (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k := by
    positivity
  have h1 : JHS ^ 2 / dim ≤ Jop ^ 2 := by rw [div_le_iff₀ hdim]; nlinarith
  have h2 : Jop ^ 2 ≤ (loss' * (C / (k * v)) ^ (r * (k - 2 - r)) * Dr⁻¹ ^ (k - 2 - r)) ^ 2 :=
    pow_le_pow_left₀ hJop hABS 2
  have h3 : (loss' * (C / (k * v)) ^ (r * (k - 2 - r)) * Dr⁻¹ ^ (k - 2 - r)) ^ 2 =
      loss' ^ 2 * (C / (k * v)) ^ (2 * r * (k - 2 - r)) * Dr⁻¹ ^ (2 * (k - 2 - r)) := by ring
  rw [volumeFactor_eq k r G T g v]
  calc _ = (Real.exp 1 * Real.pi / (k * v)) ^ k * (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k *
        (JHS ^ 2 / dim) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (h1.trans (h2.trans h3.le)) hVF

theorem minBoundFirst' : MinI' := by
  intro k r C G T g v t Dr loss loss' JHS Jop dim hk hC hG hT hg hv ht hDr hl' hdim hJop hJHS
    hAV hloss hVF hABS hrank
  have hk1 : 1 ≤ k := by omega
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlossp : 0 < loss := lt_of_lt_of_le (pow_pos hDr _) hloss
  have hmain := volumeFactor_mul_sq_div_le k r C G T g v Dr loss' JHS Jop dim hk1 hC hG hT hg hv
    hDr hdim hJop hABS hrank
  rcases le_total 1 (Formalism.HermitianLatticeCounting.LatticeSumBounds.xv k r C (G / (T * Dr ^ 2)) t g) with h | h
  · rw [min_eq_left h, one_pow, mul_one]
    calc _ ≤ loss * t⁻¹ ^ k := hVF
      _ = loss * 1 * t⁻¹ ^ k := by ring
      _ ≤ loss * loss' ^ 2 * t⁻¹ ^ k :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (one_le_pow₀ hl') hlossp.le)
            (by positivity)
  · rw [min_eq_right h, gainBase_pow k r C (G / (T * Dr ^ 2)) t g hk1 hC]
    have eG : (G / (T * Dr ^ 2)) ^ k = (G / T) ^ k * Dr⁻¹ ^ (2 * k) := by
      rw [pow_mul Dr⁻¹ 2 k, ← mul_pow]; congr 1; ring
    have et : t⁻¹ ^ k * t ^ k = 1 := by rw [← mul_pow, inv_mul_cancel₀ ht.ne', one_pow]
    rw [eG]
    set s := k - 2 - r with hs
    have hks : 2 * k = 2 * s + (2 * r + 4) := by omega
    have eCv : (C / (k * v)) ^ (2 * r * s) = (C / k) ^ (2 * r * s) * v⁻¹ ^ (2 * r * s) := by
      rw [← mul_pow]; congr 1; ring
    have hone : Dr ^ (2 * r + 4) * Dr⁻¹ ^ (2 * r + 4) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hDr.ne', one_pow]
    have eDi : Dr⁻¹ ^ (2 * s) = Dr ^ (2 * r + 4) * Dr⁻¹ ^ (2 * k) := by
      rw [hks, pow_add]
      linear_combination (-(Dr⁻¹ ^ (2 * s))) * hone
    have hZ : 0 ≤ (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 * (C / k) ^ (2 * r * s) *
        Dr⁻¹ ^ (2 * k) := by positivity
    have hAVD : (Real.exp 1 * Real.pi / (k * v)) ^ k * v⁻¹ ^ (2 * r * s) * Dr ^ (2 * r + 4) ≤
        loss := by
      calc _ ≤ 1 * Dr ^ (2 * r + 4) := mul_le_mul_of_nonneg_right hAV (by positivity)
        _ ≤ loss := by rw [one_mul]; exact hloss
    calc _ ≤ _ := hmain
      _ = ((Real.exp 1 * Real.pi / (k * v)) ^ k * v⁻¹ ^ (2 * r * s) * Dr ^ (2 * r + 4)) *
          ((G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 * (C / k) ^ (2 * r * s) *
            Dr⁻¹ ^ (2 * k)) := by rw [eCv, eDi]; ring
      _ ≤ loss * ((G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 * (C / k) ^ (2 * r * s) *
            Dr⁻¹ ^ (2 * k)) := mul_le_mul_of_nonneg_right hAVD hZ
      _ = loss * loss' ^ 2 * t⁻¹ ^ k * ((G / T) ^ k * Dr⁻¹ ^ (2 * k) * t ^ k *
            (g⁻¹ ^ (2 * r + 2)) ^ k * (C / k) ^ (2 * r * s)) := by
          linear_combination (-(loss * (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 *
            (C / k) ^ (2 * r * s) * Dr⁻¹ ^ (2 * k))) * et

theorem minBoundFirst : MinI := by
  intro k r C G T g v t Dr loss loss' JHS Jop dim hk hC hG hT hg hv ht hDr hl' hdim hJop hJHS
    heπ hloss hVF hABS hrank
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hv0 : 0 < v := by linarith
  have h1 : Real.exp 1 * Real.pi / (k * v) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have h2 : v⁻¹ ≤ 1 := by have := inv_anti₀ one_pos hv; simpa using this
  have hAV : (Real.exp 1 * Real.pi / (k * v)) ^ k * v⁻¹ ^ (2 * r * (k - 2 - r)) ≤ 1 := by
    calc _ ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (by positivity) h1) (pow_le_one₀ (by positivity) h2)
          (by positivity) zero_le_one
      _ = 1 := one_mul 1
  exact minBoundFirst' k r C G T g v t Dr loss loss' JHS Jop dim (by omega) hC hG hT hg hv0 ht hDr
    hl' hdim hJop hJHS hAV hloss hVF hABS hrank

theorem minBoundSecond' : MinII' := by
  intro k r C CT G T T' g v t Dr sh ch loss loss' JHS Jop dim hr hk hC hG hT hT' hg hv ht hDr hl'
    hdim hJop hJHS hAV hloss hsh hch hc hGeq hCT hkt hVF hABS hrank
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hg0 : 0 < g := by linarith
  have hlossp : 0 < loss := lt_of_lt_of_le (pow_pos hDr _) hloss
  have hCTp : 0 < CT := lt_of_lt_of_le (div_pos hT' hT) hCT
  have heπ : 1 ≤ Real.exp 1 * Real.pi := by
    have := Real.add_one_le_exp 1
    have := Real.pi_gt_three
    nlinarith
  have hratio := hyperbolicRatioSqLe sh ch hsh hch hc
  rcases le_or_gt 1 sh with h1 | h1
  · have hz := minBoundSecondZero k r CT G T T' g v t loss JHS dim hr (by omega) hG hT hT' hg hv ht
      hlossp.le hdim hCT hkt hVF
    have h6 : ((1 + ch) / sh) ^ (2 * k) ≤ 6 ^ k := by
      rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) (hratio.1 h1) k
    calc _ = (Formalism.HermitianLatticeCounting.LatticeSumBounds.nv k r G T g v * JHS ^ 2 * T⁻¹ ^ k / dim) * ((1 + ch) / sh) ^ (2 * k) := by
          ring
      _ ≤ (loss * (CT / (k * g ^ (2 * r + 2))) ^ k) * 6 ^ k :=
          mul_le_mul hz h6 (by positivity) (by positivity)
      _ = loss * (6 * CT / (k * g ^ (2 * r + 2))) ^ k := by ring
      _ ≤ loss * loss' ^ 2 * (6 * Real.exp 1 * Real.pi * CT / (k * g ^ (2 * r + 2))) ^ k := by
          apply mul_le_mul (le_mul_of_one_le_right hlossp.le (one_le_pow₀ hl')) _ (by positivity)
            (by positivity)
          apply pow_le_pow_left₀ (by positivity)
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith
  · have h6 : (1 + ch) ^ 2 ≤ 6 := hratio.2 h1
    obtain ⟨q, hq⟩ : ∃ q, q = 1 + ch := ⟨_, rfl⟩
    rw [← hq] at h6 ⊢
    have hmain := volumeFactor_mul_sq_div_le k r C G T g v Dr loss' JHS Jop dim (by omega) hC hG hT
      hg0 hv hDr hdim hJop hABS hrank
    set s := k - 2 - r with hs
    have hks : 2 * k = 2 * s + (2 * r + 4) := by omega
    have hDD : Dr⁻¹ ^ (2 * s) * Dr ^ (2 * k) = Dr ^ (2 * r + 4) := by
      have hone : Dr⁻¹ ^ (2 * s) * Dr ^ (2 * s) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hDr.ne', one_pow]
      rw [hks, pow_add, ← mul_assoc, hone, one_mul]
    have hW : 0 ≤ (q / sh) ^ (2 * k) * T⁻¹ ^ k :=
      mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) k) (by positivity)
    have hT0 : T ≠ 0 := hT.ne'
    have hsh0 : sh ≠ 0 := hsh.ne'
    have hv0 : v ≠ 0 := hv.ne'
    have hk0 : (k:ℝ) ≠ 0 := hkR.ne'
    have hg00 : g ≠ 0 := hg0.ne'
    have hDr0 : Dr ≠ 0 := hDr.ne'
    calc _ = (Formalism.HermitianLatticeCounting.LatticeSumBounds.nv k r G T g v * JHS ^ 2 / dim) * ((q / sh) ^ (2 * k) * T⁻¹ ^ k) := by
          ring
      _ ≤ ((Real.exp 1 * Real.pi / (k * v)) ^ k * (G / T) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k *
            (loss' ^ 2 * (C / (k * v)) ^ (2 * r * s) * Dr⁻¹ ^ (2 * s))) *
            ((q / sh) ^ (2 * k) * T⁻¹ ^ k) := mul_le_mul_of_nonneg_right hmain hW
      _ = (Real.exp 1 * Real.pi / k) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 *
            (v⁻¹ ^ k * (C / (k * v)) ^ (2 * r * s)) * (q ^ 2) ^ k * (T' / T) ^ k *
            (Dr⁻¹ ^ (2 * s) * Dr ^ (2 * k)) := by
          have hTk : T ^ k * T⁻¹ ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hT0, one_pow]
          have hsk : sh ^ (2 * k) * sh⁻¹ ^ (2 * k) = 1 := by
            rw [← mul_pow, mul_inv_cancel₀ hsh0, one_pow]
          rw [hGeq]
          linear_combination ((Real.exp 1 * Real.pi / k) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 *
            (v⁻¹ ^ k * (C / (k * v)) ^ (2 * r * s)) * (q ^ 2) ^ k * (T' / T) ^ k *
            (Dr⁻¹ ^ (2 * s) * Dr ^ (2 * k)) * (sh ^ (2 * k) * sh⁻¹ ^ (2 * k))) * hTk +
            ((Real.exp 1 * Real.pi / k) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 *
            (v⁻¹ ^ k * (C / (k * v)) ^ (2 * r * s)) * (q ^ 2) ^ k * (T' / T) ^ k *
            (Dr⁻¹ ^ (2 * s) * Dr ^ (2 * k))) * hsk
      _ ≤ (Real.exp 1 * Real.pi / k) ^ k * (g⁻¹ ^ (2 * r + 2)) ^ k * loss' ^ 2 * 1 * 6 ^ k *
            CT ^ k * loss := by
          rw [hDD]
          gcongr
          all_goals first | assumption | positivity | skip
      _ = loss * loss' ^ 2 * (6 * Real.exp 1 * Real.pi * CT / (k * g ^ (2 * r + 2))) ^ k := by
          ring

theorem minBoundSecond : MinII := by
  intro k r C CT G T T' g v t Dr sh ch loss loss' JHS Jop dim hr hk hC hCk hG hT hT' hg hv ht hDr
    hl' hdim hJop hJHS hloss hsh hch hc hGeq hCT hkt hVF hABS hrank
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hv0 : 0 < v := by linarith
  have h1 : C / (k * v) ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
  have h2 : v⁻¹ ≤ 1 := by have := inv_anti₀ one_pos hv; simpa using this
  have hAV : v⁻¹ ^ k * (C / (k * v)) ^ (2 * r * (k - 2 - r)) ≤ 1 := by
    calc _ ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (by positivity) h2) (pow_le_one₀ (by positivity) h1)
          (by positivity) zero_le_one
      _ = 1 := one_mul 1
  exact minBoundSecond' k r C CT G T T' g v t Dr sh ch loss loss' JHS Jop dim hr hk hC hG hT hT' hg
    hv0 ht hDr hl' hdim hJop hJHS hAV hloss hsh hch hc hGeq hCT hkt hVF hABS hrank

theorem nondegenerateRowBound : NonDegRow := by
  intro k f s g v NT G₁ G₂ Xi W count A₁ A₂ l₁ l₂ τ hk hs hg hv hNT hG₁ hG₂ hXi hW hA₁ hA₂ hτ
    hcount h₁ h₂
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.nTot at h₁ h₂
  obtain ⟨E, hE⟩ : ∃ E, E = (Real.exp 1 * Real.pi / (k * v)) ^ (k * f) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; positivity
  have hE' : E ≠ 0 := hE0.ne'
  rw [← hE] at h₁ h₂
  obtain ⟨a, ha⟩ : ∃ x, x = Real.sqrt (G₁ / NT) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ x, x = Real.sqrt (G₂ / NT) := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have ha2 : a ^ 2 = G₁ / NT := by rw [ha, Real.sq_sqrt (by positivity)]
  have hb2 : b ^ 2 = G₂ / NT := by rw [hb, Real.sq_sqrt (by positivity)]
  have hab : Real.sqrt (G₁ * G₂) / NT = a * b := by
    rw [ha, hb, ← Real.sqrt_mul (div_nonneg hG₁.le hNT.le),
      show G₁ / NT * (G₂ / NT) = (G₁ * G₂) / NT ^ 2 by ring,
      Real.sqrt_div (mul_nonneg hG₁.le hG₂.le), Real.sqrt_sq hNT.le]
  obtain ⟨u₁, hu₁⟩ : ∃ x, x = A₁ * a ^ k := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ x, x = A₂ * b ^ k := ⟨_, rfl⟩
  have hu₁0 : 0 ≤ u₁ := by rw [hu₁]; positivity
  have hu₂0 : 0 ≤ u₂ := by rw [hu₂]; positivity
  have hl1 : E * u₁ ^ 2 ≤ l₁ * τ := by
    have e : E * u₁ ^ 2 = E * (G₁ / NT) ^ k * A₁ ^ 2 := by rw [hu₁, ← ha2]; ring
    rw [e]; exact h₁
  have hl2 : E * u₂ ^ 2 ≤ l₂ * τ := by
    have e : E * u₂ ^ 2 = E * (G₂ / NT) ^ k * A₂ ^ 2 := by rw [hu₂, ← hb2]; ring
    rw [e]; exact h₂
  have hkey : E * (u₁ * u₂) ≤ Real.sqrt (l₁ * l₂) * τ := by
    have hprod : (E * (u₁ * u₂)) ^ 2 ≤ (l₁ * τ) * (l₂ * τ) := by
      have e : (E * (u₁ * u₂)) ^ 2 = (E * u₁ ^ 2) * (E * u₂ ^ 2) := by ring
      rw [e]
      exact mul_le_mul hl1 hl2 (by positivity) (le_trans (by positivity) hl1)
    have h0 : 0 ≤ E * (u₁ * u₂) := by positivity
    calc E * (u₁ * u₂) = Real.sqrt ((E * (u₁ * u₂)) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt ((l₁ * τ) * (l₂ * τ)) := Real.sqrt_le_sqrt hprod
      _ = Real.sqrt (l₁ * l₂ * τ ^ 2) := by congr 1; ring
      _ = Real.sqrt (l₁ * l₂) * τ := by rw [Real.sqrt_mul' _ (sq_nonneg τ), Real.sqrt_sq hτ]
  have hid : ((2 / g) ^ ((s - 1) * f) * Real.sqrt (G₁ * G₂) / NT) ^ k * Xi * W * (A₁ * A₂) =
      (2 / g) ^ ((s - 1) * k * f) * Xi * W * (u₁ * u₂) := by
    rw [mul_div_assoc, hab, hu₁, hu₂]; ring
  have hAA : 0 ≤ A₁ * A₂ := mul_nonneg hA₁ hA₂
  calc count * A₁ * A₂ = count * (A₁ * A₂) := by ring
    _ ≤ (((2 / g) ^ ((s - 1) * f) * Real.sqrt (G₁ * G₂) / NT) ^ k * Xi * W) * (A₁ * A₂) :=
        mul_le_mul_of_nonneg_right hcount hAA
    _ = (2 / g) ^ ((s - 1) * k * f) * Xi * W * (u₁ * u₂) := hid
    _ = (2 / g) ^ ((s - 1) * k * f) * Xi * W * E⁻¹ * (E * (u₁ * u₂)) := by
        rw [mul_assoc _ E⁻¹, inv_mul_cancel_left₀ hE']
    _ ≤ (2 / g) ^ ((s - 1) * k * f) * Xi * W * E⁻¹ * (Real.sqrt (l₁ * l₂) * τ) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (2 / g) ^ ((s - 1) * k * f) * (k * v / (Real.exp 1 * Real.pi)) ^ (k * f) *
          Xi * W * Real.sqrt (l₁ * l₂) * τ := by
        rw [hE, ← inv_pow, inv_div]; ring

theorem degenerateRowBound : DegRow := by
  intro k f s g v T NT G₁ G₂ K₁ K₂ Xi W count A₁ A₂ lam₁ lam₂ hk hs hg hv hT hNT hG₁ hG₂ hK₁ hK₂
    hXi hW hA₁ hA₂ hcount h₁ h₂
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.nTot at h₁ h₂
  obtain ⟨E, hE⟩ : ∃ E, E = (Real.exp 1 * Real.pi / (k * v)) ^ (k * f) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; positivity
  have hE' : E ≠ 0 := hE0.ne'
  rw [← hE] at h₁ h₂
  obtain ⟨a, ha⟩ : ∃ x, x = Real.sqrt (G₁ / NT) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ x, x = Real.sqrt (G₂ / NT) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ x, x = Real.sqrt T⁻¹ := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have ha2 : a ^ 2 = G₁ / NT := by rw [ha, Real.sq_sqrt (by positivity)]
  have hb2 : b ^ 2 = G₂ / NT := by rw [hb, Real.sq_sqrt (by positivity)]
  have hc2 : c ^ 2 = T⁻¹ := by rw [hc, Real.sq_sqrt (by positivity)]
  have hab : Real.sqrt (G₁ * G₂) / NT = a * b := by
    rw [ha, hb, ← Real.sqrt_mul (div_nonneg hG₁.le hNT.le),
      show G₁ / NT * (G₂ / NT) = (G₁ * G₂) / NT ^ 2 by ring,
      Real.sqrt_div (mul_nonneg hG₁.le hG₂.le), Real.sqrt_sq hNT.le]
  obtain ⟨u₁, hu₁⟩ : ∃ x, x = A₁ * a ^ k * K₁ ^ k * c ^ (k * f) := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ x, x = A₂ * b ^ k * K₂ ^ k * c ^ (k * f) := ⟨_, rfl⟩
  have hu₁0 : 0 ≤ u₁ := by rw [hu₁]; positivity
  have hu₂0 : 0 ≤ u₂ := by rw [hu₂]; positivity
  have hl1 : E * u₁ ^ 2 ≤ lam₁ := by
    have e : E * u₁ ^ 2 = E * (G₁ / NT) ^ k * A₁ ^ 2 * K₁ ^ (2 * k) * T⁻¹ ^ (k * f) := by
      rw [hu₁, ← ha2, ← hc2]; ring
    rw [e]; exact h₁
  have hl2 : E * u₂ ^ 2 ≤ lam₂ := by
    have e : E * u₂ ^ 2 = E * (G₂ / NT) ^ k * A₂ ^ 2 * K₂ ^ (2 * k) * T⁻¹ ^ (k * f) := by
      rw [hu₂, ← hb2, ← hc2]; ring
    rw [e]; exact h₂
  have hkey : E * (u₁ * u₂) ≤ Real.sqrt (lam₁ * lam₂) := by
    have hprod : (E * (u₁ * u₂)) ^ 2 ≤ lam₁ * lam₂ := by
      have e : (E * (u₁ * u₂)) ^ 2 = (E * u₁ ^ 2) * (E * u₂ ^ 2) := by ring
      rw [e]
      exact mul_le_mul hl1 hl2 (by positivity) (le_trans (by positivity) hl1)
    have h0 : 0 ≤ E * (u₁ * u₂) := by positivity
    calc E * (u₁ * u₂) = Real.sqrt ((E * (u₁ * u₂)) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt (lam₁ * lam₂) := Real.sqrt_le_sqrt hprod
  have hid : ((2 / g) ^ ((s - 2) * f) * Real.sqrt (G₁ * G₂) * T⁻¹ ^ f * K₁ * K₂ / NT) ^ k * Xi * W *
      (A₁ * A₂) = (2 / g) ^ ((s - 2) * k * f) * Xi * W * (u₁ * u₂) := by
    rw [show (2 / g) ^ ((s - 2) * f) * Real.sqrt (G₁ * G₂) * T⁻¹ ^ f * K₁ * K₂ / NT =
        (2 / g) ^ ((s - 2) * f) * (Real.sqrt (G₁ * G₂) / NT) * T⁻¹ ^ f * K₁ * K₂ by ring,
      hab, ← hc2, hu₁, hu₂]
    ring
  have hAA : 0 ≤ A₁ * A₂ := mul_nonneg hA₁ hA₂
  calc count * A₁ * A₂ = count * (A₁ * A₂) := by ring
    _ ≤ (((2 / g) ^ ((s - 2) * f) * Real.sqrt (G₁ * G₂) * T⁻¹ ^ f * K₁ * K₂ / NT) ^ k * Xi * W) *
          (A₁ * A₂) := mul_le_mul_of_nonneg_right hcount hAA
    _ = (2 / g) ^ ((s - 2) * k * f) * Xi * W * (u₁ * u₂) := hid
    _ = (2 / g) ^ ((s - 2) * k * f) * Xi * W * E⁻¹ * (E * (u₁ * u₂)) := by
        rw [mul_assoc _ E⁻¹, inv_mul_cancel_left₀ hE']
    _ ≤ (2 / g) ^ ((s - 2) * k * f) * Xi * W * E⁻¹ * Real.sqrt (lam₁ * lam₂) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (2 / g) ^ ((s - 2) * k * f) * (k * v / (Real.exp 1 * Real.pi)) ^ (k * f) *
          Xi * W * Real.sqrt (lam₁ * lam₂) := by
        rw [hE, ← inv_pow, inv_div]; ring

lemma div_pow_gainExponent_le (k r : ℕ) (C : ℝ) (hk : r + 2 ≤ k) (hC : 1 ≤ C) (h2 : 2 * C ^ 2 ≤ k)
    (hlog : ((r : ℝ) + 2) * Real.log k ≤ k / 6) : (C / k) ^ expo k r ≤ ((k : ℝ) ^ r)⁻¹ := by
  have hk2 : (2:ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
  have hk0 : (0:ℝ) < k := by linarith
  have hC0 : 0 < C := by linarith
  have hl2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlk : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) hk2
  have hlogC : 2 * Real.log C ≤ Real.log k - Real.log 2 := by
    have h := Real.log_le_log (by positivity) (show C ^ 2 ≤ (k:ℝ) / 2 by linarith)
    rw [Real.log_pow, Real.log_div hk0.ne' (by norm_num)] at h
    push_cast at h
    linarith
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos (div_pos hC0 hk0) _) (inv_pos.mpr (pow_pos hk0 r)),
    Real.log_rpow (div_pos hC0 hk0), Real.log_inv, Real.log_pow, Real.log_div hC0.ne' hk0.ne']
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.expo
  have hcast : ((2 * r * (k - 2 - r) : ℕ) : ℝ) = 2 * r * ((k:ℝ) - 2 - r) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (show r ≤ k - 2 by omega),
      Nat.cast_sub (show 2 ≤ k by omega)]
    push_cast; try ring
  rw [hcast]
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have hkr : (0:ℝ) ≤ (k:ℝ) - 2 - r := by
    have : ((r + 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at this; linarith
  have hx : ((r:ℝ) + 2) * Real.log 2 ≤ ((r:ℝ) + 2) * Real.log k :=
    mul_le_mul_of_nonneg_left hlk (by positivity)
  have hmain : ((r:ℝ) + 2) * Real.log k ≤ ((k:ℝ) - 2 - r) * Real.log 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hl2.le hk0.le]
  have hg0 : 0 ≤ 2 * (r:ℝ) * ((k:ℝ) - 2 - r) / k :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr0) hkr) hk0.le
  calc 2 * (r:ℝ) * ((k:ℝ) - 2 - r) / k * (Real.log C - Real.log k)
        ≤ 2 * (r:ℝ) * ((k:ℝ) - 2 - r) / k * ((Real.log k - Real.log 2) / 2 - Real.log k) :=
        mul_le_mul_of_nonneg_left (by linarith) hg0
    _ = -((r:ℝ) * (((k:ℝ) - 2 - r) * (Real.log k + Real.log 2))) / k := by ring
    _ ≤ -((r:ℝ) * Real.log k) := by
        rw [div_le_iff₀ hk0]
        nlinarith [mul_le_mul_of_nonneg_left hmain hr0]

theorem prodMinGainBaseLe : ProdMinX := by
  intro ι _ k r C C₁ C₂ T' g ν t hk hC h2 hlog hT' hg hν ht hkt hprodν hprodt
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hCk : (C / k) ^ Formalism.HermitianLatticeCounting.LatticeSumBounds.expo k r ≤ ((k:ℝ) ^ r)⁻¹ :=
    div_pow_gainExponent_le k r C hk hC h2 hlog
  have hpt : ∀ v, min 1 (Formalism.HermitianLatticeCounting.LatticeSumBounds.xv k r C (ν v) (t v) g) ≤
      min (ν v) T' * t v * (g⁻¹ ^ (2 * r + 2) * ((k:ℝ) ^ r)⁻¹) := by
    intro v
    refine (minGainBaseLe k r C (ν v) T' (t v) g hk hC (hν v) hT' (ht v) hg (hkt v)).trans ?_
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.xv
    have hm : 0 < min (ν v) T' := lt_min (hν v) hT'
    have h0 : 0 ≤ min (ν v) T' * t v * g⁻¹ ^ (2 * r + 2) :=
      mul_nonneg (mul_nonneg hm.le (ht v).le) (by positivity)
    calc min (ν v) T' * t v * g⁻¹ ^ (2 * r + 2) * (C / k) ^ Formalism.HermitianLatticeCounting.LatticeSumBounds.expo k r
          ≤ min (ν v) T' * t v * g⁻¹ ^ (2 * r + 2) * ((k:ℝ) ^ r)⁻¹ :=
          mul_le_mul_of_nonneg_left hCk h0
      _ = min (ν v) T' * t v * (g⁻¹ ^ (2 * r + 2) * ((k:ℝ) ^ r)⁻¹) := by ring
  have hnn : ∀ v, 0 ≤ min 1 (Formalism.HermitianLatticeCounting.LatticeSumBounds.xv k r C (ν v) (t v) g) := by
    intro v
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.xv
    have h1 := hν v
    have h3 := ht v
    exact le_min zero_le_one (mul_nonneg (mul_nonneg (mul_nonneg h1.le h3.le) (by positivity))
      (Real.rpow_nonneg (div_nonneg (by linarith) hk0.le) _))
  have hPmin : 0 ≤ ∏ v, min (ν v) T' :=
    Finset.prod_nonneg (fun v _ => (lt_min (hν v) hT').le)
  calc ∏ v, min 1 (Formalism.HermitianLatticeCounting.LatticeSumBounds.xv k r C (ν v) (t v) g)
        ≤ ∏ v, (min (ν v) T' * t v * (g⁻¹ ^ (2 * r + 2) * ((k:ℝ) ^ r)⁻¹)) :=
        Finset.prod_le_prod (fun v _ => hnn v) (fun v _ => hpt v)
    _ = (∏ v, min (ν v) T') * (∏ v, t v) *
          (g⁻¹ ^ (2 * r + 2) * ((k:ℝ) ^ r)⁻¹) ^ Fintype.card ι := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
    _ ≤ (C₁ * g) ^ Fintype.card ι * C₂ *
          (g⁻¹ ^ (2 * r + 2) * ((k:ℝ) ^ r)⁻¹) ^ Fintype.card ι := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul hprodν hprodt (Finset.prod_nonneg (fun v _ => (ht v).le))
          (hPmin.trans hprodν)
    _ = C₂ * (C₁ * g * g⁻¹ ^ (2 * r + 2) * ((k:ℝ) ^ r)⁻¹) ^ Fintype.card ι := by ring

theorem meanBoundAssembly : MeanBoundAssembly := by
  intro k s de NT lf massk masss massks massFlagLatticeZero mean nM nS mM mS Gl hsk hk hde hNT hlf hmk hms hmks
    hmean hnM hnS hmM hmS hGl hP hmM' hmS' hnM' hnS' hGl' hL0
  have hde0 : 0 < de := by linarith
  have hNT0 : 0 < NT := by linarith
  have hX0 : 0 < de * NT := mul_pos hde0 hNT0
  have hM0 : 0 < massk * NT ^ (k - 1) := by positivity
  have h1 : mean ≤ nM * nS * mM * mS * Gl / (massk * NT ^ (k - 1)) := by
    rw [le_div_iff₀ hM0]
    calc mean * (massk * NT ^ (k - 1)) ≤ mean * massFlagLatticeZero := mul_le_mul_of_nonneg_left hL0 hmean
      _ ≤ _ := hP
  have h2 : nM * nS * mM * mS * Gl ≤ de ^ (1 + lf) * (de * NT) ^ (2 + lf) *
      (massks * de ^ (k - s) * de ^ (s + 1)) * (masss * (de * NT) ^ (2 * s)) *
      (de * NT) ^ (4 * (2 * s + 1)) := by
    gcongr
  have hde_le : de ^ (1 + lf) ≤ (de * NT) ^ (1 + lf) :=
    Real.rpow_le_rpow hde0.le (by nlinarith) (by linarith)
  have hsplit : (de * NT) ^ (((10 * s + 8 : ℕ) : ℝ) + 2 * lf) =
      (de * NT) ^ (1 + lf) * (de * NT) ^ (2 + lf) * (de * NT) ^ (10 * s + 5) := by
    rw [← Real.rpow_natCast (de * NT) (10 * s + 5), ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    congr 1; push_cast; try ring
  have e1 : de ^ (k - s) * de ^ (s + 1) = de ^ (k + 1) := by rw [← pow_add]; congr 1; omega
  have e2 : NT ^ k = NT ^ (k - 1) * NT := by rw [← pow_succ]; congr 1; omega
  have hpow : de ^ (k - s) * de ^ (s + 1) * (de * NT) ^ (2 * s) * (de * NT) ^ (4 * (2 * s + 1)) /
      NT ^ (k - 1) = (de / NT) ^ k * (de * NT) ^ (10 * s + 5) := by
    rw [e1, div_pow, e2, eq_comm, div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
    ring
  calc mean ≤ nM * nS * mM * mS * Gl / (massk * NT ^ (k - 1)) := h1
    _ ≤ (de ^ (1 + lf) * (de * NT) ^ (2 + lf) * (massks * de ^ (k - s) * de ^ (s + 1)) *
          (masss * (de * NT) ^ (2 * s)) * (de * NT) ^ (4 * (2 * s + 1))) /
          (massk * NT ^ (k - 1)) := div_le_div_of_nonneg_right h2 hM0.le
    _ = de ^ (1 + lf) * (de * NT) ^ (2 + lf) *
          (de ^ (k - s) * de ^ (s + 1) * (de * NT) ^ (2 * s) * (de * NT) ^ (4 * (2 * s + 1)) /
            NT ^ (k - 1)) * (masss * massks / massk) := by ring
    _ = de ^ (1 + lf) * (de * NT) ^ (2 + lf) * ((de / NT) ^ k * (de * NT) ^ (10 * s + 5)) *
          (masss * massks / massk) := by rw [hpow]
    _ ≤ (de * NT) ^ (1 + lf) * (de * NT) ^ (2 + lf) * ((de / NT) ^ k * (de * NT) ^ (10 * s + 5)) *
          (masss * massks / massk) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hde_le (by positivity)) (by positivity)) (by positivity)
    _ = (de / NT) ^ k * (de * NT) ^ (((10 * s + 8 : ℕ) : ℝ) + 2 * lf) * (masss * massks / massk) := by
        rw [hsplit]; ring

theorem prodMinLeOfProdRatio : SmallTerm := by
  intro ι _ sh₁ ch₁ sh₂ ch₂ T T' g hT hT' hg h₁ h₂ hprod
  have hmin : ∀ x : ℝ, 0 < x → min (T' * x ^ 2) T' = T' * (min 1 x) ^ 2 := by
    intro x hx
    rcases le_total x 1 with h | h
    · have hx2 : x ^ 2 ≤ 1 := by nlinarith
      rw [min_eq_right h, min_eq_left (mul_le_of_le_one_right hT'.le hx2)]
    · have hx2 : 1 ≤ x ^ 2 := by nlinarith
      rw [min_eq_left h, min_eq_right (le_mul_of_one_le_right hT'.le hx2), one_pow, mul_one]
  have hm₁ : ∀ v, 0 < min 1 (sh₁ v) := fun v => lt_min one_pos (h₁ v).1
  have hm₂ : ∀ v, 0 < min 1 (sh₂ v) := fun v => lt_min one_pos (h₂ v).1
  have hPm : 0 < ∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v)) :=
    Finset.prod_pos (fun v _ => mul_pos (hm₁ v) (hm₂ v))
  have hbound : Real.sqrt (T * T' / g ^ 2) ^ Fintype.card ι ≤
      4 ^ Fintype.card ι / ∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v)) := by
    refine hprod.trans ?_
    calc ∏ v, (ch₁ v + ch₂ v) / (sh₁ v * sh₂ v)
          ≤ ∏ v, (4 / (min 1 (sh₁ v) * min 1 (sh₂ v))) :=
          Finset.prod_le_prod
            (fun v _ => div_nonneg (add_nonneg (h₁ v).2.1 (h₂ v).2.1)
              (mul_pos (h₁ v).1 (h₂ v).1).le)
            (fun v _ => hyperbolicPairRatioLe _ _ _ _ (h₁ v).1 (h₁ v).2.1 (h₁ v).2.2
              (h₂ v).1 (h₂ v).2.1 (h₂ v).2.2)
      _ = 4 ^ Fintype.card ι / ∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v)) := by
          rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  have hsq : Real.sqrt (T * T' / g ^ 2) ^ 2 = T * T' / g ^ 2 := Real.sq_sqrt (by positivity)
  have hk1 : (∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) * Real.sqrt (T * T' / g ^ 2) ^ Fintype.card ι ≤
      4 ^ Fintype.card ι := by
    rw [le_div_iff₀ hPm] at hbound; linarith
  have hk2 : (∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) ^ 2 * (T * T' / g ^ 2) ^ Fintype.card ι ≤
      16 ^ Fintype.card ι := by
    have h0 : 0 ≤ (∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) *
        Real.sqrt (T * T' / g ^ 2) ^ Fintype.card ι := by positivity
    have := pow_le_pow_left₀ h0 hk1 2
    calc (∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) ^ 2 * (T * T' / g ^ 2) ^ Fintype.card ι
          = ((∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) *
              Real.sqrt (T * T' / g ^ 2) ^ Fintype.card ι) ^ 2 := by
          rw [mul_pow, ← pow_mul, mul_comm (Fintype.card ι) 2, pow_mul, hsq]
      _ ≤ (4 ^ Fintype.card ι) ^ 2 := this
      _ = 16 ^ Fintype.card ι := by
          rw [← pow_mul, mul_comm (Fintype.card ι) 2, pow_mul]; norm_num
  have hsq2 : Real.sqrt (T' / T) ^ 2 = T' / T := Real.sq_sqrt (by positivity)
  have hab : (∏ v, min (T' * sh₁ v ^ 2) T') * (∏ v, min (T' * sh₂ v ^ 2) T') ≤
      ((4 * Real.sqrt (T' / T) * g) ^ Fintype.card ι) ^ 2 := by
    rw [← Finset.prod_mul_distrib]
    have e : ∀ v, min (T' * sh₁ v ^ 2) T' * min (T' * sh₂ v ^ 2) T' =
        T' ^ 2 * (min 1 (sh₁ v) * min 1 (sh₂ v)) ^ 2 := by
      intro v; rw [hmin _ (h₁ v).1, hmin _ (h₂ v).1]; ring
    simp only [e]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow]
    have hc : T * T' / g ^ 2 * (T' / T * g ^ 2) = T' ^ 2 := by
      first | (field_simp; ring) | field_simp
    calc (T' ^ 2) ^ Fintype.card ι * (∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) ^ 2
          = ((∏ v, (min 1 (sh₁ v) * min 1 (sh₂ v))) ^ 2 * (T * T' / g ^ 2) ^ Fintype.card ι) *
            (T' / T * g ^ 2) ^ Fintype.card ι := by
          rw [mul_assoc, ← mul_pow, hc]; ring
      _ ≤ 16 ^ Fintype.card ι * (T' / T * g ^ 2) ^ Fintype.card ι :=
          mul_le_mul_of_nonneg_right hk2 (by positivity)
      _ = ((4 * Real.sqrt (T' / T) * g) ^ Fintype.card ι) ^ 2 := by
          rw [← mul_pow, ← pow_mul, mul_comm (Fintype.card ι) 2, pow_mul]
          congr 1
          rw [mul_pow, mul_pow, hsq2]; ring
  by_contra hcon
  push_neg at hcon
  obtain ⟨ha, hb⟩ := hcon
  have hc0 : 0 ≤ (4 * Real.sqrt (T' / T) * g) ^ Fintype.card ι := by positivity
  have := mul_lt_mul'' ha hb hc0 hc0
  nlinarith

private theorem eighty_one_pow_mul_four_mul_pow_le_six_mul_pow (m : ℕ) (hm : 1 ≤ m) :
    (81:ℝ) ^ m * ((4 * m : ℕ) : ℝ) ^ (4 * m) ≤ ((6 * m : ℕ) : ℝ) ^ (6 * m) := by
  have hx : (1:ℝ) ≤ m := by exact_mod_cast hm
  push_cast
  rw [pow_mul, pow_mul, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have h4 : (0:ℝ) ≤ (m:ℝ) ^ 4 := by positivity
  have h2 : (1:ℝ) ≤ (m:ℝ) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 h4]

theorem heightExponentAssembly : HeightExponentAssembly := by
  intro s r f A cf De NT HH hs hf hA hcf hDe hNT hHH hNT2 hDe3
  have hHH0 : 0 < HH := by linarith
  have hDe0 : 0 < De := by linarith
  have hNT0 : 0 < NT := by linarith
  have hNTH : NT ≤ HH := by nlinarith
  have hDN : De * NT ≤ HH ^ 4 := by
    calc De * NT ≤ HH ^ 3 * HH := mul_le_mul hDe3 hNTH hNT0.le (by positivity)
      _ = HH ^ 4 := by ring
  have hs1 : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hf1 : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  have B1 : (De * NT) ^ (A * (s + cf)) ≤ HH ^ (4 * (A * (s + cf))) := by
    calc (De * NT) ^ (A * (s + cf)) ≤ (HH ^ 4) ^ (A * (s + cf)) :=
          Real.rpow_le_rpow (by positivity) hDN (by positivity)
      _ = HH ^ (4 * (A * (s + cf))) := by
          rw [← Real.rpow_natCast HH 4, ← Real.rpow_mul hHH0.le]; norm_num
  have B2 : De ^ (cf + 4) ≤ HH ^ (3 * (cf + 4)) := by
    calc De ^ (cf + 4) ≤ (HH ^ 3) ^ (cf + 4) := Real.rpow_le_rpow hDe0.le hDe3 (by positivity)
      _ = HH ^ (3 * (cf + 4)) := by
          rw [← Real.rpow_natCast HH 3, ← Real.rpow_mul hHH0.le]; norm_num
  have B3 : NT ^ (2 * r) * De ^ r * 9 ^ (s * f) * HH ^ (9 * s + 9 * s * r + 16 * r ^ 2) ≤
      HH ^ (4 * r + (9 * s + 9 * s * r + 16 * r ^ 2)) * 9 ^ (s * f) := by
    have h1 : NT ^ (2 * r) ≤ HH ^ r := by
      rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) hNT2 r
    have h2 : De ^ r ≤ HH ^ (3 * r) := by
      rw [pow_mul]; exact pow_le_pow_left₀ hDe0.le hDe3 r
    calc NT ^ (2 * r) * De ^ r * 9 ^ (s * f) * HH ^ (9 * s + 9 * s * r + 16 * r ^ 2)
          ≤ HH ^ r * HH ^ (3 * r) * 9 ^ (s * f) * HH ^ (9 * s + 9 * s * r + 16 * r ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul h1 h2 (by positivity) (by positivity)) (by positivity)) (by positivity)
      _ = HH ^ (4 * r + (9 * s + 9 * s * r + 16 * r ^ 2)) * 9 ^ (s * f) := by ring
  have hm1 : 1 ≤ s * f := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have B45 : (9:ℝ) ^ (s * f) * 9 ^ (s * f) * ((4 * f * s).factorial : ℝ) ≤
      (6 * (s:ℝ) * f) ^ (6 * s * f) := by
    have h81 := eighty_one_pow_mul_four_mul_pow_le_six_mul_pow (s * f) hm1
    have hfac : ((4 * f * s).factorial : ℝ) ≤ ((4 * (s * f) : ℕ) : ℝ) ^ (4 * (s * f)) := by
      rw [show 4 * f * s = 4 * (s * f) by ring]; exact_mod_cast Nat.factorial_le_pow (4 * (s * f))
    have e6 : (6 * (s:ℝ) * f) ^ (6 * s * f) = ((6 * (s * f) : ℕ) : ℝ) ^ (6 * (s * f)) := by
      rw [show 6 * s * f = 6 * (s * f) by ring]; push_cast; try ring
    rw [e6]
    calc (9:ℝ) ^ (s * f) * 9 ^ (s * f) * ((4 * f * s).factorial : ℝ)
          ≤ 81 ^ (s * f) * ((4 * (s * f) : ℕ) : ℝ) ^ (4 * (s * f)) := by
          rw [← mul_pow, show (9:ℝ) * 9 = 81 by norm_num]
          exact mul_le_mul_of_nonneg_left hfac (by positivity)
      _ ≤ _ := h81
  have hEnat : (HH ^ (4 * r + (9 * s + 9 * s * r + 16 * r ^ 2)) * 9 ^ (s * f)) ^ 2 =
      HH ^ (((2 * (4 * r + (9 * s + 9 * s * r + 16 * r ^ 2)) : ℕ)) : ℝ) *
        ((9:ℝ) ^ (s * f) * 9 ^ (s * f)) := by
    rw [Real.rpow_natCast]; ring
  have hexp : 4 * (A * (s + cf)) + 3 * (cf + 4) +
      (((2 * (4 * r + (9 * s + 9 * s * r + 16 * r ^ 2)) : ℕ)) : ℝ) ≤
      (4 * A + 60) * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) + (4 * A + 60) * cf := by
    push_cast
    have hs0 : (0:ℝ) ≤ s := by linarith
    nlinarith [mul_nonneg (mul_nonneg hA hr0) hs0, mul_nonneg hA hs0, mul_nonneg hA (mul_nonneg hr0 hr0),
      mul_nonneg hA hr0, mul_nonneg hr0 hs0, mul_nonneg hr0 hr0, mul_nonneg hA hcf]
  calc _ ≤ HH ^ (4 * (A * (s + cf))) * HH ^ (3 * (cf + 4)) *
        (HH ^ (4 * r + (9 * s + 9 * s * r + 16 * r ^ 2)) * 9 ^ (s * f)) ^ 2 *
        ((4 * f * s).factorial : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul B1 B2 (by positivity) (by positivity))
          (pow_le_pow_left₀ (by positivity) B3 2) (by positivity) (by positivity)) (by positivity)
    _ = HH ^ (4 * (A * (s + cf)) + 3 * (cf + 4) +
          (((2 * (4 * r + (9 * s + 9 * s * r + 16 * r ^ 2)) : ℕ)) : ℝ)) *
          ((9:ℝ) ^ (s * f) * 9 ^ (s * f) * ((4 * f * s).factorial : ℝ)) := by
        rw [hEnat, Real.rpow_add hHH0, Real.rpow_add hHH0]; ring
    _ ≤ HH ^ ((4 * A + 60) * ((s : ℝ) + (2 * r + 2)) * (2 * r + 2) + (4 * A + 60) * cf) *
          (6 * (s:ℝ) * f) ^ (6 * s * f) :=
        mul_le_mul (Real.rpow_le_rpow_of_exponent_le hHH hexp) B45 (by positivity) (by positivity)

theorem normInvEntryLeMinor : InverseEntryMinor := by
  intro n M P hP hdet i j
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, smul_eq_mul,
    norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Ring.inverse_eq_inv,
    norm_inv, inv_mul_eq_div]
  exact div_le_div_of_nonneg_right (hP j i) (norm_nonneg _)

theorem lowerBoundOfProdLengths : LengthLower := by
  intro r l l' R Dr hl hl' hD b
  have hR : 0 ≤ R := ((hl' b).1.le).trans (hl' b).2
  have h1 : ∏ a, l a ≤ R ^ r := by
    calc ∏ a, l a ≤ ∏ _a : Fin r, R :=
          Finset.prod_le_prod (fun a _ => (hl a).1.le) (fun a _ => (hl a).2)
      _ = R ^ r := by simp
  have h2 : ∏ b', l' b' ≤ l' b * R ^ (r - 1) := by
    rw [← Finset.mul_prod_erase Finset.univ l' (Finset.mem_univ b)]
    apply mul_le_mul_of_nonneg_left _ (hl' b).1.le
    calc ∏ b' ∈ Finset.univ.erase b, l' b' ≤ ∏ _b' ∈ Finset.univ.erase b, R :=
          Finset.prod_le_prod (fun a _ => (hl' a).1.le) (fun a _ => (hl' a).2)
      _ = R ^ (r - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ,
            Fintype.card_fin]
  have hr : 0 < r := Fin.pos b
  calc Dr ≤ (∏ a, l a) * ∏ b', l' b' := hD
    _ ≤ R ^ r * (l' b * R ^ (r - 1)) :=
        mul_le_mul h1 h2 (Finset.prod_nonneg (fun a _ => (hl' a).1.le)) (pow_nonneg hR _)
    _ = l' b * R ^ (2 * r - 1) := by
        rw [show 2 * r - 1 = r + (r - 1) by omega, pow_add]; ring

theorem adjugateLastColumnEqCofactor : CofVecAdjugate := by
  intro R _ r Z b
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec
  rw [Fin.val_last, pow_add]
  simp only [Matrix.submatrix_submatrix, Function.comp_id, Function.id_comp]
  ring

theorem expSumLe' : ExpSumLe' := by
  intro A x hA hx
  have h3A : 0 < 3 * A := by linarith
  have hlog : 0 ≤ Real.log (3 * A) := Real.log_nonneg (by linarith)
  have hE : Real.exp (-x / 6) * Real.exp (x / 6) = 1 := by
    rw [← Real.exp_add, show -x / 6 + x / 6 = (0:ℝ) by ring, Real.exp_zero]
  have h3 : 3 * A ≤ Real.exp (x / 6) := by
    calc 3 * A = Real.exp (Real.log (3 * A)) := (Real.exp_log h3A).symm
      _ ≤ Real.exp (x / 6) := Real.exp_le_exp.mpr (by linarith)
  have hpos := Real.exp_pos (-x / 6)
  have hA' : 3 * A * Real.exp (-x / 6) ≤ 1 := by nlinarith
  have hsplit : Real.exp (-x / 2) = Real.exp (-x / 3) * Real.exp (-x / 6) := by
    rw [← Real.exp_add]; congr 1; ring
  have t1 : Real.exp (-4 * x) ≤ Real.exp (-x / 2) := Real.exp_le_exp.mpr (by linarith)
  have t2 : Real.exp (-x) ≤ Real.exp (-x / 2) := Real.exp_le_exp.mpr (by linarith)
  have hp3 := Real.exp_pos (-x / 3)
  have hs : Real.exp (-4 * x) + Real.exp (-x / 2) + Real.exp (-x) ≤ 3 * Real.exp (-x / 2) := by
    linarith
  calc A * (Real.exp (-4 * x) + Real.exp (-x / 2) + Real.exp (-x))
        ≤ A * (3 * Real.exp (-x / 2)) := mul_le_mul_of_nonneg_left hs (by linarith)
    _ = Real.exp (-x / 3) * (3 * A * Real.exp (-x / 6)) := by rw [hsplit]; ring
    _ ≤ Real.exp (-x / 3) * 1 := mul_le_mul_of_nonneg_left hA' hp3.le
    _ = Real.exp (-x / 3) := mul_one _

theorem prodMaxDivEqOne : ThresholdBelow := by
  intro N D H₂ hH hD
  exact Finset.prod_eq_one (fun i _ => max_eq_left ((div_le_one hH).mpr (hD i)))

theorem maxInvSinhSqLe : ShInvPlace := by
  intro sh G T T' Dr hsh hG hDr hTT hGeq
  have hTT0 : 0 < T * T' := by linarith
  have hsh0 : sh ≠ 0 := hsh.ne'
  have hDr0 : Dr ≠ 0 := hDr.ne'
  have hT0 : T * T' ≠ 0 := hTT0.ne'
  apply max_le
  · exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hTT (le_max_left _ _))
      (le_max_left _ _)
  · have e : 1 / sh ^ 2 = T * T' * Dr ^ 2 * (1 / G) := by
      rw [hGeq, mul_one_div, div_eq_div_iff (by positivity) (by rw [← hGeq]; exact hG.ne')]
      ring
    rw [e]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (le_max_right _ _) hTT0.le) (le_max_right _ _)
      (by positivity) (by positivity)

theorem thresholdExponentInequality : ThresholdP := by
  intro k r A cf hA hcf0 hcf hk
  have hkR : (2 * (r:ℝ) + 2) ^ 3 ≤ k := by exact_mod_cast hk
  have hr1 : (1:ℝ) ≤ (r:ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) r; linarith
  have hA0 : (0:ℝ) ≤ A := by linarith
  have ha := mul_le_mul_of_nonneg_left hkR (by positivity : (0:ℝ) ≤ A * ((r:ℝ) + 1) ^ 2)
  have hb := mul_le_mul_of_nonneg_left hcf (by positivity : (0:ℝ) ≤ A * ((r:ℝ) + 1))
  have hc : (r:ℝ) + 1 ≤ A * ((r:ℝ) + 1) := by nlinarith
  have hd : A * ((r:ℝ) + 1) ^ 2 ≤ A * ((r:ℝ) + 1) ^ 5 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr1 (by norm_num)) hA0
  have he : A * ((r:ℝ) + 1) ^ 1 ≤ A * ((r:ℝ) + 1) ^ 5 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr1 (by norm_num)) hA0
  have hf : (0:ℝ) ≤ A * ((r:ℝ) + 1) ^ 5 := by positivity
  linarith

theorem eichlerTransformProperties : EichlerFacts := by
  intro R V _ _ _ _ h hh u σ τ huu huσ hτ
  have hσu : h σ u = 0 := by rw [hh u σ, huσ, star_zero]
  have hE : ∀ (σ' : V) (τ' : R) (y : V),
      Formalism.HermitianLatticeCounting.LatticeSumBounds.eichler h u σ' τ' y = y - h y σ' • u + h y u • σ' - (τ' * h y u) • u :=
    fun _ _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hxu hxσ
    rw [hE, hxu, hxσ]; simp
  · intro p x' hpu hx'u hx'σ
    rw [hE]
    simp [hpu, hx'u, hx'σ]
  · intro x
    refine ⟨-(h x σ) - τ * h x u, ?_⟩
    rw [hE]; module
  · intro x
    have hyu : h (Formalism.HermitianLatticeCounting.LatticeSumBounds.eichler h u σ τ x) u = h x u := by
      rw [hE]
      simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, huu, hσu, mul_zero, sub_zero, add_zero]
    have hyσ : h (Formalism.HermitianLatticeCounting.LatticeSumBounds.eichler h u σ τ x) σ = h x σ + h x u * h σ σ := by
      rw [hE]
      simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, huσ, mul_zero, sub_zero, add_zero]
    rw [hE (-σ) (star τ) (Formalism.HermitianLatticeCounting.LatticeSumBounds.eichler h u σ τ x), map_neg, hyσ, hyu, hE σ τ x, ← hτ]
    module

theorem centralTransvectionProperties : CentreFacts := by
  intro R V _ _ _ _ h r e c
  refine ⟨?_, ?_⟩
  · intro x hx
    simp [hx]
  · intro n f' b
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.mul_apply, Finset.sum_smul]
    simp [Matrix.of_apply]

theorem prodVolumeFactor : NProduct := by
  intro ι _ k r G vt T g v hk hT hg hvt hprod
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.nv
  rw [Finset.prod_pow]
  have e : ∏ w, (Real.exp 1 * Real.pi * G w * g⁻¹ ^ (2 * r + 2) / (T * k * vt w)) =
      (Real.exp 1 * Real.pi * g⁻¹ ^ (2 * r + 2) / (T * k)) ^ Fintype.card ι * (∏ w, G w) /
        ∏ w, vt w := by
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib,
      ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro w _
    ring
  rw [e, hprod, mul_comm k (Fintype.card ι), pow_mul, ← mul_pow]
  congr 1
  ring

theorem prodUnitaryOrderRatioBound : ThetaProd := by
  intro ι P j e ep η q h
  have hb : ∀ p ∈ P, 0 < Formalism.HermitianLatticeCounting.LatticeSumBounds.theta j (ep p) (η p) (q p) ∧
      Formalism.HermitianLatticeCounting.LatticeSumBounds.theta j (ep p) (η p) (q p) ≤ 2 ^ e := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := h p hp
    obtain ⟨b1, -, b3⟩ := unitaryOrderRatioBound j (ep p) (η p) (q p) h2 h3 h4
    exact ⟨b1, b3.trans (pow_le_pow_right₀ (by norm_num) h1)⟩
  refine ⟨Finset.prod_pos (fun p hp => (hb p hp).1), ?_⟩
  calc ∏ p ∈ P, Formalism.HermitianLatticeCounting.LatticeSumBounds.theta j (ep p) (η p) (q p) ≤ ∏ _p ∈ P, (2:ℝ) ^ e :=
        Finset.prod_le_prod (fun p hp => (hb p hp).1.le) (fun p hp => (hb p hp).2)
    _ = 2 ^ (e * P.card) := by rw [Finset.prod_const, ← pow_mul]

theorem nondegenerateFactorBound : DeNonDegBound := by
  intro f s g G₁ G₂ HH₁ HH₂ hg hG₁ hG₂ h₁ h₂ hH₁ hH₂
  have hH : 1 ≤ HH₁ * HH₂ := one_le_mul_of_one_le_of_one_le hH₁ hH₂
  have hq : (2 / g) ^ ((s - 1) * f) ≤ 1 :=
    pow_le_one₀ (by positivity) (by rw [div_le_one (by linarith)]; exact hg)
  have hsq : Real.sqrt (G₁ * G₂) ≤ HH₁ * HH₂ := by
    calc Real.sqrt (G₁ * G₂) ≤ Real.sqrt (HH₁ * HH₂) :=
          Real.sqrt_le_sqrt (mul_le_mul h₁ h₂ hG₂ (by linarith))
      _ ≤ Real.sqrt ((HH₁ * HH₂) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = HH₁ * HH₂ := Real.sqrt_sq (by linarith)
  have h1 : (2 / g) ^ ((s - 1) * f) * Real.sqrt (G₁ * G₂) ≤ HH₁ * HH₂ := by
    calc (2 / g) ^ ((s - 1) * f) * Real.sqrt (G₁ * G₂) ≤ 1 * (HH₁ * HH₂) :=
          mul_le_mul hq hsq (Real.sqrt_nonneg _) zero_le_one
      _ = HH₁ * HH₂ := one_mul _
  refine ⟨h1, h1.trans ?_⟩
  calc HH₁ * HH₂ = (HH₁ * HH₂) ^ 1 := (pow_one _).symm
    _ ≤ (HH₁ * HH₂) ^ 3 := pow_le_pow_right₀ hH (by norm_num)

theorem degenerateFactorBound : DeDegBound := by
  intro f s g T G₁ G₂ K₁ K₂ HH₁ HH₂ hg hT hG₁ hG₂ h₁ h₂ hK₁ hK₂ hk₁ hk₂ h9
  have hH₁ : 0 ≤ HH₁ := hG₁.trans h₁
  have hH₂ : 0 ≤ HH₂ := hG₂.trans h₂
  have hq : (2 / g) ^ ((s - 2) * f) ≤ 1 :=
    pow_le_one₀ (by positivity) (by rw [div_le_one (by linarith)]; exact hg)
  have hTi : T⁻¹ ≤ 1 := by have := inv_anti₀ one_pos hT; simpa using this
  have hTf : T⁻¹ ^ f ≤ 1 := pow_le_one₀ (by positivity) hTi
  have hY0 : 0 ≤ Real.sqrt (G₁ * G₂) * K₁ * K₂ := by positivity
  have hY : Real.sqrt (G₁ * G₂) * K₁ * K₂ ≤ (HH₁ * HH₂) ^ 3 := by
    have hsq : (Real.sqrt (G₁ * G₂) * K₁ * K₂) ^ 2 ≤ ((HH₁ * HH₂) ^ 3) ^ 2 := by
      have e : (Real.sqrt (G₁ * G₂) * K₁ * K₂) ^ 2 = (G₁ * G₂) * (K₁ ^ 2 * K₂ ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hG₁ hG₂)]; ring
      rw [e]
      calc (G₁ * G₂) * (K₁ ^ 2 * K₂ ^ 2)
            ≤ (HH₁ * HH₂) * ((9 ^ f * HH₁ ^ 3) * (9 ^ f * HH₂ ^ 3)) :=
            mul_le_mul (mul_le_mul h₁ h₂ hG₂ hH₁) (mul_le_mul hk₁ hk₂ (by positivity) (by positivity))
              (by positivity) (by positivity)
        _ = (9 ^ f) ^ 2 * (HH₁ * HH₂) ^ 4 := by ring
        _ ≤ (HH₁ * HH₂) ^ 2 * (HH₁ * HH₂) ^ 4 :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h9 2) (by positivity)
        _ = ((HH₁ * HH₂) ^ 3) ^ 2 := by ring
    calc Real.sqrt (G₁ * G₂) * K₁ * K₂ = Real.sqrt ((Real.sqrt (G₁ * G₂) * K₁ * K₂) ^ 2) :=
          (Real.sqrt_sq hY0).symm
      _ ≤ Real.sqrt (((HH₁ * HH₂) ^ 3) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = (HH₁ * HH₂) ^ 3 := Real.sqrt_sq (by positivity)
  calc (2 / g) ^ ((s - 2) * f) * Real.sqrt (G₁ * G₂) * T⁻¹ ^ f * K₁ * K₂
        = ((2 / g) ^ ((s - 2) * f) * T⁻¹ ^ f) * (Real.sqrt (G₁ * G₂) * K₁ * K₂) := by ring
    _ ≤ (1 * 1) * (HH₁ * HH₂) ^ 3 :=
        mul_le_mul (mul_le_mul hq hTf (by positivity) zero_le_one) hY hY0 (by norm_num)
    _ = (HH₁ * HH₂) ^ 3 := by ring

theorem prodHyperbolicRatioSqLe : DegFactorBound := by
  intro ι _ sh ch G Dr T T' HH hTT hsc hG hDr hGeq hHH1 hHH2 hHH3
  have hTT0 : 0 ≤ T * T' := by linarith
  have hHH0 : 0 ≤ HH := le_trans (pow_nonneg hTT0 _) hHH1
  have hper : ∀ v, ((1 + ch v) / sh v) ^ 2 ≤
      9 * (T * T' * max 1 (Dr v ^ 2) * max 1 (1 / G v)) := by
    intro v
    obtain ⟨hs, hc, he⟩ := hsc v
    have h1 := hyperbolicRatioLe (sh v) (ch v) hs hc he
    have h0 : 0 ≤ (1 + ch v) / sh v := by positivity
    have h2 : ((1 + ch v) / sh v) ^ 2 ≤ (3 * max 1 (1 / sh v)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    have h3 : max 1 (1 / sh v) ^ 2 ≤ max 1 (1 / sh v ^ 2) := by
      rcases le_total (1 / sh v) 1 with h | h
      · rw [max_eq_left h, one_pow]; exact le_max_left _ _
      · rw [max_eq_right h, div_pow, one_pow]; exact le_max_right _ _
    have h4 := maxInvSinhSqLe (sh v) (G v) T T' (Dr v) hs (hG v) (hDr v) hTT (hGeq v)
    calc ((1 + ch v) / sh v) ^ 2 ≤ (3 * max 1 (1 / sh v)) ^ 2 := h2
      _ = 9 * max 1 (1 / sh v) ^ 2 := by ring
      _ ≤ 9 * (T * T' * max 1 (Dr v ^ 2) * max 1 (1 / G v)) := by linarith
  rw [← Finset.prod_pow]
  calc ∏ v, ((1 + ch v) / sh v) ^ 2
        ≤ ∏ v, (9 * (T * T' * max 1 (Dr v ^ 2) * max 1 (1 / G v))) :=
        Finset.prod_le_prod (fun v _ => sq_nonneg _) (fun v _ => hper v)
    _ = 9 ^ Fintype.card ι * ((T * T') ^ Fintype.card ι * (∏ v, max 1 (Dr v ^ 2)) *
          ∏ v, max 1 (1 / G v)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
          Finset.prod_const, Finset.prod_const, Finset.card_univ]
    _ ≤ 9 ^ Fintype.card ι * (HH * HH * HH) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (mul_le_mul hHH1 hHH2 (finset_prod_max_one_nonneg _ _) hHH0) hHH3
          (finset_prod_max_one_nonneg _ _) (mul_nonneg hHH0 hHH0)
    _ = 9 ^ Fintype.card ι * HH ^ 3 := by ring

theorem splitResidueTrace : ResidueSplit := by
  intro k A _ _ _ _ ε hε
  have hsa : ∀ a : A, star a = a ↔ (ε a).1 = (ε a).2 := by
    intro a
    constructor
    · intro h
      have h0 := hε a
      rw [h] at h0
      have h1 := congrArg Prod.fst h0
      simpa using h1
    · intro h
      apply ε.injective
      rw [hε]
      ext <;> simp [h]
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.card_congr ε.toEquiv, Nat.card_prod, sq]
  · apply Nat.card_congr
    exact {
      toFun := fun a => (ε a.1).1
      invFun := fun x => ⟨ε.symm (x, x), (hsa _).mpr (by simp)⟩
      left_inv := fun a => by
        apply Subtype.ext
        apply ε.injective
        simp only [RingEquiv.apply_symm_apply]
        ext
        · rfl
        · exact (hsa a.1).mp a.2
      right_inv := fun x => by simp }
  · intro a ha
    refine ⟨ε.symm ((ε a).1, 0), ?_⟩
    apply ε.injective
    rw [map_add, hε, RingEquiv.apply_symm_apply]
    ext
    · simp
    · simp [(hsa a).mp ha]

theorem cardQuadruplesProdLe : QuadCount := by
  intro De hDe
  obtain ⟨N, hN⟩ : ∃ N, N = ⌊De⌋₊ := ⟨_, rfl⟩
  have hsub : {q : Fin 4 → ℕ | (∀ i, 1 ≤ q i) ∧ ((∏ i, q i : ℕ) : ℝ) ≤ De} ⊆
      ↑(Fintype.piFinset (fun _ : Fin 4 => Finset.Icc 1 N)) := by
    intro q hq
    obtain ⟨h1, h2⟩ := hq
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    refine ⟨h1 i, ?_⟩
    rw [hN]
    apply Nat.le_floor
    have hpos : 0 < ∏ j, q j := Finset.prod_pos (fun j _ => h1 j)
    have hqi : q i ≤ ∏ j, q j := Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem q (Finset.mem_univ i))
    exact le_trans (by exact_mod_cast hqi) h2
  refine ⟨(Fintype.piFinset (fun _ : Fin 4 => Finset.Icc 1 N)).finite_toSet.subset hsub, ?_⟩
  have hcard : ({q : Fin 4 → ℕ | (∀ i, 1 ≤ q i) ∧ ((∏ i, q i : ℕ) : ℝ) ≤ De}).ncard ≤
      (Fintype.piFinset (fun _ : Fin 4 => Finset.Icc 1 N)).card := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Fintype.card_piFinset, Finset.prod_const, Nat.card_Icc, Finset.card_univ,
    Fintype.card_fin, Nat.add_sub_cancel] at hcard
  have hNDe : (N:ℝ) ≤ De := by rw [hN]; exact Nat.floor_le (by linarith)
  calc (({q : Fin 4 → ℕ | (∀ i, 1 ≤ q i) ∧ ((∏ i, q i : ℕ) : ℝ) ≤ De}).ncard : ℝ)
        ≤ ((N ^ 4 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (N:ℝ) ^ 4 := by push_cast; try ring
    _ ≤ De ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hNDe 4

lemma summable_one_div_add_one_pow (j : ℕ) (hj : 2 ≤ j) : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ j) := by
  have h := Real.summable_one_div_nat_pow.mpr (show 1 < j by omega)
  have h1 := (summable_nat_add_iff 1).mpr h
  exact h1.congr (fun n => by simp)

lemma summable_one_div_add_two_pow (j : ℕ) (hj : 2 ≤ j) : Summable (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ j) := by
  have h := Real.summable_one_div_nat_pow.mpr (show 1 < j by omega)
  have h1 := (summable_nat_add_iff 2).mpr h
  exact h1.congr (fun n => by simp)

lemma zetaSeries_eq_one_add_tsum (j : ℕ) (hj : 2 ≤ j) : zetaR j = 1 + ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ j := by
  have h1 := (hasSum_nat_add_iff' 1).mpr (summable_one_div_add_one_pow j hj).hasSum
  have h2 : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ j) (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1) := by
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR
    simpa [add_assoc, one_add_one_eq_two] using h1
  rw [h2.tsum_eq]; ring

lemma tsum_one_div_add_two_sq : ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 2 = Real.pi ^ 2 / 6 - 1 := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  have h2 : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by simpa using h
  have h3 : Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR 2 = Real.pi ^ 2 / 6 := h2.tsum_eq
  have h4 := zetaSeries_eq_one_add_tsum 2 le_rfl
  linarith

lemma sum_Icc_three_pow_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (N : ℕ) :
    ∑ j ∈ Finset.Icc 3 N, x ^ j ≤ x ^ 3 / (1 - x) := by
  have h1x : 0 < 1 - x := by linarith
  have key : ∀ n, (1 - x) * ∑ j ∈ Finset.Icc 3 (n + 2), x ^ j = x ^ 3 - x ^ (n + 3) := by
    intro n
    induction n with
    | zero =>
      rw [Finset.Icc_eq_empty (show ¬ 3 ≤ 0 + 2 by norm_num)]
      simp
    | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by ring,
        Finset.sum_Icc_succ_top (show 3 ≤ n + 2 + 1 by omega), mul_add, ih]
      ring
  rw [le_div_iff₀ h1x]
  rcases (show N ≤ 1 ∨ 2 ≤ N by omega) with h | h
  · rw [Finset.Icc_eq_empty (show ¬ 3 ≤ N by omega), Finset.sum_empty, zero_mul]; positivity
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    rw [mul_comm, key n]
    have : 0 ≤ x ^ (n + 3) := by positivity
    linarith

private theorem hasSum_inv_succ_sub_inv_succ_succ_eq_one :
    HasSum (fun n : ℕ => 1 / ((n:ℝ) + 1) - 1 / ((n:ℝ) + 2)) 1 := by
  have hnn : ∀ n : ℕ, 0 ≤ 1 / ((n:ℝ) + 1) - 1 / ((n:ℝ) + 2) := by
    intro n
    have h1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le h1 (by linarith)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have e : ∀ M : ℕ, ∑ i ∈ Finset.range M, (1 / ((i:ℝ) + 1) - 1 / ((i:ℝ) + 2)) =
      1 - 1 / ((M:ℝ) + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, ih, Nat.cast_succ, show (M:ℝ) + 1 + 1 = M + 2 by ring]; ring
  simp_rw [e]
  have := (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (1:ℝ)) Filter.atTop (nhds 1)).sub
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using this

private theorem hasSum_finset_sum_of_forall_hasSum {γ : Type*} [DecidableEq γ] (s : Finset γ) (f : γ → ℕ → ℝ)
    (a : γ → ℝ) : (∀ i ∈ s, HasSum (f i) (a i)) →
      HasSum (fun n => ∑ i ∈ s, f i n) (∑ i ∈ s, a i) := by
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp only [Finset.sum_empty]
    exact hasSum_zero
  · intro i s hi ih h
    have e1 : (fun n => ∑ j ∈ insert i s, f j n) = fun n => f i n + ∑ j ∈ s, f j n := by
      funext n; rw [Finset.sum_insert hi]
    rw [e1, Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private theorem inv_cube_div_one_sub_inv_eq_of_eq_add_one (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : b = a + 1) :
    (1 / b) ^ 3 / (1 - 1 / b) = 1 / a - 1 / b - 1 / b ^ 2 := by
  have e1 : 1 - 1 / b = a / b := by
    rw [eq_div_iff hb, sub_mul, one_div, inv_mul_cancel₀ hb, hab]; ring
  have ha' : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have hb' : b * b⁻¹ = 1 := mul_inv_cancel₀ hb
  rw [e1, div_div_eq_mul_div, div_eq_iff ha]
  linear_combination (b⁻¹ ^ 2 + 1 + b⁻¹) * hb' - ha' - (b⁻¹ + b⁻¹ ^ 2) * hab

lemma sum_zetaSeries_sub_one_le (N : ℕ) : ∑ j ∈ Finset.Icc 3 N, (zetaR j - 1) ≤ 0.356 := by
  have hH : HasSum (fun n : ℕ => ∑ j ∈ Finset.Icc 3 N, (1 / ((n:ℝ) + 2)) ^ j)
      (∑ j ∈ Finset.Icc 3 N, (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1)) := by
    apply hasSum_finset_sum_of_forall_hasSum
    intro j hj
    have hj2 : 2 ≤ j := by simp only [Finset.mem_Icc] at hj; omega
    show HasSum (fun n : ℕ => (1 / ((n:ℝ) + 2)) ^ j) (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1)
    have e : (fun n : ℕ => (1 / ((n:ℝ) + 2)) ^ j) = fun n : ℕ => 1 / ((n:ℝ) + 2) ^ j := by
      funext n; exact _root_.one_div_pow _ _
    rw [e, show Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1 = ∑' n : ℕ, 1 / ((n:ℝ) + 2) ^ j by
      rw [zetaSeries_eq_one_add_tsum j hj2]; ring]
    exact (summable_one_div_add_two_pow j hj2).hasSum
  have hb : ∀ n : ℕ, ∑ j ∈ Finset.Icc 3 N, (1 / ((n:ℝ) + 2)) ^ j ≤
      (1 / ((n:ℝ) + 1) - 1 / ((n:ℝ) + 2)) - 1 / ((n:ℝ) + 2) ^ 2 := by
    intro n
    have hn1 : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have hn2 : (0:ℝ) < (n:ℝ) + 2 := by positivity
    have hx0 : 0 ≤ 1 / ((n:ℝ) + 2) := by positivity
    have hx1 : 1 / ((n:ℝ) + 2) < 1 := by rw [div_lt_one hn2]; linarith
    refine (sum_Icc_three_pow_le _ hx0 hx1 N).trans (le_of_eq ?_)
    exact inv_cube_div_one_sub_inv_eq_of_eq_add_one _ _ hn1.ne' hn2.ne' (by ring)
  have hS1 : HasSum (fun n : ℕ => (1 / ((n:ℝ) + 1) - 1 / ((n:ℝ) + 2)) - 1 / ((n:ℝ) + 2) ^ 2)
      (1 - (Real.pi ^ 2 / 6 - 1)) := by
    have h2 : HasSum (fun n : ℕ => 1 / ((n:ℝ) + 2) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
      rw [← tsum_one_div_add_two_sq]
      exact (summable_one_div_add_two_pow 2 le_rfl).hasSum
    exact hasSum_inv_succ_sub_inv_succ_succ_eq_one.sub h2
  have hle := hasSum_le hb hH hS1
  nlinarith [Real.pi_gt_d4]

lemma one_le_zetaSeries (j : ℕ) (hj : 2 ≤ j) : 1 ≤ zetaR j := by
  rw [zetaSeries_eq_one_add_tsum j hj]
  have : 0 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ j := tsum_nonneg (fun n => by positivity)
  linarith

theorem sumLogZetaSeriesLe : ZetaLogSum := by
  intro N
  calc ∑ j ∈ Finset.Icc 3 N, Real.log (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j) ≤ ∑ j ∈ Finset.Icc 3 N, (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj2 : 2 ≤ j := by simp only [Finset.mem_Icc] at hj; omega
        exact Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos (one_le_zetaSeries j hj2))
    _ ≤ 0.356 := sum_zetaSeries_sub_one_le N

lemma zetaSeries_le (j : ℕ) (hj : 3 ≤ j) : zetaR j ≤ 1.356 := by
  have hmem : j ∈ Finset.Icc 3 j := Finset.mem_Icc.mpr ⟨hj, le_rfl⟩
  have hnn : ∀ i ∈ Finset.Icc 3 j, (0:ℝ) ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR i - 1 := by
    intro i hi
    have : 2 ≤ i := by simp only [Finset.mem_Icc] at hi; omega
    linarith [one_le_zetaSeries i this]
  have h := Finset.single_le_sum hnn hmem
  linarith [sum_zetaSeries_sub_one_le j]

lemma prod_zetaSeries_le (S : Finset ℕ) (hS : ∀ j ∈ S, 3 ≤ j) : ∏ j ∈ S, zetaR j ≤ Real.exp 0.356 := by
  have hpos : ∀ j ∈ S, 0 < Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j := fun j hj =>
    lt_of_lt_of_le one_pos (one_le_zetaSeries j (by have := hS j hj; omega))
  obtain ⟨M, hM⟩ : ∃ M, S ⊆ Finset.Icc 3 M :=
    ⟨S.sup id, fun j hj => Finset.mem_Icc.mpr ⟨hS j hj, Finset.le_sup (f := id) hj⟩⟩
  have hsub : ∑ j ∈ S, (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1) ≤ ∑ j ∈ Finset.Icc 3 M, (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg hM (fun i hi _ => by
      have : 2 ≤ i := by simp only [Finset.mem_Icc] at hi; omega
      linarith [one_le_zetaSeries i this])
  calc ∏ j ∈ S, Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j = Real.exp (∑ j ∈ S, Real.log (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j)) := by
        rw [Real.exp_sum]
        exact Finset.prod_congr rfl (fun j hj => (Real.exp_log (hpos j hj)).symm)
    _ ≤ Real.exp (∑ j ∈ S, (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1)) :=
        Real.exp_le_exp.mpr (Finset.sum_le_sum (fun j hj => Real.log_le_sub_one_of_pos (hpos j hj)))
    _ ≤ Real.exp 0.356 := Real.exp_le_exp.mpr (hsub.trans (sum_zetaSeries_sub_one_le M))

noncomputable def s5bA (v : ℝ) (j : ℕ) : ℝ := ((j - 1).factorial : ℝ) * (v / Real.pi) ^ j

lemma factorialPiWeight_pos (v : ℝ) (hv : 0 < v) (j : ℕ) : 0 < s5bA v j := by
  unfold s5bA
  have := Real.pi_pos
  exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (div_pos hv this) _)

lemma one_le_mul_factorialPiWeight (v : ℝ) (hv : 1 ≤ v) (k : ℕ) (hk : 1 ≤ k) :
    1 ≤ (Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)) * s5bA v k := by
  have hst := invFactorialLeStirling k hk
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hv0 : 0 < v := by linarith
  have hπ0 : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hk0' : (k:ℝ) ≠ 0 := hk0.ne'
  have hv0' : v ≠ 0 := hv0.ne'
  have hF : (0:ℝ) < ((k - 1).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  unfold s5bA
  have e0 : (Real.exp 1 / k) ^ k = (Real.exp 1 * Real.pi / (k * v)) ^ k * (v / Real.pi) ^ k := by
    rw [← mul_pow]; congr 1
    first | (field_simp; ring) | field_simp
  have e : (Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)) *
      (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) =
      ((Real.exp 1 / k) ^ k * Real.sqrt (k / (2 * Real.pi))) * ((k - 1).factorial : ℝ) := by
    rw [e0]; ring
  rw [e]
  exact (div_le_iff₀ hF).mp hst

theorem invMassFactorLe : InvMk := by
  intro f k v Lv hv hk hL
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk3 : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hv0 : 0 < v := by linarith
  have hz1 : 1 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR k := one_le_zetaSeries k (by omega)
  have hzle : Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR k ≤ 1.356 := zetaSeries_le k hk
  have hzf : 0 < Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR k ^ f := pow_pos (by linarith) f
  have hL0 : 0 < Lv k := lt_of_lt_of_le (inv_pos.mpr hzf) hL
  have hLi : (Lv k)⁻¹ ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR k ^ f := by
    have := inv_anti₀ (inv_pos.mpr hzf) hL
    rwa [inv_inv] at this
  have hW := one_le_mul_factorialPiWeight v hv k (by omega)
  have hWpos := factorialPiWeight_pos v hv0 k
  have hWi : (s5bA v k)⁻¹ ≤
      (Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)) := by
    calc (s5bA v k)⁻¹ = (s5bA v k)⁻¹ * 1 := (mul_one _).symm
      _ ≤ (s5bA v k)⁻¹ * ((Real.exp 1 * Real.pi / (k * v)) ^ k *
            Real.sqrt (k / (2 * Real.pi)) * s5bA v k) :=
          mul_le_mul_of_nonneg_left hW (inv_nonneg.mpr hWpos.le)
      _ = (Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)) := by
          rw [mul_comm (s5bA v k)⁻¹, mul_assoc, mul_inv_cancel₀ hWpos.ne', mul_one]
  have hs1 : Real.sqrt (k / (2 * Real.pi)) * 1.356 ≤ k := by
    have h1 : (k:ℝ) / (2 * Real.pi) ≤ ((k:ℝ) / 2) ^ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_le_mul hk3 Real.pi_gt_three.le (by norm_num) hk0.le]
    have h2 : Real.sqrt (k / (2 * Real.pi)) ≤ k / 2 := by
      calc Real.sqrt (k / (2 * Real.pi)) ≤ Real.sqrt (((k:ℝ) / 2) ^ 2) := Real.sqrt_le_sqrt h1
        _ = k / 2 := Real.sqrt_sq (by positivity)
    nlinarith [Real.sqrt_nonneg (k / (2 * Real.pi))]
  have hs2 : Real.sqrt ((2 * v) ^ f) ≤ (2 * v) ^ f := by
    have h1 : 1 ≤ (2 * v) ^ f := one_le_pow₀ (by linarith)
    calc Real.sqrt ((2 * v) ^ f) ≤ Real.sqrt (((2 * v) ^ f) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = (2 * v) ^ f := Real.sqrt_sq (by positivity)
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.mJ
  have e : (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) = s5bA v k := rfl
  rw [e, mul_inv, mul_inv, inv_inv, ← inv_pow]
  calc (s5bA v k)⁻¹ ^ f * Real.sqrt ((2 * v) ^ f) * (Lv k)⁻¹
        ≤ ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi))) ^ f *
            (2 * v) ^ f * (1.356:ℝ) ^ f :=
        mul_le_mul (mul_le_mul (pow_le_pow_left₀ (by positivity) hWi f) hs2 (by positivity)
          (by positivity)) (hLi.trans (pow_le_pow_left₀ (by linarith) hzle f)) (by positivity)
          (by positivity)
    _ = ((Real.exp 1 * Real.pi / (k * v)) ^ k) ^ f * (Real.sqrt (k / (2 * Real.pi)) * 1.356) ^ f *
          (2 * v) ^ f := by ring
    _ ≤ ((Real.exp 1 * Real.pi / (k * v)) ^ k) ^ f * (k:ℝ) ^ f * (2 * v) ^ f :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hs1 f) (by positivity)) (by positivity)
    _ = (Real.exp 1 * Real.pi / (k * v)) ^ (k * f) * (k * (2 * v)) ^ f := by rw [pow_mul]; ring

lemma prod_massFactor (f : ℕ) (v : ℝ) (Lv : ℕ → ℝ) (S : Finset ℕ) :
    ∏ j ∈ S, mJ f v Lv j =
      (∏ j ∈ S, s5bA v j) ^ f * ((Real.sqrt ((2 * v) ^ f))⁻¹) ^ S.card * ∏ j ∈ S, Lv j := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.mJ s5bA
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const]

lemma factorialPiWeight_le_pi_pow_mul (v : ℝ) (hv : 1 ≤ v) (j t : ℕ) : s5bA v j ≤ Real.pi ^ t * s5bA v (j + t) := by
  unfold s5bA
  have hπ := Real.pi_pos
  have hπ0 : Real.pi ≠ 0 := hπ.ne'
  have hf : ((j - 1).factorial : ℝ) ≤ ((j + t - 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (show j - 1 ≤ j + t - 1 by omega)
  have hvp : v ^ j ≤ v ^ (j + t) := pow_le_pow_right₀ hv (by omega)
  have e1 : (v / Real.pi) ^ j = v ^ j / Real.pi ^ j := div_pow _ _ _
  have e2 : Real.pi ^ t * (((j + t - 1).factorial : ℝ) * (v / Real.pi) ^ (j + t)) =
      ((j + t - 1).factorial : ℝ) * v ^ (j + t) / Real.pi ^ j := by
    rw [eq_div_iff (pow_ne_zero j hπ0), div_pow, pow_add Real.pi j t]
    calc _ = ((j + t - 1).factorial : ℝ) * v ^ (j + t) *
          ((Real.pi ^ j * Real.pi ^ t) / (Real.pi ^ j * Real.pi ^ t)) := by ring
      _ = ((j + t - 1).factorial : ℝ) * v ^ (j + t) := by rw [div_self (by positivity), mul_one]
  rw [e1, e2, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul hf hvp (by positivity) (by positivity)

lemma one_le_seventeen_mul_factorialPiWeight (v : ℝ) (hv : 1 ≤ v) (k : ℕ) (hk : 3 ≤ k) : 1 ≤ 17 * s5bA v (k - 1) := by
  have h := piPowDivFactorialLt k hk
  have hπ := Real.pi_pos
  have hF : (0:ℝ) < ((k - 2).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  unfold s5bA
  rw [show k - 1 - 1 = k - 2 by omega]
  have hv' : (1 / Real.pi) ^ (k - 1) ≤ (v / Real.pi) ^ (k - 1) :=
    pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hv hπ.le) _
  rw [div_lt_iff₀ hF] at h
  have e : (1 / Real.pi) ^ (k - 1) = (Real.pi ^ (k - 1))⁻¹ := by rw [one_div, inv_pow]
  rw [e] at hv'
  have hpk : 0 < Real.pi ^ (k - 1) := pow_pos hπ _
  calc (1:ℝ) = (Real.pi ^ (k - 1))⁻¹ * Real.pi ^ (k - 1) := (inv_mul_cancel₀ hpk.ne').symm
    _ ≤ (Real.pi ^ (k - 1))⁻¹ * (17 * ((k - 2).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left h.le (inv_nonneg.mpr hpk.le)
    _ ≤ (v / Real.pi) ^ (k - 1) * (17 * ((k - 2).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right hv' (by positivity)
    _ = 17 * (((k - 2).factorial : ℝ) * (v / Real.pi) ^ (k - 1)) := by ring

lemma prod_factorialPiWeight_le (v : ℝ) (hv : 1 ≤ v) (k s : ℕ) (hs : 2 ≤ s) (hk : s + 2 ≤ k) :
    ∏ j ∈ Finset.Ioc 2 s, s5bA v j ≤
      (Real.pi ^ ((s - 2) * (k - s - 2)) * 17 *
        ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)))) *
        ∏ j ∈ Finset.Ioc (k - s) k, s5bA v j := by
  have hv0 : 0 < v := by linarith
  have hW : ∀ j, 0 < s5bA v j := factorialPiWeight_pos v hv0
  obtain ⟨t, ht⟩ : ∃ t, t = k - s - 2 := ⟨_, rfl⟩
  rw [← ht]
  have h1 : ∏ j ∈ Finset.Ioc 2 s, s5bA v j ≤
      Real.pi ^ (t * (s - 2)) * ∏ j ∈ Finset.Ioc 2 s, s5bA v (j + t) := by
    calc ∏ j ∈ Finset.Ioc 2 s, s5bA v j
          ≤ ∏ j ∈ Finset.Ioc 2 s, (Real.pi ^ t * s5bA v (j + t)) :=
          Finset.prod_le_prod (fun j _ => (hW j).le)
            (fun j _ => factorialPiWeight_le_pi_pow_mul v hv j t)
      _ = Real.pi ^ (t * (s - 2)) * ∏ j ∈ Finset.Ioc 2 s, s5bA v (j + t) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ioc, ← pow_mul]
  have h2 : ∏ j ∈ Finset.Ioc 2 s, s5bA v (j + t) =
      ∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j := by
    rw [show k - s = 2 + t by omega, show k - 2 = s + t by omega, ← Finset.map_add_right_Ioc,
      Finset.prod_map]
    rfl
  have h3 : ∏ j ∈ Finset.Ioc (k - s) k, s5bA v j =
      (∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j) * s5bA v (k - 1) *
        s5bA v k := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    rw [show m + 2 - 2 = m by omega, show m + 2 - 1 = m + 1 by omega,
      show m + 2 = m + 1 + 1 by ring,
      Finset.prod_Ioc_succ_top (show m + 1 + 1 - s ≤ m + 1 by omega),
      Finset.prod_Ioc_succ_top (show m + 1 + 1 - s ≤ m by omega)]
  have hA := one_le_seventeen_mul_factorialPiWeight v hv k (by omega)
  have hB := one_le_mul_factorialPiWeight v hv k (by omega)
  have hP0 : 0 ≤ ∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j :=
    Finset.prod_nonneg (fun j _ => (hW j).le)
  have hX0 : 0 ≤ Real.pi ^ (t * (s - 2)) * ∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j :=
    mul_nonneg (pow_nonneg Real.pi_pos.le _) hP0
  rw [h3]
  calc ∏ j ∈ Finset.Ioc 2 s, s5bA v j
        ≤ Real.pi ^ (t * (s - 2)) * ∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j := by
        rw [← h2]; exact h1
    _ = (Real.pi ^ (t * (s - 2)) * ∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j) * 1 * 1 := by
        ring
    _ ≤ (Real.pi ^ (t * (s - 2)) * ∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j) *
          (17 * s5bA v (k - 1)) *
          ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)) * s5bA v k) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hA hX0) hB zero_le_one
          (mul_nonneg hX0 (by linarith))
    _ = (Real.pi ^ ((s - 2) * t) * 17 *
          ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)))) *
          ((∏ j ∈ Finset.Ioc (k - s) (k - 2), s5bA v j) * s5bA v (k - 1) *
            s5bA v k) := by ring

theorem massRatioBound : XiBound := by
  intro f k s v mass2 Lv hv hm2 hs hk hL
  have hv0 : 0 < v := by linarith
  have hA3 : ∀ j ∈ Finset.Ioc 2 s, 3 ≤ j := by intro j hj; rw [Finset.mem_Ioc] at hj; omega
  have hB3 : ∀ j ∈ Finset.Ioc (k - s) k, 3 ≤ j := by intro j hj; rw [Finset.mem_Ioc] at hj; omega
  have hzpos : ∀ j, 3 ≤ j → 0 < Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j := fun j hj =>
    lt_of_lt_of_le one_pos (one_le_zetaSeries j (by omega))
  have hLpos : ∀ j, 3 ≤ j → 0 < Lv j := fun j hj =>
    lt_of_lt_of_le (inv_pos.mpr (pow_pos (hzpos j hj) f)) (hL j hj).1
  have hW : ∀ j, 0 < s5bA v j := factorialPiWeight_pos v hv0
  have hσ0 : 0 < Real.sqrt ((2 * v) ^ f) := Real.sqrt_pos.mpr (by positivity)
  have hσ2 : Real.sqrt ((2 * v) ^ f) ^ 2 = (2 * v) ^ f := Real.sq_sqrt (by positivity)
  have hPB0 : 0 < ∏ j ∈ Finset.Ioc (k - s) k, s5bA v j := Finset.prod_pos (fun j _ => hW j)
  have hLB0 : 0 < ∏ j ∈ Finset.Ioc (k - s) k, Lv j := Finset.prod_pos (fun j hj => hLpos j (hB3 j hj))
  have hR := prod_factorialPiWeight_le v hv k s hs hk
  have hratio : (∏ j ∈ Finset.Ioc 2 s, s5bA v j) /
      (∏ j ∈ Finset.Ioc (k - s) k, s5bA v j) ≤
      Real.pi ^ ((s - 2) * (k - s - 2)) * 17 *
        ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi))) := by
    rw [div_le_iff₀ hPB0]; exact hR
  have hLA : ∏ j ∈ Finset.Ioc 2 s, Lv j ≤ Real.exp 0.356 ^ f := by
    calc ∏ j ∈ Finset.Ioc 2 s, Lv j ≤ ∏ j ∈ Finset.Ioc 2 s, Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j ^ f :=
          Finset.prod_le_prod (fun j hj => (hLpos j (hA3 j hj)).le) (fun j hj => (hL j (hA3 j hj)).2)
      _ = (∏ j ∈ Finset.Ioc 2 s, Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j) ^ f := Finset.prod_pow _ _ _
      _ ≤ Real.exp 0.356 ^ f :=
          pow_le_pow_left₀ (Finset.prod_nonneg (fun j hj => (hzpos j (hA3 j hj)).le))
            (prod_zetaSeries_le _ hA3) f
  have hLB : (∏ j ∈ Finset.Ioc (k - s) k, Lv j)⁻¹ ≤ Real.exp 0.356 ^ f := by
    have h1 : ((∏ j ∈ Finset.Ioc (k - s) k, Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j) ^ f)⁻¹ ≤ ∏ j ∈ Finset.Ioc (k - s) k, Lv j := by
      rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
      exact Finset.prod_le_prod (fun j hj => (inv_pos.mpr (pow_pos (hzpos j (hB3 j hj)) f)).le)
        (fun j hj => (hL j (hB3 j hj)).1)
    have h2 : 0 < (∏ j ∈ Finset.Ioc (k - s) k, Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j) ^ f :=
      pow_pos (Finset.prod_pos (fun j hj => hzpos j (hB3 j hj))) f
    have h3 := inv_anti₀ (inv_pos.mpr h2) h1
    rw [inv_inv] at h3
    exact h3.trans (pow_le_pow_left₀ (Finset.prod_nonneg (fun j hj => (hzpos j (hB3 j hj)).le))
      (prod_zetaSeries_le _ hB3) f)
  have hexp : Real.exp 0.356 ^ f * Real.exp 0.356 ^ f ≤ Real.exp (0.72 * f) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by have := (Nat.cast_nonneg f : (0:ℝ) ≤ f); nlinarith)
  have key : ∀ (M PA PB LA LB σ : ℝ) (a : ℕ), 0 < PB → 0 < LB → 0 < σ →
      M * (PA ^ f * σ⁻¹ ^ a * LA) / (PB ^ f * σ⁻¹ ^ (a + 2) * LB) =
        M * (PA / PB) ^ f * σ ^ 2 * (LA * LB⁻¹) := by
    intro M PA PB LA LB σ a hPB hLB hσ
    have hP : PB ^ f * PB⁻¹ ^ f = 1 := by rw [← mul_pow, mul_inv_cancel₀ hPB.ne', one_pow]
    have hS : σ ^ 2 * σ⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hσ.ne', one_pow]
    have hL : LB * LB⁻¹ = 1 := mul_inv_cancel₀ hLB.ne'
    rw [div_eq_iff (by positivity)]
    linear_combination (-(M * PA ^ f * σ⁻¹ ^ a * LA) * (σ ^ 2 * σ⁻¹ ^ 2) * (LB * LB⁻¹)) * hP +
      (-(M * PA ^ f * σ⁻¹ ^ a * LA) * (LB * LB⁻¹)) * hS + (-(M * PA ^ f * σ⁻¹ ^ a * LA)) * hL
  rw [prod_massFactor, prod_massFactor, Nat.card_Ioc, Nat.card_Ioc, show k - (k - s) = s by omega]
  have hs' : (Real.sqrt ((2 * v) ^ f))⁻¹ ^ s = (Real.sqrt ((2 * v) ^ f))⁻¹ ^ ((s - 2) + 2) := by
    congr 1; omega
  rw [hs', key _ _ _ _ _ _ _ hPB0 hLB0 hσ0, hσ2]
  have hRf0 : 0 ≤ Real.pi ^ ((s - 2) * (k - s - 2)) * 17 *
      ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi))) := by positivity
  calc mass2 * ((∏ j ∈ Finset.Ioc 2 s, s5bA v j) /
          (∏ j ∈ Finset.Ioc (k - s) k, s5bA v j)) ^ f * (2 * v) ^ f *
          ((∏ j ∈ Finset.Ioc 2 s, Lv j) * (∏ j ∈ Finset.Ioc (k - s) k, Lv j)⁻¹)
        ≤ mass2 * (Real.pi ^ ((s - 2) * (k - s - 2)) * 17 *
            ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)))) ^ f * (2 * v) ^ f *
          (Real.exp 0.356 ^ f * Real.exp 0.356 ^ f) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (div_nonneg (Finset.prod_nonneg (fun j _ => (hW j).le)) hPB0.le) hratio f) hm2)
          (by positivity))
          (mul_le_mul hLA hLB (inv_nonneg.mpr hLB0.le) (by positivity))
          (mul_nonneg (Finset.prod_nonneg (fun j hj => (hLpos j (hA3 j hj)).le)) (inv_nonneg.mpr hLB0.le))
          (by positivity)
    _ ≤ mass2 * (Real.pi ^ ((s - 2) * (k - s - 2)) * 17 *
            ((Real.exp 1 * Real.pi / (k * v)) ^ k * Real.sqrt (k / (2 * Real.pi)))) ^ f * (2 * v) ^ f *
          Real.exp (0.72 * f) := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = mass2 * (2 * v) ^ f * Real.exp (0.72 * f) * 17 ^ f * Real.sqrt (k / (2 * Real.pi)) ^ f *
          Real.pi ^ ((s - 2) * (k - s - 2) * f) * (Real.exp 1 * Real.pi / (k * v)) ^ (k * f) := by
        ring

theorem prodDeltaLossBound : LossPrimeProd := by
  classical
  intro ι l _ E D De H₁ H₂ e Sg hH₁ hH₂ hD hDprod hDe0 hDe
  have hH₁0 : 0 ≤ H₁ := by linarith
  have hDv : ∀ v, De v ≤ ∏ i ∈ E, max 1 (1 / D i v) := by
    intro v
    rcases hDe v with h | ⟨i, hi, h⟩
    · exact h.trans (one_le_finset_prod_of_forall_one_le _ _ (fun i _ => le_max_left _ _))
    · rw [← Finset.mul_prod_erase E _ hi]
      calc De v ≤ max 1 (1 / D i v) := h.trans (le_max_right _ _)
        _ ≤ max 1 (1 / D i v) * ∏ j ∈ E.erase i, max 1 (1 / D j v) :=
            le_mul_of_one_le_right (zero_le_one.trans (le_max_left _ _))
              (one_le_finset_prod_of_forall_one_le _ _ (fun j _ => le_max_left _ _))
  have hinv : ∏ v, ∏ i ∈ E, max 1 (1 / D i v) ≤
      H₂ ^ (Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂ := by
    rw [Finset.prod_comm]
    calc ∏ i ∈ E, ∏ v, max 1 (1 / D i v) ≤ ∏ i ∈ E, ∏ v, max 1 (D i v) :=
          Finset.prod_le_prod (fun i _ => finset_prod_max_one_nonneg _ _)
            (fun i hi => (prodMaxInvLeSq ι (D i) Finset.univ (hD i hi) (hDprod i hi)).2)
      _ ≤ _ := prod_prod_max_le_pow_mul_thresholdSize E D H₂ hH₂ hD
  rw [Finset.prod_pow]
  apply pow_le_pow_left₀ (Finset.prod_nonneg (fun v _ => mul_nonneg hH₁0 (hDe0 v)))
  calc ∏ v ∈ Sg, H₁ * De v ≤ ∏ v ∈ Sg, (H₁ * ∏ i ∈ E, max 1 (1 / D i v)) :=
        Finset.prod_le_prod (fun v _ => mul_nonneg hH₁0 (hDe0 v))
          (fun v _ => mul_le_mul_of_nonneg_left (hDv v) hH₁0)
    _ = (∏ _v ∈ Sg, H₁) * ∏ v ∈ Sg, ∏ i ∈ E, max 1 (1 / D i v) := Finset.prod_mul_distrib
    _ ≤ H₁ ^ Fintype.card ι * ∏ v, ∏ i ∈ E, max 1 (1 / D i v) := by
        apply mul_le_mul _ (finset_prod_real_mono_of_subset_of_one_le _ _ (Finset.subset_univ _) _
          (fun v _ => one_le_finset_prod_of_forall_one_le _ _ (fun i _ => le_max_left _ _)))
          (Finset.prod_nonneg (fun v _ => finset_prod_max_one_nonneg _ _)) (pow_nonneg hH₁0 _)
        rw [Finset.prod_const]
        exact pow_le_pow_right₀ hH₁ (Finset.card_le_univ Sg)
    _ ≤ H₁ ^ Fintype.card ι * (H₂ ^ (Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂) :=
        mul_le_mul_of_nonneg_left hinv (pow_nonneg hH₁0 _)
    _ = H₁ ^ Fintype.card ι * H₂ ^ (Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂ := by ring

theorem topRowsBound : NonDegTopRows := by
  intro C k m f b v NT hC hk hm hb hv hvb hkb hNT hNTb
  have hb0 : 0 < b := by linarith
  have hC0 : 0 < C := by linarith
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hf0 : (0:ℝ) ≤ f := Nat.cast_nonneg f
  have hv0 : 0 < v := by linarith
  have hNT0 : 0 < NT := by linarith
  have hL : 0.69 < Real.log b := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num) hb
    linarith
  have hL0 : 0 ≤ Real.log b := by linarith
  obtain ⟨H, hH⟩ : ∃ H, H = b ^ (C * (m:ℝ) ^ 2 * f) := ⟨_, rfl⟩
  rw [← hH]
  have hH0 : 0 < H := by rw [hH]; exact Real.rpow_pos_of_pos hb0 _
  have hlogH : Real.log H = C * (m:ℝ) ^ 2 * f * Real.log b := by rw [hH, Real.log_rpow hb0]
  have hlogk : Real.log k ≤ C * Real.log b := by
    have h := Real.log_le_log hk0 hkb
    rwa [Real.log_rpow hb0] at h
  have hlogv : Real.log v ≤ Real.log b := Real.log_le_log hv0 hvb
  have hlogNT : Real.log NT ≤ C * m * f * Real.log b := by
    have h := Real.log_le_log hNT0 hNTb
    rwa [Real.log_rpow hb0] at h
  have hlogC : Real.log C ≤ C := by
    have := Real.log_le_sub_one_of_pos hC0; linarith
  have hX0 : 0 < H * NT := mul_pos hH0 hNT0
  have p1 : 0 < (C * (k:ℝ) ^ 2 * v) ^ (k * f) := pow_pos (by positivity) _
  have p2 : 0 < (H * NT) ^ (C * (k:ℝ)) := Real.rpow_pos_of_pos hX0 _
  have p3 : 0 < H ^ (C * (k:ℝ) * (m:ℝ) ^ 2) := Real.rpow_pos_of_pos hH0 _
  have e1 : Real.log ((C * (k:ℝ) ^ 2 * v) ^ (k * f)) =
      ((k:ℝ) * f) * (Real.log C + 2 * Real.log k + Real.log v) := by
    rw [Real.log_pow, Real.log_mul (mul_pos hC0 (pow_pos hk0 2)).ne' hv0.ne',
      Real.log_mul hC0.ne' (pow_pos hk0 2).ne', Real.log_pow]
    push_cast; try ring
  have e2 : Real.log ((H * NT) ^ (C * (k:ℝ))) = C * k * (C * (m:ℝ) ^ 2 * f * Real.log b + Real.log NT) := by
    rw [Real.log_rpow hX0, Real.log_mul hH0.ne' hNT0.ne', hlogH]
  have e3 : Real.log (H ^ (C * (k:ℝ) * (m:ℝ) ^ 2)) = C * k * (m:ℝ) ^ 2 * (C * (m:ℝ) ^ 2 * f * Real.log b) := by
    rw [Real.log_rpow hH0, hlogH]
  have hpos := mul_pos (mul_pos p1 p2) p3
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul (mul_pos p1 p2).ne' p3.ne', Real.log_mul p1.ne' p2.ne', e1, e2, e3]
  have hK : 0 ≤ (k:ℝ) * f := mul_nonneg hk0.le hf0
  have hu1 : 1 ≤ C ^ 2 * (m:ℝ) ^ 4 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC) (one_le_pow₀ hm1)
  have hCu : C ≤ C ^ 2 * (m:ℝ) ^ 4 := by
    calc C = C * 1 := (mul_one C).symm
      _ ≤ C * (C * (m:ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hm1)) hC0.le
      _ = C ^ 2 * (m:ℝ) ^ 4 := by ring
  have hm24 : (m:ℝ) ^ 2 ≤ (m:ℝ) ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
  have hm14 : (m:ℝ) ≤ (m:ℝ) ^ 4 := by
    calc (m:ℝ) = (m:ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (m:ℝ) ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
  have hKu : 0 ≤ (k:ℝ) * f * (C ^ 2 * (m:ℝ) ^ 4) := by positivity
  have hP5 : 0 ≤ C ^ 2 * (k:ℝ) * f * Real.log b := by positivity
  have hCk0 : 0 ≤ C * (k:ℝ) := by positivity
  have F1 := mul_le_mul_of_nonneg_left hlogC hK
  have KoszulLowersPower := mul_le_mul_of_nonneg_left hCu hK
  have KoszulImageInIdeal := mul_le_mul_of_nonneg_left hL.le hKu
  have F3 := mul_le_mul_of_nonneg_left hlogk hK
  have F3b := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCu hL0) hK
  have F4 := mul_le_mul_of_nonneg_left hlogv hK
  have F4b := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hL0 hu1) hK
  have F5 := mul_le_mul_of_nonneg_left hm24 hP5
  have F6 := mul_le_mul_of_nonneg_left hlogNT hCk0
  have DiagonalTruncatedIntegralZero := mul_le_mul_of_nonneg_left hm14 hP5
  linarith

end Formalism.HermitianLatticeCounting.P
