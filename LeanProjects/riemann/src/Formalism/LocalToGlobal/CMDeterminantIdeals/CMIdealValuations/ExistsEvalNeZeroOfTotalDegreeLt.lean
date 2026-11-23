import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG

noncomputable section

namespace Formalism.L2.LamCM

open MvPolynomial IsLocalRing

section SlopeTestRemainingChoices

theorem exists_eval_ne_zero_of_totalDegree_lt {k σ : Type} [Field k] [Finite σ] (p : MvPolynomial σ k) (hp : p ≠ 0)
    (S : Finset k) (hS : p.totalDegree < S.card) : ∃ x : σ → k, eval x p ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hp (eq_zero_of_eval_zero_at_prod_finset p (fun _ => S)
    (fun i => lt_of_le_of_lt (degreeOf_le_totalDegree p i) hS) (fun x _ => h x))

theorem exists_finset_card_gt {k : Type} (D : ℕ) (h : Infinite k ∨ D < Nat.card k) : ∃ S : Finset k, D < S.card := by
  rcases h with h | h
  · obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq k (D + 1)
    exact ⟨S, by omega⟩
  · have : Finite k := Nat.finite_of_card_ne_zero (by omega)
    have := Fintype.ofFinite k
    refine ⟨Finset.univ, ?_⟩
    rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]

theorem totalDegree_det_X_le {k σ : Type} [Field k] (n : ℕ) (f : Fin n → Fin n → σ) :
    (Matrix.of fun i j => (X (f i j) : MvPolynomial σ k)).det.totalDegree ≤ n := by
  rw [Matrix.det_apply]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s _ => ?_)
  rw [Units.smul_def]
  refine (totalDegree_smul_le _ _).trans ?_
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i, ((Matrix.of fun i j => (X (f i j) : MvPolynomial σ k)) (s i) i).totalDegree
      ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => by simp [totalDegree_X]
    _ = n := by simp

end SlopeTestRemainingChoices

section Subst

theorem coeff_aeval_scale {K σ : Type} [Field K] [Fintype σ] (c : σ → K) (F : MvPolynomial σ K) (μ : σ →₀ ℕ) :
    coeff μ (aeval (fun w => C (c w) * X w) F) = coeff μ F * ∏ w, c w ^ μ w := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial s a =>
    have hs : (s.prod fun i k => (C (c i) * X i) ^ k : MvPolynomial σ K) = C (∏ w, c w ^ s w) * monomial s 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), map_prod,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [mul_pow, map_pow]
    rw [aeval_monomial, hs, algebraMap_eq, ← mul_assoc, ← C_mul, coeff_C_mul,
      coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq, add_mul]

theorem substGauss : SubstGauss := by
  intro R K _ _ _ B _ m P U c hP hcU μ
  classical
  obtain ⟨P0, hP0⟩ : P ∈ Set.range (map (algebraMap R K)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨ν, -, rfl⟩ := mem_coeffs_iff.mp ha
    exact hP ν
  let g0 : FrVar m → MvPolynomial (FrVar m) R := fun v =>
    ∑ j, C (hcU v.1 j v.2.2).choose * X (⟨v.1, (v.2.1, j)⟩ : FrVar m)
  have key : aeval (fun w : FrVar m => C (c w.1 w.2.2) * X w) (substFr U P) = map (algebraMap R K) (bind₁ g0 P0) := by
    rw [map_bind₁, hP0, substFr, aeval_bind₁]
    change bind₁ _ P = bind₁ _ P
    refine congrArg (fun g => bind₁ g P) (funext fun v => ?_)
    simp only [g0, map_sum, map_mul, aeval_C, aeval_X, map_C, map_X, algebraMap_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hcU v.1 j v.2.2).choose_spec, C_mul]
    ring
  have h := coeff_aeval_scale (fun w : FrVar m => c w.1 w.2.2) (substFr U P) μ
  rw [key, coeff_map] at h
  exact ⟨_, h⟩

end Subst

section Core

theorem coeffIntegralOfUnitEval : LemmaGCore := by
  intro R K _ _ _ _ _ _ B _ m P hcard hval μ0
  classical
  by_contra hμ0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) P.support (fun μ => coeff μ P)
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨n, u, hbu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hex : ∃ e : ℕ, ∀ μ, algebraMap R K (ϖ ^ e) * coeff μ P ∈ Set.range (algebraMap R K) := by
    refine ⟨n, fun μ => ?_⟩
    by_cases hμ : μ ∈ P.support
    · obtain ⟨r, hr⟩ := hb μ hμ
      refine ⟨(↑u⁻¹ : R) * r, ?_⟩
      rw [map_mul, hr, Algebra.smul_def, hbu, map_mul, ← mul_assoc, ← mul_assoc, ← map_mul, Units.inv_mul, map_one,
        one_mul]
    · rw [notMem_support_iff.mp hμ, mul_zero]
      exact ⟨0, map_zero _⟩
  set e := Nat.find hex with he_def
  have he : ∀ μ, algebraMap R K (ϖ ^ e) * coeff μ P ∈ Set.range (algebraMap R K) := Nat.find_spec hex
  have he0 : e ≠ 0 := by
    intro h0
    apply hμ0
    simpa [h0] using he μ0
  have hmin : ¬ ∀ μ, algebraMap R K (ϖ ^ (e - 1)) * coeff μ P ∈ Set.range (algebraMap R K) :=
    Nat.find_min hex (by omega)
  push Not at hmin
  obtain ⟨μ1, hμ1⟩ := hmin

  obtain ⟨Q, hQ⟩ : C (algebraMap R K (ϖ ^ e)) * P ∈ Set.range (map (algebraMap R K)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨ν, -, rfl⟩ := mem_coeffs_iff.mp ha
    rw [coeff_C_mul]
    exact he ν
  have hQc : ∀ μ, algebraMap R K (coeff μ Q) = algebraMap R K (ϖ ^ e) * coeff μ P := by
    intro μ
    rw [← coeff_map, hQ, coeff_C_mul]
  have hu1 : IsUnit (coeff μ1 Q) := by
    by_contra hnu
    have hmem : coeff μ1 Q ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
    obtain ⟨t, ht⟩ := hmem
    apply hμ1
    refine ⟨t, ?_⟩
    have hϖK : algebraMap R K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ0
    apply mul_left_cancel₀ hϖK
    rw [← map_mul, mul_comm, ht, hQc, ← mul_assoc, ← map_mul, ← pow_succ', Nat.sub_add_cancel (by omega)]

  set Qb : MvPolynomial (FrVar m) (ResidueField R) := map (residue R) Q with hQb
  let Dt : MvPolynomial (FrVar m) (ResidueField R) :=
    ∏ b, (Matrix.of fun (k i : Fin (m b)) => (X (⟨b, (i, k)⟩ : FrVar m) : MvPolynomial (FrVar m) (ResidueField R))).det
  have hDt : ∀ x : FrVar m → ResidueField R,
      eval x Dt = ∏ b, (Matrix.of fun (k i : Fin (m b)) => x ⟨b, (i, k)⟩).det := by
    intro x
    simp only [Dt, map_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext k i
    simp [RingHom.mapMatrix_apply]
  have hQb0 : Qb ≠ 0 := by
    intro h0
    have := congrArg (coeff μ1) h0
    rw [hQb, coeff_map, coeff_zero] at this
    exact (residue_ne_zero_iff_isUnit _).mpr hu1 this
  have hDt0 : Dt ≠ 0 := by
    intro h0
    have := hDt (fun v => if v.2.1 = v.2.2 then 1 else 0)
    rw [h0, map_zero] at this
    have h1 : ∀ b, (Matrix.of fun (k i : Fin (m b)) =>
        (fun v : FrVar m => if v.2.1 = v.2.2 then (1 : ResidueField R) else 0) ⟨b, (i, k)⟩) = 1 := by
      intro b
      ext k i
      simp [Matrix.one_apply, eq_comm]
    simp only [h1, Matrix.det_one, Finset.prod_const_one] at this
    exact zero_ne_one this
  have hdeg : (Qb * Dt).totalDegree ≤ P.totalDegree + ∑ b, m b := by
    refine (totalDegree_mul _ _).trans (add_le_add ?_ ?_)
    · have hsub : Qb.support ⊆ P.support := by
        intro μ hμ
        rw [mem_support_iff] at hμ ⊢
        intro hP0
        apply hμ
        rw [hQb, coeff_map]
        have : coeff μ Q = 0 := hinj (by rw [hQc, hP0, mul_zero, map_zero])
        rw [this, map_zero]
      unfold totalDegree
      exact Finset.sup_mono hsub
    · refine (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      exact totalDegree_det_X_le (m b) _
  obtain ⟨S, hS⟩ := exists_finset_card_gt (k := ResidueField R) _ hcard
  obtain ⟨x, hx⟩ := exists_eval_ne_zero_of_totalDegree_lt (Qb * Dt) (mul_ne_zero hQb0 hDt0) S (by omega)
  rw [map_mul, hDt, mul_ne_zero_iff, Finset.prod_ne_zero_iff] at hx
  obtain ⟨hxQ, hxD⟩ := hx

  choose y hy using fun v => residue_surjective (R := R) (x v)
  let Xf : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R := fun b => Matrix.of fun k i => y ⟨b, (i, k)⟩
  have hdet : ∀ b, IsUnit (Xf b).det := by
    intro b
    rw [← residue_ne_zero_iff_isUnit, RingHom.map_det]
    convert hxD b (Finset.mem_univ _) using 2
    ext k i
    simp [Xf, RingHom.mapMatrix_apply, hy]
  have hyx : (residue R) ∘ y = x := funext hy
  have hQy : IsUnit (eval y Q) := by
    rw [← residue_ne_zero_iff_isUnit, map_eval, hyx]
    exact hxQ
  obtain ⟨r, hr⟩ := hval Xf hdet
  have hev : evalFr P (fun b => (Xf b).map (algebraMap R K)) = eval (algebraMap R K ∘ y) P := rfl
  have hyQ : eval y Q = ϖ ^ e * r := by
    apply hinj
    rw [map_eval, hQ, map_mul, eval_C, map_mul, hr, hev]
  rw [hyQ] at hQy
  exact hϖ.not_isUnit ((isUnit_pow_iff he0).mp (isUnit_of_mul_isUnit_left hQy))

end Core

section Descent

theorem LemmaG_of : BigResExt → LemmaG := by
  intro hB V K _ _ _ _ _ _ B _ m P hc hfin hW μ
  classical
  obtain ⟨W, _, _, _, _, hcW, hfinW, hN, hinj, hloc⟩ := hB V hc hfin (P.totalDegree + ∑ b, m b)
  have hg : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap V W)) :=
    (IsFractionRing.injective W (FractionRing W)).comp hinj
  let f : K →+* FractionRing W := IsFractionRing.lift hg
  have hf : ∀ a : V, f (algebraMap V K a) = algebraMap W (FractionRing W) (algebraMap V W a) :=
    fun a => IsFractionRing.lift_algebraMap hg a
  have hdeg : (map f P).totalDegree ≤ P.totalDegree := by
    unfold totalDegree
    exact Finset.sup_mono (support_map_subset f P)
  have hcoef := coeffIntegralOfUnitEval W (FractionRing W) B m (map f P) (Or.inr (by omega))
    (hW W (FractionRing W) f hcW hfinW hloc hf) μ
  rw [coeff_map] at hcoef
  obtain ⟨w, hw⟩ := hcoef
  set x := coeff μ P
  by_cases hx0 : x = 0
  · exact ⟨0, by rw [hx0, map_zero]⟩
  rcases ValuationRing.isInteger_or_isInteger V x with ⟨r, hr⟩ | ⟨y, hy⟩
  · exact ⟨r, hr⟩
  · by_cases hyu : IsUnit y
    · refine ⟨↑hyu.unit⁻¹, ?_⟩
      have h1 : algebraMap V K y * algebraMap V K ↑hyu.unit⁻¹ = 1 := by
        rw [← map_mul, ← map_one (algebraMap V K)]
        congr 1
        exact hyu.mul_val_inv
      rw [hy] at h1
      rw [← inv_inv x]
      exact (eq_inv_of_mul_eq_one_right h1)
    · exfalso
      apply hyu
      apply isUnit_of_map_unit (algebraMap V W) y
      have h1 : algebraMap W (FractionRing W) (w * algebraMap V W y) = algebraMap W (FractionRing W) 1 := by
        rw [map_mul, hw, ← hf, hy, ← map_mul, mul_inv_cancel₀ hx0, map_one, map_one]
      have h2 := IsFractionRing.injective W (FractionRing W) h1
      exact ⟨⟨algebraMap V W y, w, by rw [mul_comm]; exact h2, h2⟩, rfl⟩

end Descent

end Formalism.L2.LamCM
