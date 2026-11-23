import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open PowerSeries

section TruncEval

variable {S : Type*} [CommRing S] [Algebra ℚ S]

theorem aeval_trunc_coe_of_pow_eq_zero {n : ℕ} {s : S} (hs : s ^ n = 0) (P : Polynomial ℚ) :
    Polynomial.aeval s (trunc n (P : ℚ⟦X⟧)) = Polynomial.aeval s P := by
  have hdvd : Polynomial.X ^ n ∣ P - trunc n (P : ℚ⟦X⟧) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, coeff_trunc, if_pos hd, Polynomial.coeff_coe, sub_self]
  obtain ⟨Q, hQ⟩ := hdvd
  have h := congrArg (Polynomial.aeval s) hQ
  rw [map_sub, map_mul, map_pow, Polynomial.aeval_X, hs, zero_mul, sub_eq_zero] at h
  exact h.symm

def truncEval {n : ℕ} (s : S) (hs : s ^ n = 0) : ℚ⟦X⟧ →ₐ[ℚ] S where
  toFun f := Polynomial.aeval s (trunc n f)
  map_one' := by
    rcases n with _ | n
    · have : Subsingleton S := subsingleton_of_zero_eq_one (by simpa using hs.symm)
      exact Subsingleton.elim _ _
    · rw [← Polynomial.coe_one, aeval_trunc_coe_of_pow_eq_zero hs, map_one]
  map_mul' f g := by
    rw [← trunc_trunc_mul_trunc, ← Polynomial.coe_mul, aeval_trunc_coe_of_pow_eq_zero hs, map_mul]
  map_zero' := by
    rw [map_zero, map_zero]
  map_add' f g := by
    rw [map_add, map_add]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, ← Polynomial.coe_one,
      aeval_trunc_coe_of_pow_eq_zero hs, map_one, ← Algebra.algebraMap_eq_smul_one]

theorem truncEval_apply {n : ℕ} (s : S) (hs : s ^ n = 0) (f : ℚ⟦X⟧) :
    truncEval s hs f = Polynomial.aeval s (trunc n f) := rfl

theorem truncEval_eq_sum {n : ℕ} (s : S) (hs : s ^ n = 0) (f : ℚ⟦X⟧) :
    truncEval s hs f = ∑ i ∈ Finset.range n, algebraMap ℚ S (coeff i f) * s ^ i := by
  rcases n with _ | n
  · have : Subsingleton S := subsingleton_of_zero_eq_one (by simpa using hs.symm)
    exact Subsingleton.elim _ _
  · rw [truncEval_apply, Polynomial.aeval_eq_sum_range' (natDegree_trunc_lt f n)]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [coeff_trunc, if_pos (Finset.mem_range.1 hi), Algebra.smul_def]

@[simp]
theorem truncEval_X {n : ℕ} (s : S) (hs : s ^ n = 0) : truncEval s hs X = s := by
  rcases n with _ | _ | n
  · have : Subsingleton S := subsingleton_of_zero_eq_one (by simpa using hs.symm)
    exact Subsingleton.elim _ _
  · rw [pow_one] at hs
    rw [truncEval_eq_sum, Finset.sum_range_one, coeff_zero_X, map_zero, zero_mul, hs]
  · rw [truncEval_apply, trunc_X, Polynomial.aeval_X]

theorem truncEval_unique {n : ℕ} (ψ : ℚ⟦X⟧ →ₐ[ℚ] S) (s : S) (hs : s ^ n = 0) (hψ : ψ X = s) :
    ψ = truncEval s hs := by
  have hpoly : (ψ.comp (Polynomial.coeToPowerSeries.algHom ℚ)) = Polynomial.aeval s := by
    apply Polynomial.algHom_ext
    simp [hψ]
  ext f
  obtain ⟨h, hh⟩ : X ^ n ∣ f - (trunc n f : ℚ⟦X⟧) := by
    rw [X_pow_dvd_iff]
    intro m hm
    rw [map_sub, Polynomial.coeff_coe, coeff_trunc, if_pos hm, sub_self]
  have h1 : ψ f = ψ (trunc n f : ℚ⟦X⟧) := by
    have := congrArg ψ hh
    rw [map_sub, map_mul, map_pow, hψ, hs, zero_mul, sub_eq_zero] at this
    exact this
  rw [h1, truncEval_apply]
  exact congrArg (fun F : Polynomial ℚ →ₐ[ℚ] S => F (trunc n f)) hpoly

end TruncEval

section SeriesEval

variable {B : Type*} [CommRing B] (I : Ideal B)

theorem eq_of_forall_sub_mem_pow [IsHausdorff I B] {x y : B} (h : ∀ n, x - y ∈ I ^ n) : x = y := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff I B) (x - y) fun n => ?_
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  exact h n

theorem pow_mk_eq_zero {z : B} (hz : z ∈ I) (n : ℕ) :
    (Ideal.Quotient.mk (I ^ n) z) ^ n = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hz n

variable [Algebra ℚ B]

theorem factorₐ_comp_truncEval {z : B} (hz : z ∈ I) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorₐ ℚ (Ideal.pow_le_pow_right hle)).comp
        (truncEval (Ideal.Quotient.mk (I ^ n) z) (pow_mk_eq_zero I hz n)) =
      truncEval (Ideal.Quotient.mk (I ^ m) z) (pow_mk_eq_zero I hz m) := by
  apply truncEval_unique
  rw [AlgHom.comp_apply, truncEval_X]
  rfl

variable [IsAdicComplete I B]

def seriesEval (z : B) (hz : z ∈ I) : ℚ⟦X⟧ →ₐ[ℚ] B :=
  IsAdicComplete.liftAlgHom I
    (fun n => truncEval (Ideal.Quotient.mk (I ^ n) z) (pow_mk_eq_zero I hz n))
    (fun hle => factorₐ_comp_truncEval I hz hle)

variable {I}

theorem mk_seriesEval {z : B} (hz : z ∈ I) (f : ℚ⟦X⟧) (n : ℕ) :
    Ideal.Quotient.mk (I ^ n) (seriesEval I z hz f) =
      Ideal.Quotient.mk (I ^ n) (∑ i ∈ Finset.range n, algebraMap ℚ B (coeff i f) * z ^ i) := by
  have h := IsAdicComplete.mk_liftAlgHom I
    (fun n => truncEval (Ideal.Quotient.mk (I ^ n) z) (pow_mk_eq_zero I hz n))
    (fun hle => factorₐ_comp_truncEval I hz hle) n f
  rw [seriesEval, h, truncEval_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

theorem seriesEval_sub_sum_mem {z : B} (hz : z ∈ I) (f : ℚ⟦X⟧) (n : ℕ) :
    seriesEval I z hz f - ∑ i ∈ Finset.range n, algebraMap ℚ B (coeff i f) * z ^ i ∈ I ^ n :=
  Ideal.Quotient.eq.1 (mk_seriesEval hz f n)

theorem tendsto_seriesEval {z : B} (hz : z ∈ I) (f : ℚ⟦X⟧) :
    @Filter.Tendsto ℕ B (fun n => ∑ i ∈ Finset.range n, algebraMap ℚ B (coeff i f) * z ^ i)
      Filter.atTop (@nhds B I.adicTopology (seriesEval I z hz f)) := by
  let _ := I.adicTopology
  rw [(Ideal.hasBasis_nhds_adic I (seriesEval I z hz f)).tendsto_right_iff]
  intro n _
  filter_upwards [Filter.eventually_ge_atTop n] with N hN
  refine ⟨_, Ideal.pow_le_pow_right hN (neg_mem (seriesEval_sub_sum_mem hz f N)), ?_⟩
  simp

@[simp]
theorem seriesEval_X {z : B} (hz : z ∈ I) : seriesEval I z hz X = z := by
  refine eq_of_forall_sub_mem_pow I fun n => ?_
  refine Ideal.pow_le_pow_right (Nat.le_add_right n 2) ?_
  have h := seriesEval_sub_sum_mem hz X (n + 2)
  rwa [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_eq_zero, coeff_zero_X,
    coeff_one_X, map_zero, map_one, zero_mul, add_zero, pow_one, one_mul, zero_add] at h
  intro i _
  rw [coeff_X, if_neg (by omega), map_zero, zero_mul]

theorem seriesEval_mem {z : B} (hz : z ∈ I) {f : ℚ⟦X⟧} (hf : constantCoeff f = 0) :
    seriesEval I z hz f ∈ I := by
  have h := seriesEval_sub_sum_mem hz f 1
  rwa [Finset.sum_range_one, coeff_zero_eq_constantCoeff_apply, hf, map_zero, zero_mul, sub_zero,
    pow_one] at h

theorem seriesEval_subst {z : B} (hz : z ∈ I) {g : ℚ⟦X⟧} (hg : constantCoeff g = 0) {w : B}
    (hw : w ∈ I) (hgw : seriesEval I z hz g = w) (f : ℚ⟦X⟧) :
    seriesEval I w hw f = seriesEval I z hz (f.subst g) := by
  have hS := HasSubst.of_constantCoeff_zero' hg
  have key : seriesEval I w hw = (seriesEval I z hz).comp (substAlgHom hS) := by
    refine IsAdicComplete.algHom_ext I fun n => ?_
    have hwn : (Ideal.Quotient.mkₐ ℚ (I ^ n) w) ^ n = 0 := pow_mk_eq_zero I hw n
    rw [truncEval_unique ((Ideal.Quotient.mkₐ ℚ (I ^ n)).comp (seriesEval I w hw)) _ hwn
      (by rw [AlgHom.comp_apply, seriesEval_X]),
      truncEval_unique ((Ideal.Quotient.mkₐ ℚ (I ^ n)).comp ((seriesEval I z hz).comp
        (substAlgHom hS))) _ hwn (by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, coe_substAlgHom, subst_X hS, hgw])]
  rw [key, AlgHom.comp_apply, coe_substAlgHom]

omit [IsAdicComplete I B] in

theorem map_partialSum {B' : Type*} [CommRing B'] [Algebra ℚ B'] (F : B →+* B') (z : B)
    (f : ℚ⟦X⟧) (n : ℕ) :
    F (∑ i ∈ Finset.range n, algebraMap ℚ B (coeff i f) * z ^ i) =
      ∑ i ∈ Finset.range n, algebraMap ℚ B' (coeff i f) * F z ^ i := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, RingHom.map_rat_algebraMap]

theorem map_seriesEval {B' : Type*} [CommRing B'] [Algebra ℚ B'] {I' : Ideal B'}
    [IsAdicComplete I' B'] (F : B →+* B') (hF : I.map F ≤ I') {z : B} (hz : z ∈ I)
    (hFz : F z ∈ I') (f : ℚ⟦X⟧) : F (seriesEval I z hz f) = seriesEval I' (F z) hFz f := by
  refine eq_of_forall_sub_mem_pow I' fun n => ?_
  have h1 : F (seriesEval I z hz f - ∑ i ∈ Finset.range n, algebraMap ℚ B (coeff i f) * z ^ i) ∈
      I' ^ n := by
    have := Ideal.mem_map_of_mem F (seriesEval_sub_sum_mem hz f n)
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hF n this
  have h2 := seriesEval_sub_sum_mem hFz f n
  rw [map_sub, map_partialSum] at h1
  have := sub_mem h1 h2
  rwa [sub_sub_sub_cancel_right] at this

end SeriesEval

section Log

theorem one_add_X_mul_geom : (1 + X : ℚ⟦X⟧) * mk (fun n => algebraMap ℚ ℚ ((-1) ^ n)) = 1 := by
  ext n
  rw [add_mul, one_mul, map_add, coeff_one]
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_mk, coeff_mk, if_neg (Nat.succ_ne_zero n)]
    simp [pow_succ]

theorem log_subst_one_add_X_pow_sub_one (k : ℕ) :
    (log ℚ).subst ((1 + X) ^ k - 1 : ℚ⟦X⟧) = (k : ℚ⟦X⟧) * log ℚ := by
  have hg : constantCoeff ((1 + X) ^ k - 1 : ℚ⟦X⟧) = 0 := by simp
  have hS := HasSubst.of_constantCoeff_zero' hg
  apply derivative.ext
  · set G : ℚ⟦X⟧ := mk (fun n => algebraMap ℚ ℚ ((-1) ^ n)) with hG
    have hsub : ((1 + X : ℚ⟦X⟧) ^ k) * G.subst ((1 + X) ^ k - 1 : ℚ⟦X⟧) = 1 := by
      have h := congrArg (substAlgHom hS) one_add_X_mul_geom
      rw [map_mul, map_one, map_add, map_one, coe_substAlgHom, subst_X hS, add_sub_cancel] at h
      exact h
    rw [derivative_subst hS, deriv_log, ← hG]
    have hd : d⁄dX ℚ ((k : ℚ⟦X⟧) * log ℚ) = (k : ℚ⟦X⟧) * G := by
      rw [Derivation.leibniz, deriv_log, ← hG, Derivation.map_natCast, smul_zero, add_zero,
        smul_eq_mul]
    rw [hd, map_sub, derivative_pow, derivative_one, sub_zero, map_add, derivative_one,
      derivative_X, zero_add, mul_one]
    have hne : ((1 + X : ℚ⟦X⟧) ^ k) ≠ 0 := by
      refine pow_ne_zero _ fun h => ?_
      have := congrArg constantCoeff h
      simp at this
    apply mul_left_cancel₀ hne
    rcases k with _ | k
    · simp
    · have h1 : (1 + X : ℚ⟦X⟧) * G = 1 := one_add_X_mul_geom
      calc (1 + X : ℚ⟦X⟧) ^ (k + 1) * (G.subst ((1 + X) ^ (k + 1) - 1 : ℚ⟦X⟧) *
              (((k + 1 : ℕ) : ℚ⟦X⟧) * (1 + X) ^ (k + 1 - 1)))
          = ((1 + X : ℚ⟦X⟧) ^ (k + 1) * G.subst ((1 + X) ^ (k + 1) - 1 : ℚ⟦X⟧)) *
              (((k + 1 : ℕ) : ℚ⟦X⟧) * (1 + X) ^ k) := by rw [Nat.add_sub_cancel]; ring
        _ = ((k + 1 : ℕ) : ℚ⟦X⟧) * (1 + X) ^ k * ((1 + X) * G) := by rw [hsub, h1]; ring
        _ = (1 + X : ℚ⟦X⟧) ^ (k + 1) * (((k + 1 : ℕ) : ℚ⟦X⟧) * G) := by ring
  · have h0 : MvPowerSeries.constantCoeff ((1 + X) ^ k - 1 : ℚ⟦X⟧) = 0 := hg
    have := constantCoeff_subst_eq_zero h0 (log ℚ) constantCoeff_log
    rw [map_mul, constantCoeff_log, mul_zero]
    exact this

variable {B : Type*} [CommRing B] [Algebra ℚ B] {I : Ideal B} [IsAdicComplete I B]

variable (I) in

def logOnePlus (z : B) (hz : z ∈ I) : B :=
  seriesEval I z hz (log ℚ)

theorem logOnePlus_sub_sum_mem {z : B} (hz : z ∈ I) (n : ℕ) :
    logOnePlus I z hz - ∑ i ∈ Finset.Ico 1 n, algebraMap ℚ B ((-1) ^ (i + 1) / i) * z ^ i ∈
      I ^ n := by
  have hs : ∑ i ∈ Finset.Ico 1 n, algebraMap ℚ B ((-1) ^ (i + 1) / i) * z ^ i =
      ∑ i ∈ Finset.range n, algebraMap ℚ B (coeff i (log ℚ)) * z ^ i := by
    rcases n with _ | n
    · simp
    · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos n), coeff_log,
        if_pos rfl, map_zero, zero_mul, zero_add]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [coeff_log, if_neg (by have := (Finset.mem_Ico.1 hi).1; omega), Algebra.algebraMap_self,
        RingHom.id_apply]
  rw [hs]
  exact seriesEval_sub_sum_mem hz (log ℚ) n

theorem logOnePlus_mem {z : B} (hz : z ∈ I) : logOnePlus I z hz ∈ I :=
  seriesEval_mem hz constantCoeff_log

theorem logOnePlus_eq_mul {z : B} (hz : z ∈ I) : ∃ u, u - 1 ∈ I ∧ logOnePlus I z hz = z * u := by
  set h : ℚ⟦X⟧ := mk fun n => coeff (n + 1) (log ℚ)
  have hlog : log ℚ = X * h := by
    conv_lhs => rw [eq_X_mul_shift_add_const (log ℚ)]
    rw [constantCoeff_log, map_zero, add_zero]
  refine ⟨seriesEval I z hz h, ?_, ?_⟩
  · have h1 := seriesEval_sub_sum_mem hz h 1
    rwa [Finset.sum_range_one, pow_zero, mul_one, pow_one, coeff_mk, zero_add, coeff_one_log,
      map_one] at h1
  · rw [logOnePlus, hlog, map_mul, seriesEval_X]

theorem logOnePlus_pow {z : B} (hz : z ∈ I) (k : ℕ) (hk : (1 + z) ^ k - 1 ∈ I) :
    logOnePlus I ((1 + z) ^ k - 1) hk = k * logOnePlus I z hz := by
  have hg : constantCoeff ((1 + X) ^ k - 1 : ℚ⟦X⟧) = 0 := by simp
  rw [logOnePlus, seriesEval_subst hz hg hk (by simp), log_subst_one_add_X_pow_sub_one, map_mul,
    map_natCast, logOnePlus]

end Log

end GroundTheory.PAdicHodge
