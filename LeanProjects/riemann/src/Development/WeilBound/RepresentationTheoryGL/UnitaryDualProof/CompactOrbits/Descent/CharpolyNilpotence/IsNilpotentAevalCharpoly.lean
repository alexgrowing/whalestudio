import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVan

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.T.Desc.JC

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc

variable {k : Type} [Field k] {n : ℕ}

theorem trace_aeval_eq_sum (A : Matrix (Fin n) (Fin n) k) (p : k[X]) :
    trace (aeval A p) = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * trace (A ^ i) := by
  rw [aeval_eq_sum_range, Matrix.trace_sum]
  simp only [Matrix.trace_smul, smul_eq_mul]

theorem isNilpotent_of_trace_pow [CharZero k] (A : Matrix (Fin n) (Fin n) k)
    (h : ∀ m, 1 ≤ m → trace (A ^ m) = 0) : IsNilpotent A := by
  obtain ⟨q, hq, hXq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd A.charpoly
    (charpoly_monic A).ne_zero 0
  simp only [map_zero, sub_zero] at hq hXq
  set r := rootMultiplicity 0 A.charpoly
  have hcop : IsCoprime (X ^ (r + 1) : k[X]) q :=
    IsCoprime.pow_left ((Polynomial.irreducible_X.coprime_iff_not_dvd).2 hXq)
  obtain ⟨a, b, hab⟩ := hcop
  have hzero : aeval A (X ^ (r + 1) * q) = 0 := by
    have e : (X ^ (r + 1) * q : k[X]) = X * A.charpoly := by
      rw [hq]
      ring
    rw [e, map_mul, aeval_self_charpoly, mul_zero]
  have hsum : aeval A (a * X ^ (r + 1)) + aeval A (b * q) = 1 := by
    rw [← map_add, hab, map_one]
  have hprod : aeval A (a * X ^ (r + 1)) * aeval A (b * q) = 0 := by
    rw [← map_mul]
    have e : a * X ^ (r + 1) * (b * q) = (a * b) * (X ^ (r + 1) * q) := by ring
    rw [e, map_mul, hzero, mul_zero]
  have he : aeval A (a * X ^ (r + 1)) = 1 - aeval A (b * q) := eq_sub_of_add_eq hsum
  have hidem : IsIdempotentElem (aeval A (a * X ^ (r + 1))) := by
    unfold IsIdempotentElem
    calc aeval A (a * X ^ (r + 1)) * aeval A (a * X ^ (r + 1))
        = aeval A (a * X ^ (r + 1)) * (1 - aeval A (b * q)) := by rw [← he]
      _ = aeval A (a * X ^ (r + 1)) := by rw [mul_sub, mul_one, hprod, sub_zero]
  have htr : trace (aeval A (a * X ^ (r + 1))) = 0 := by
    rw [trace_aeval_eq_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases i with _ | i
    · simp [coeff_mul_X_pow']
    · rw [h (i + 1) (by omega), mul_zero]
  have hlin : IsIdempotentElem (Matrix.toLinAlgEquiv' (aeval A (a * X ^ (r + 1)))) :=
    hidem.map _
  have hlintr : LinearMap.trace k _ (Matrix.toLinAlgEquiv' (aeval A (a * X ^ (r + 1)))) = 0 := by
    rw [LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n)), LinearMap.toMatrix_eq_toMatrix']
    change trace (LinearMap.toMatrix' (Matrix.toLin' _)) = 0
    rw [LinearMap.toMatrix'_toLin', htr]
  have hz : aeval A (a * X ^ (r + 1)) = 0 := by
    have := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hlin hlintr
    exact (map_eq_zero_iff _ (AlgEquiv.injective _)).1 this
  refine ⟨r + 1, ?_⟩
  have e : (X ^ (r + 1) : k[X]) = X ^ (r + 1) * (a * X ^ (r + 1)) + b * (X ^ (r + 1) * q) := by
    linear_combination (-(X ^ (r + 1) : k[X])) * hab
  have := congrArg (aeval A) e
  rw [map_add, map_mul (aeval A) (X ^ (r + 1)), hz, map_mul (aeval A) b, hzero, mul_zero, mul_zero,
    add_zero, map_pow, aeval_X] at this
  exact this

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem trace_pow_eq {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {x x₀ : Matrix (Fin n) (Fin n) k}
    (h : pZ Z x = pZ Z x₀) (i : ℕ) (hi : i < 2 * n + 1) : trace (x ^ i) = trace (x₀ ^ i) := by
  have h1 : ((1 : Z) : Matrix (Fin n) (Fin n) k) =
      ∑ j, (Module.finBasis k Z).repr 1 j • ((Module.finBasis k Z j : Z) : Matrix (Fin n) (Fin n) k) := by
    have h0 := congrArg Subtype.val ((Module.finBasis k Z).sum_repr 1)
    rw [← h0, AddSubmonoidClass.coe_finset_sum]
    rfl
  have key : ∀ y : Matrix (Fin n) (Fin n) k, trace (y ^ i) =
      ∑ j, (Module.finBasis k Z).repr 1 j * pZ Z y (⟨i, hi⟩, j) := by
    intro y
    calc trace (y ^ i) = trace (((1 : Z) : Matrix (Fin n) (Fin n) k) * y ^ i) := by simp
      _ = _ := by
        rw [h1, Finset.sum_mul, Matrix.trace_sum]
        simp [pZ, smul_mul_assoc, Matrix.trace_smul]
  rw [key x, key x₀, h]

theorem trace_aeval_eq {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {x x₀ : Matrix (Fin n) (Fin n) k}
    (h : pZ Z x = pZ Z x₀) (p : k[X]) (hp : p.natDegree ≤ 2 * n) :
    trace (aeval x p) = trace (aeval x₀ p) := by
  rw [trace_aeval_eq_sum, trace_aeval_eq_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [trace_pow_eq h i (by simp at hi; omega)]

private theorem trace_aeval_eq_of_pZ_eq {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}
    {x x₀ : Matrix (Fin n) (Fin n) k} (h : pZ Z x = pZ Z x₀) (p : k[X]) :
    trace (aeval x p) = trace (aeval x₀ p) := by
  have hM : (x.charpoly * x₀.charpoly).Monic := (charpoly_monic x).mul (charpoly_monic x₀)
  have hdeg : (x.charpoly * x₀.charpoly).natDegree = 2 * n := by
    rw [(charpoly_monic x).natDegree_mul (charpoly_monic x₀), charpoly_natDegree_eq_dim,
      charpoly_natDegree_eq_dim, Fintype.card_fin]
    ring
  have hx : aeval x (x.charpoly * x₀.charpoly) = 0 := by
    rw [map_mul, aeval_self_charpoly, zero_mul]
  have hx0 : aeval x₀ (x.charpoly * x₀.charpoly) = 0 := by
    rw [map_mul, aeval_self_charpoly, mul_zero]
  rw [← aeval_modByMonic_eq_self_of_root hx, ← aeval_modByMonic_eq_self_of_root hx0]
  exact trace_aeval_eq h _ ((natDegree_modByMonic_le p hM).trans hdeg.le)

theorem isNilpotent_aeval_charpoly [CharZero k] {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}
    {x x₀ : Matrix (Fin n) (Fin n) k} (h : pZ Z x = pZ Z x₀) : IsNilpotent (aeval x x₀.charpoly) := by
  apply isNilpotent_of_trace_pow
  intro m hm
  rw [← map_pow, trace_aeval_eq_of_pZ_eq h, map_pow, aeval_self_charpoly, zero_pow (by omega),
    Matrix.trace_zero]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem pow_eq_zero_of_isNilpotent {N : Matrix (Fin n) (Fin n) k} (hN : IsNilpotent N) : N ^ n = 0 := by
  have h := isNilpotent_charpoly_sub_pow_of_isNilpotent hN
  have h0 : N.charpoly - X ^ Fintype.card (Fin n) = 0 := h.eq_zero
  rw [sub_eq_zero, Fintype.card_fin] at h0
  have := aeval_self_charpoly N
  rwa [h0, map_pow, aeval_X] at this

theorem jcPoly [CharZero k] : JCPoly (k := k) := by
  classical
  unfold JCPoly
  intro m Z _ y
  by_cases hex : ∃ x₀ ∈ Bz Z, pZ Z x₀ = y
  · obtain ⟨x₀, -, rfl⟩ := hex
    have hsq : Squarefree (UniqueFactorizationMonoid.radical x₀.charpoly) :=
      UniqueFactorizationMonoid.squarefree_radical
    have hsep : (UniqueFactorizationMonoid.radical x₀.charpoly).Separable :=
      PerfectField.separable_iff_squarefree.mpr hsq
    obtain ⟨N, c, hc⟩ := (UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd
      (charpoly_monic x₀).ne_zero).mpr dvd_rfl
    set Q := UniqueFactorizationMonoid.radical x₀.charpoly
    obtain ⟨a, b, hab⟩ := hsep
    set T : k[X] := X - b * Q
    have hT : ∀ z : k[X], T.comp z = z + -(b.comp z * Q.comp z) := by
      intro z
      simp [T, sub_comp, mul_comp, sub_eq_add_neg]
    have e1 : ∀ p w : k[X], (p.map C).eval w = p.comp w := fun p w => by
      rw [eval_map]
      rfl
    have step : ∀ z : k[X], ∃ w, Q.comp (T.comp z) = (Q.comp z) ^ 2 * w := by
      intro z
      obtain ⟨s, hs⟩ := Polynomial.binomExpansion (Q.map C) z (-(b.comp z * Q.comp z))
      refine ⟨a.comp z + s * (b.comp z) ^ 2, ?_⟩
      have hab' : a.comp z * Q.comp z + b.comp z * (derivative Q).comp z = 1 := by
        have := congrArg (fun p => p.comp z) hab
        simpa [add_comp, mul_comp] using this
      rw [derivative_map] at hs
      simp only [e1] at hs
      rw [hT, hs]
      linear_combination (-(Q.comp z)) * hab'
    have iter : ∀ j, ∃ w v, Q.comp ((fun p => T.comp p)^[j] X) = Q ^ (2 ^ j) * w ∧
        X - (fun p => T.comp p)^[j] X = Q * v := by
      intro j
      induction j with
      | zero => exact ⟨1, 0, by simp, by simp⟩
      | succ j ih =>
        obtain ⟨w, v, hw, hv⟩ := ih
        obtain ⟨w', hw'⟩ := step ((fun p => T.comp p)^[j] X)
        rw [Function.iterate_succ_apply']
        refine ⟨w ^ 2 * w', v + b.comp ((fun p => T.comp p)^[j] X) * Q ^ (2 ^ j - 1) * w, ?_, ?_⟩
        · rw [hw', hw, pow_succ (2 : ℕ) j, pow_mul]
          ring
        · have hQ : Q ^ (2 ^ j) = Q * Q ^ (2 ^ j - 1) := by
            rw [← pow_succ']
            congr 1
            have := Nat.one_le_two_pow (n := j)
            omega
          rw [hT, hw, hQ]
          linear_combination hv
    obtain ⟨w, v, hw, hv⟩ := iter m
    refine ⟨(fun p => T.comp p)^[m] X, fun x _ hx => ?_⟩
    have hQx : IsNilpotent (aeval x Q) := by
      have h5 := isNilpotent_aeval_charpoly hx
      have hpow : aeval x Q ^ N = aeval x x₀.charpoly * aeval x c := by
        rw [← map_pow, hc, map_mul]
      have hcomm : Commute (aeval x x₀.charpoly) (aeval x c) := by
        rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
      have : IsNilpotent (aeval x Q ^ N) := by
        rw [hpow]
        exact hcomm.isNilpotent_mul_right h5
      exact IsNilpotent.of_pow this
    have hQn : aeval x Q ^ m = 0 := pow_eq_zero_of_isNilpotent hQx
    constructor
    · apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq
      have h0 : aeval (aeval x ((fun p => T.comp p)^[m] X)) Q = 0 := by
        rw [← aeval_comp, hw, map_mul, map_pow]
        rw [pow_eq_zero_of_le (Nat.lt_two_pow_self).le hQn, zero_mul]
      change aeval (Matrix.toLinAlgEquiv' _) Q = 0
      rw [aeval_algEquiv, AlgHom.comp_apply, h0, map_zero]
    · have h1 : x - aeval x ((fun p => T.comp p)^[m] X) = aeval x Q * aeval x v := by
        rw [← map_mul, ← hv, map_sub, aeval_X]
      rw [h1]
      have hcomm : Commute (aeval x Q) (aeval x v) := by
        rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
      exact hcomm.isNilpotent_mul_right hQx
  · exact ⟨0, fun x hx hxy => absurd ⟨x, hx, hxy⟩ hex⟩

end PositivityTheory.RgUd.T.Desc.JC
