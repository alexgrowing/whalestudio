import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FlagsAndDiagonals.WMConjDiagonal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem resFlag_field {k : Type} [Field k] (u T : M4 k) (d : Fin 4 → k) (hu : IsGSp 1 u)
    (hT : IsUp T) (e : Matrix.diagonal d * u = u * T) (hd : ∀ i j, lamW i ≠ lamW j → d i - T j j ≠ 0) :
    u 1 0 = 0 ∧ u 3 0 = 0 ∧ (u 0 0 ≠ 0 ∨ u 2 0 ≠ 0) ∧
      (u 0 0 ≠ 0 → u 0 0 * u 1 1 - u 0 1 * u 1 0 ≠ 0 ∧ u 0 0 * u 2 1 - u 0 1 * u 2 0 = 0) := by
  have t10 : T 1 0 = 0 := hT _ _ (by decide)
  have t20 : T 2 0 = 0 := hT _ _ (by decide)
  have t30 : T 3 0 = 0 := hT _ _ (by decide)
  have t21 : T 2 1 = 0 := hT _ _ (by decide)
  have t31 : T 3 1 = 0 := hT _ _ (by decide)
  have c0 : ∀ i, (d i - T 0 0) * u i 0 = 0 := fun i => by
    have := congrFun (congrFun e i) 0
    rw [Matrix.diagonal_mul, Matrix.mul_apply, Fin.sum_univ_four, t10, t20, t30] at this
    linear_combination this
  have c1 : ∀ i, (d i - T 1 1) * u i 1 = u i 0 * T 0 1 := fun i => by
    have := congrFun (congrFun e i) 1
    rw [Matrix.diagonal_mul, Matrix.mul_apply, Fin.sum_univ_four, t21, t31] at this
    linear_combination this
  have h10 : u 1 0 = 0 := (mul_eq_zero.1 (c0 1)).resolve_left (hd _ _ (by decide))
  have h30 : u 3 0 = 0 := (mul_eq_zero.1 (c0 3)).resolve_left (hd _ _ (by decide))
  have s := sp_adj_mul hu
  have s00 := congrFun (congrFun s 0) 0
  have s10 := congrFun (congrFun s 1) 0
  have s11 := congrFun (congrFun s 1) 1
  have s31 := congrFun (congrFun s 3) 1
  rw [Matrix.mul_apply, Fin.sum_univ_four] at s00 s10 s11 s31
  rw [Matrix.one_apply_eq] at s00 s11
  rw [Matrix.one_apply_ne (by decide)] at s10 s31
  have a30 : adj u 3 0 = - u 3 0 := by simp [adj_apply, sgn, Fin.rev]
  have a31 : adj u 3 1 = - u 2 0 := by simp [adj_apply, sgn, Fin.rev]
  have a32 : adj u 3 2 = u 1 0 := by simp [adj_apply, sgn, Fin.rev]
  have a33 : adj u 3 3 = u 0 0 := by simp [adj_apply, sgn, Fin.rev]
  rw [a30, a31, a32, a33] at s31
  refine ⟨h10, h30, ?_, fun h00 => ?_⟩
  · by_contra hn
    push Not at hn
    rw [hn.1, hn.2, h10, h30] at s00
    simp at s00
  · have hA : d 0 - T 1 1 ≠ 0 := hd _ _ (by decide)
    have hB : d 2 - T 1 1 ≠ 0 := hd _ _ (by decide)
    have key : u 0 0 * u 2 1 - u 0 1 * u 2 0 = 0 := by
      apply mul_left_cancel₀ (mul_ne_zero hA hB)
      linear_combination (d 0 - T 1 1) * u 0 0 * c1 2 - (d 2 - T 1 1) * u 2 0 * c1 0
        + u 2 0 * T 0 1 * c0 0 - u 0 0 * T 0 1 * c0 2
    refine ⟨fun hn => ?_, key⟩
    rw [h10, mul_zero, sub_zero] at hn
    have h11 : u 1 1 = 0 := (mul_eq_zero.1 hn).resolve_left h00
    rw [h10, h30, h11] at s31
    have h31 : u 3 1 = 0 := by
      apply mul_left_cancel₀ h00
      linear_combination s31
    rw [h10, h30] at s10
    rw [h11, h31] at s11
    apply h00
    linear_combination u 0 1 * s10 - u 0 0 * s11 + adj u 1 2 * key

theorem UpperTheory.V.Ws.Lab.resFlag :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (X u : M4 R) (d d' : Fin 4 → R), Cg (maximalIdeal R) X (Matrix.diagonal d) → IsGSp 1 u →
      IsUp (adj u * X * u) → (∀ i, (adj u * X * u : M4 R) i i - d' i ∈ maximalIdeal R) → (∀ i j, lamW i ≠ lamW j → IsUnit (d i - d' j)) →
      u 1 0 ∈ maximalIdeal R ∧ u 3 0 ∈ maximalIdeal R ∧ (IsUnit (u 0 0) ∨ IsUnit (u 2 0)) ∧
        (IsUnit (u 0 0) → IsUnit (u 0 0 * u 1 1 - u 0 1 * u 1 0) ∧ u 0 0 * u 2 1 - u 0 1 * u 2 0 ∈ maximalIdeal R) := by
  intro R _ _ X u d d' hX hu hUp hdi hsep
  have hX' : X.map (residue R) = Matrix.diagonal fun i => residue R (d i) := by
    ext i j
    have := (residue_eq_zero_iff _).2 (hX i j)
    rw [map_sub, sub_eq_zero] at this
    rw [Matrix.map_apply, this]
    by_cases e : i = j
    · subst e; simp
    · simp [Matrix.diagonal_apply_ne _ e]
  have hu' : IsGSp 1 (u.map (residue R)) := by simpa using gsp_map (residue R) hu
  have e : X * u = u * (adj u * X * u) := by
    rw [← mul_assoc, ← mul_assoc, sp_mul_adj hu, one_mul]
  have e' := congrArg (fun M : M4 R => M.map (residue R)) e
  beta_reduce at e'
  rw [Matrix.map_mul, Matrix.map_mul (L := u), hX'] at e'
  have H := resFlag_field (u.map (residue R)) ((adj u * X * u).map (residue R)) _ hu'
    (fun i j h => by rw [Matrix.map_apply, hUp i j h, map_zero]) e' (fun i j h => by
      have h1 := (residue_eq_zero_iff _).2 (hdi j)
      rw [map_sub, sub_eq_zero] at h1
      rw [Matrix.map_apply, h1, ← map_sub]
      exact ((hsep i j h).map _).ne_zero)
  simp only [Matrix.map_apply, ← map_mul, ← map_sub, residue_eq_zero_iff, Ne] at H
  simpa only [notMem_maximalIdeal] using H
