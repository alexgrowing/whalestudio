import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem unit_add_mem {R : Type} [CommRing R] [IsLocalRing R] {a b : R} (ha : IsUnit a)
    (hb : b ∈ maximalIdeal R) : IsUnit (a + b) := by
  by_contra h
  have h1 : a + b ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
  have h2 : a ∈ maximalIdeal R := by simpa using (maximalIdeal R).sub_mem h1 hb
  exact (IsLocalRing.mem_maximalIdeal _).mp h2 ha

private theorem two_kill {R : Type} [CommRing R] [IsLocalRing R] {p q r s a b : R} (hp : IsUnit p) (hs : IsUnit s)
    (hq : q ∈ maximalIdeal R) (e1 : p * a + q * b = 0) (e2 : r * a + s * b = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨s', hs'⟩ := hs.exists_right_inv
  have hb : b = -(s' * r) * a := by linear_combination s' * e2 - b * hs'
  have hm : q * s' * r ∈ maximalIdeal R :=
    (maximalIdeal R).mul_mem_right _ ((maximalIdeal R).mul_mem_right _ hq)
  have hu : IsUnit (p + -(q * s' * r)) := unit_add_mem hp ((maximalIdeal R).neg_mem hm)
  have ha : a = 0 := (hu.mul_right_eq_zero).mp (by linear_combination e1 - q * hb)
  refine ⟨ha, ?_⟩
  rw [hb, ha]
  ring

private theorem cols {R : Type} [CommRing R] [IsLocalRing R] (X u U : M4 R) (hb : IsBlock X) (hs : Sep X)
    (e : X * u = u * U) (hU : IsUp U) (hc : ∀ i, U i i - X i i ∈ maximalIdeal R) :
    ∃ y, u 0 1 = y * u 0 0 ∧ u 2 1 = y * u 2 0 := by
  have h01 : IsUnit (X 0 0 - X 1 1) := hs.unit 0 1 (by decide)
  have h21 : IsUnit (X 2 2 - X 1 1) := hs.unit 2 1 (by decide)
  have p0 : IsUnit (X 0 0 - U 1 1) := by
    have := unit_add_mem h01 (neg_mem (hc 1))
    convert this using 1; ring
  have p2 : IsUnit (X 2 2 - U 1 1) := by
    have := unit_add_mem h21 (neg_mem (hc 1))
    convert this using 1; ring
  have pU : IsUnit (U 0 0 - U 1 1) := by
    have := unit_add_mem p0 (hc 0)
    convert this using 1; ring
  obtain ⟨w, hw⟩ := pU.exists_left_inv
  have z01 := hb 0 1 (by decide)
  have z03 := hb 0 3 (by decide)
  have z21 := hb 2 1 (by decide)
  have z23 := hb 2 3 (by decide)
  have y10 := hU 1 0 (by decide)
  have y20 := hU 2 0 (by decide)
  have y30 := hU 3 0 (by decide)
  have y21 := hU 2 1 (by decide)
  have y31 := hU 3 1 (by decide)
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e20 := congrFun (congrFun e 2) 0
  have e21 := congrFun (congrFun e 2) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_four, z01, z03, z21, z23, y10, y20, y30, y21, y31, zero_mul, mul_zero,
    add_zero] at e00 e01 e20 e21
  have := two_kill (a := u 0 1 - U 0 1 * w * u 0 0) (b := u 2 1 - U 0 1 * w * u 2 0) (r := X 2 0) p0 p2
    (hs.off 0 2 (by decide))
    (by linear_combination e01 - U 0 1 * w * e00 - U 0 1 * u 0 0 * hw)
    (by linear_combination e21 - U 0 1 * w * e20 - U 0 1 * u 2 0 * hw)
  exact ⟨U 0 1 * w, sub_eq_zero.mp this.1, sub_eq_zero.mp this.2⟩

private theorem entries_one_three_zero_eq_zero_of_intertwine_up {R : Type} [CommRing R] [IsLocalRing R] (X u U : M4 R) (hb : IsBlock X)
    (hs : Sep X) (e : X * u = u * U) (hU : IsUp U) (hc : ∀ i, U i i - X i i ∈ maximalIdeal R) :
    u 1 0 = 0 ∧ u 3 0 = 0 := by
  have X10 : X 1 0 = 0 := hb 1 0 (by simp [lamW])
  have coord_mul_inv_coord_eq_one : X 1 2 = 0 := hb 1 2 (by simp [lamW])
  have X30 : X 3 0 = 0 := hb 3 0 (by simp [lamW])
  have X32 : X 3 2 = 0 := hb 3 2 (by simp [lamW])
  have U10 : U 1 0 = 0 := hU 1 0 (by decide)
  have U20 : U 2 0 = 0 := hU 2 0 (by decide)
  have U30 : U 3 0 = 0 := hU 3 0 (by decide)
  have r10 := congrFun (congrFun e 1) 0
  have r30 := congrFun (congrFun e 3) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_four, X10, coord_mul_inv_coord_eq_one, X30, X32, U10, U20, U30,
    zero_mul, mul_zero, add_zero, zero_add] at r10 r30
  have hc0 := hc 0
  have hp : IsUnit (X 1 1 - U 0 0) := by
    have e' : X 1 1 - U 0 0 = (X 1 1 - X 0 0) + -(U 0 0 - X 0 0) := by ring
    rw [e']
    exact unit_add_mem (hs.unit 1 0 (by simp [lamW])) ((maximalIdeal R).neg_mem hc0)
  have hs' : IsUnit (X 3 3 - U 0 0) := by
    have e' : X 3 3 - U 0 0 = (X 3 3 - X 0 0) + -(U 0 0 - X 0 0) := by ring
    rw [e']
    exact unit_add_mem (hs.unit 3 0 (by simp [lamW])) ((maximalIdeal R).neg_mem hc0)
  have hq : X 1 3 ∈ maximalIdeal R := hs.off 1 3 (by decide)
  exact two_kill (r := X 3 1) (a := u 1 0) (b := u 3 0) hp hs' hq
    (by linear_combination r10) (by linear_combination r30)

theorem UpperTheory.V.Ws.Bl.flagVec :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (X u : M4 R), IsBlock X → Sep X → IsGSp 1 u → IsUp (adj u * X * u) → (∀ i, (adj u * X * u) i i - X i i ∈ maximalIdeal R) → uPlus u ≠ ⊥ := by
  intro R _ _ X u hb hs hg hup hc
  have hinv : adj u * u = 1 := by simpa [IsGSp] using hg
  have e : X * u = u * (adj u * X * u) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_eq_one_comm.mp hinv, Matrix.one_mul]
  obtain ⟨y, hy1, hy2⟩ := cols X u _ hb hs e hup hc
  obtain ⟨h10, h30⟩ := entries_one_three_zero_eq_zero_of_intertwine_up X u _ hb hs e hup hc
  have I10 := congrFun (congrFun hinv 1) 0
  have I11 := congrFun (congrFun hinv 1) 1
  have I00 := congrFun (congrFun hinv 0) 0
  have I31 := congrFun (congrFun hinv 3) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, adj_apply, sgn, Fin.rev] at I10 I11 I00 I31
  have iso : u 0 0 * u 3 1 = u 2 0 * u 1 1 := by
    linear_combination I31 - u 2 1 * h10 + u 0 1 * h30
  obtain ⟨w, hw⟩ : ∃ w : Fin 4 → R, w = ![0, u 1 1, 0, u 3 1] := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin 4 → R, φ = ![u 2 0, 0, -u 0 0, 0] := ⟨_, rfl⟩
  obtain ⟨Y, hYd⟩ : ∃ Y : M4 R, Y = Matrix.vecMulVec w φ := ⟨_, rfl⟩
  have hYm : Y ∈ uM R := by
    show Y ∈ hAB R ⊓ sp4 R
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · show ∀ i j, ¬ lamW i < lamW j → Y i j = 0
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [lamW, Matrix.vecMulVec_apply]
    · show adj Y = -Y
      ext i j
      fin_cases i <;> fin_cases j <;>
        (try simp [hYd, hw, hφ, adj_apply, sgn, Fin.rev, Matrix.vecMulVec_apply]) <;>
        first
          | linear_combination iso
          | linear_combination (-1 : R) * iso
  have hv : w = Matrix.mulVec u ![-y, 1, 0, 0] := by
    funext i
    fin_cases i <;> simp [hw, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
      first
        | linear_combination (-1 : R) * hy1
        | linear_combination y * h10
        | linear_combination (-1 : R) * hy2
        | linear_combination y * h30
        | linear_combination hy1
        | linear_combination hy2
        | linear_combination (-y) * h10
        | linear_combination (-y) * h30
  have hA : Matrix.mulVec (adj u) w = ![-y, 1, 0, 0] := by
    rw [hv, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hB0 : Matrix.vecMul φ u 0 = 0 := by
    simp [hφ, Matrix.vecMul, dotProduct, Fin.sum_univ_four] <;> ring
  have hB1 : Matrix.vecMul φ u 1 = 0 := by
    simp [hφ, Matrix.vecMul, dotProduct, Fin.sum_univ_four] <;>
      linear_combination u 2 0 * hy1 - u 0 0 * hy2
  have hN : adj u * Y * u = Matrix.vecMulVec ![-y, 1, 0, 0] (Matrix.vecMul φ u) := by
    rw [hYd, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hA]
  have hsup : IsSUp (adj u * Y * u) := by
    intro i j hji
    rw [hN, Matrix.vecMulVec_apply]
    fin_cases i <;> fin_cases j <;>
      first
        | (simp [hB0, hB1]; done)
        | (exfalso; simp at hji; done)
        | (exfalso; revert hji; decide)
  rw [Submodule.ne_bot_iff]
  refine ⟨⟨Y, hYm⟩, ?_, ?_⟩
  · exact hsup
  · intro hY0
    have hY : Y = 0 := congrArg Subtype.val hY0
    have f1 : u 1 1 * u 2 0 = 0 := by
      have h := congrFun (congrFun hY 1) 0
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have f2 : u 1 1 * u 0 0 = 0 := by
      have h := congrFun (congrFun hY 1) 2
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero, -neg_eq_zero, -mul_neg] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have f3 : u 3 1 * u 2 0 = 0 := by
      have h := congrFun (congrFun hY 3) 0
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have f4 : u 3 1 * u 0 0 = 0 := by
      have h := congrFun (congrFun hY 3) 2
      simp [hYd, hw, hφ, Matrix.vecMulVec_apply, -mul_eq_zero, -neg_eq_zero, -mul_neg] at h
      first | linear_combination h | linear_combination (-1 : R) * h
    have J : u 2 2 * u 1 1 - u 0 2 * u 3 1 = 1 := by
      linear_combination I11 - u 3 2 * hy1 + u 1 2 * hy2 - y * I10 + y * u 2 2 * h10 -
        y * u 0 2 * h30
    have z00 : u 0 0 = 0 := by linear_combination (-u 0 0) * J + u 2 2 * f2 - u 0 2 * f4
    have z20 : u 2 0 = 0 := by linear_combination (-u 2 0) * J + u 2 2 * f1 - u 0 2 * f3
    have h1 : (1 : R) = 0 := by
      linear_combination (-1 : R) * I00 + u 3 3 * z00 + u 2 3 * h10 - u 1 3 * z20 - u 0 3 * h30
    exact one_ne_zero h1
