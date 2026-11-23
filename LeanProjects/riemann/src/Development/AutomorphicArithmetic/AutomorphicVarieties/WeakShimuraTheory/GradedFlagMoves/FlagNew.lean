import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lowMk {R : Type} [CommRing R] (x y z t : R) :
    IsLow (!![1, 0, 0, 0; -x, 1, 0, 0; -y, -t, 1, 0; -z, -(y + t * x), x, 1] : M4 R) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adj_apply, sgn, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four] <;> ring
  · intro i
    fin_cases i <;> simp
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢

private theorem adjMk {R : Type} [CommRing R] (x y z t : R) :
    adj (!![1, 0, 0, 0; -x, 1, 0, 0; -y, -t, 1, 0; -z, -(y + t * x), x, 1] : M4 R) =
      !![1, 0, 0, 0; x, 1, 0, 0; y + t * x, t, 1, 0; z, y, -x, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev] <;> ring

private theorem upOf {k : Type} [Field k] {ν : k} {w : M4 k} (h : IsGSp ν w) (h0 : w 0 0 ≠ 0)
    (h1 : w 1 0 = 0) (h2 : w 2 0 = 0) (h3 : w 3 0 = 0) (h4 : w 2 1 = 0) : IsUp w := by
  have e1 := congrFun (congrFun h 3) 1
  have e2 := congrFun (congrFun h 3) 2
  simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, h1, h2, h3] at e1 e2
  have h31 : w 3 1 = 0 := by
    rcases e1 with e1 | e1
    · exact absurd e1 h0
    · exact e1
  have h32 : w 3 2 = 0 := by
    rcases e2 with e2 | e2
    · exact absurd e2 h0
    · exact e2
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;> omega

private theorem core {k : Type} [Field k] {ν : k} {u : M4 k} (hu : IsGSp ν u) (h0 : u 0 0 ≠ 0) (h1 : u 1 1 ≠ 0)
    (h01 : u 0 1 = 0) : ∃ n' : M4 k, IsLow n' ∧ IsUp (adj n' * u) ∧ (u 2 1 = 0 → n' 2 1 = 0) := by
  obtain ⟨x, hx⟩ : ∃ x : k, x * u 0 0 + u 1 0 = 0 :=
    ⟨-u 1 0 / u 0 0, by field_simp; ring⟩
  obtain ⟨t, ht⟩ : ∃ t : k, t * u 1 1 + u 2 1 = 0 :=
    ⟨-u 2 1 / u 1 1, by field_simp; ring⟩
  obtain ⟨y, hy⟩ : ∃ y : k, (y + t * x) * u 0 0 + t * u 1 0 + u 2 0 = 0 :=
    ⟨-(t * u 1 0 + u 2 0) / u 0 0 - t * x, by field_simp; ring⟩
  obtain ⟨z, hz⟩ : ∃ z : k, z * u 0 0 + y * u 1 0 - x * u 2 0 + u 3 0 = 0 :=
    ⟨(x * u 2 0 - y * u 1 0 - u 3 0) / u 0 0, by field_simp; ring⟩
  have hl := lowMk x y z t
  refine ⟨_, hl, ?_, ?_⟩
  · have hinv : adj (!![1, 0, 0, 0; -x, 1, 0, 0; -y, -t, 1, 0; -z, -(y + t * x), x, 1] : M4 k) *
        !![1, 0, 0, 0; -x, 1, 0, 0; -y, -t, 1, 0; -z, -(y + t * x), x, 1] = 1 := by
      simpa [IsGSp] using hl.1
    have hinv' := mul_eq_one_comm.mp hinv
    have hG : IsGSp 1 (adj (!![1, 0, 0, 0; -x, 1, 0, 0; -y, -t, 1, 0; -z, -(y + t * x), x, 1] : M4 k)) := by
      unfold IsGSp
      rw [(grp k).2.1]
      simpa using hinv'
    have hP := (grp k).2.2.2.2.2.2.2.1 1 ν _ _ hG hu
    rw [one_mul] at hP
    rw [adjMk] at hP ⊢
    apply upOf hP
    · simpa [Matrix.mul_apply, Fin.sum_univ_four] using h0
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination hx
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination hy
    · simp [Matrix.mul_apply, Fin.sum_univ_four]
      linear_combination hz
    · simp [Matrix.mul_apply, Fin.sum_univ_four, h01]
      linear_combination ht
  · intro h21
    have : t = 0 := by
      rw [h21, add_zero] at ht
      rcases mul_eq_zero.mp ht with h | h
      · exact h
      · exact absurd h h1
    simp [this]

theorem UpperTheory.V.Ws.Rt.flagNew :
    ∀ (k : Type) [Field k] (ν : k) (X n : M4 k), ν ≠ 0 → IsGSp ν X → IsLow n → ((SuppM nP X ∧ SuppM qQ n) ∨ SuppM nM X) →
      ∃ n' : M4 k, IsLow n' ∧ IsUp (adj n' * X * n) ∧ (SuppM nP X ∧ SuppM qQ n → SuppM qQ n') := by
  intro k _ ν X n hν hX hn hS
  obtain ⟨hn1, hnd, hnu⟩ := hn
  have hu : IsGSp ν (X * n) := by
    have := (grp k).2.2.2.2.2.2.2.1 ν 1 X n hX hn1
    simpa using this
  have key : X 0 1 = 0 ∧ X 0 2 = 0 ∧ X 0 3 = 0 ∧ X 1 3 = 0 ∧ X 2 3 = 0 ∧
      X 1 2 * X 2 1 = 0 ∧ X 1 2 * n 2 1 = 0 := by
    rcases hS with ⟨hA, hB⟩ | hA
    · refine ⟨hA 0 1 (by decide) (by decide), hA 0 2 (by decide) (by decide),
        hA 0 3 (by decide) (by decide), hA 1 3 (by decide) (by decide),
        hA 2 3 (by decide) (by decide), ?_, ?_⟩
      · rw [hA 2 1 (by decide) (by decide), mul_zero]
      · rw [hB 2 1 (by decide) (by decide), mul_zero]
    · refine ⟨hA 0 1 (by decide) (by decide), hA 0 2 (by decide) (by decide),
        hA 0 3 (by decide) (by decide), hA 1 3 (by decide) (by decide),
        hA 2 3 (by decide) (by decide), ?_, ?_⟩
      · rw [hA 1 2 (by decide) (by decide), zero_mul]
      · rw [hA 1 2 (by decide) (by decide), zero_mul]
  obtain ⟨z01, z02, z03, z13, z23, c1, c2⟩ := key
  have n01 : n 0 1 = 0 := hnu 0 1 (by decide)
  have n11 : n 1 1 = 1 := hnd 1
  have n00 : n 0 0 = 1 := hnd 0
  have d0 := congrFun (congrFun hX 0) 0
  have d1 := congrFun (congrFun hX 1) 1
  simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn, Fin.rev, z01, z02, z03, z13, z23] at d0 d1
  have x00 : X 0 0 ≠ 0 := by
    intro h
    rw [h] at d0
    simp at d0
    exact hν d0.symm
  have x11 : X 1 1 ≠ 0 := by
    intro h
    apply hν
    rw [← d1, h]
    linear_combination -c1
  have h00 : (X * n) 0 0 ≠ 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_four, z01, z02, z03, n00] using x00
  have h11 : (X * n) 1 1 ≠ 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, z13, n01, n11]
    rw [c2, add_zero]
    exact x11
  have h01 : (X * n) 0 1 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, z01, z02, z03, n01]
  obtain ⟨n', hl, hup, h21⟩ := core hu h00 h11 h01
  refine ⟨n', hl, by rwa [← mul_assoc] at hup, ?_⟩
  rintro ⟨hA, hB⟩
  have e21 : (X * n) 2 1 = 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_four, z23, n01, n11, hA 2 1 (by decide) (by decide),
      hB 2 1 (by decide) (by decide)]
  have m21 := h21 e21
  intro i j hij hw
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | exact hl.2.2 _ _ (by decide)
    | exact m21
    | exact absurd (by decide) hw
