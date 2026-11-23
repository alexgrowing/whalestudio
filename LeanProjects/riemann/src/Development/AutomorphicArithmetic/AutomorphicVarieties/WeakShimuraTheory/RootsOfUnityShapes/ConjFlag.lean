import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem up_mul {R : Type} [CommRing R] {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) : IsUp (X * Y) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k < i
  · rw [hX i k hk, zero_mul]
  · rw [hY k j (lt_of_lt_of_le h (not_lt.1 hk)), mul_zero]

private theorem up_mul_diag {R : Type} [CommRing R] {X Y : M4 R} (hX : IsUp X) (hY : IsUp Y) (i : Fin 4) :
    (X * Y : M4 R) i i = X i i * Y i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hX i k h, zero_mul]
  · rw [hY k i h, mul_zero]

private theorem up_adj {R : Type} [CommRing R] {X : M4 R} (hX : IsUp X) : IsUp (adj X) := by
  intro i j h
  rw [adj_apply, hX _ _ (Fin.rev_lt_rev.2 h), smul_zero]

private theorem gsp_mul_adj {R : Type} [CommRing R] {ν μ : R} {P : M4 R} (hμ : μ * ν = 1) (h : IsGSp ν P) :
    P * adj P = ν • (1 : M4 R) := by
  have h' : adj P * P = ν • (1 : M4 R) := h
  have h1 : (μ • adj P) * P = 1 := by
    rw [Matrix.smul_mul, h', smul_smul, hμ, one_smul]
  have h2 : P * (μ • adj P) = 1 := mul_eq_one_comm.mp h1
  calc P * adj P = (ν * μ) • (P * adj P) := by rw [mul_comm, hμ, one_smul]
    _ = ν • (P * (μ • adj P)) := by rw [Matrix.mul_smul, smul_smul]
    _ = ν • (1 : M4 R) := by rw [h2]

theorem UpperTheory.V.Ws.Rq.conjFlag :
    ∀ (R : Type) [CommRing R] (ν : R) (X Y Z n₀ n : M4 R), IsUnit ν → IsGSp ν X → IsLow n₀ → IsLow n → IsUp (adj n * X * n₀) →
      Z * X = X * Y → IsUp (adj n₀ * Y * n₀) → IsUp (adj n * Z * n) ∧ ∀ i, (adj n * Z * n) i i = (adj n₀ * Y * n₀) i i := by
  intro R _ ν X Y Z n₀ n hν hX hn₀ hn hU hZ hV
  obtain ⟨hadj, hadj2, -, -, -, -, -, -, -⟩ := grp R
  obtain ⟨u, rfl⟩ := hν
  have hμ : ((u⁻¹ : Rˣ) : R) * u = 1 := u.inv_mul
  have hn1 : n * adj n = 1 := by
    have := gsp_mul_adj (μ := (1 : R)) (one_mul 1) hn.1
    rwa [one_smul] at this
  have hn01 : n₀ * adj n₀ = 1 := by
    have := gsp_mul_adj (μ := (1 : R)) (one_mul 1) hn₀.1
    rwa [one_smul] at this
  have hn0 : adj n₀ * n₀ = 1 := by
    have h : adj n₀ * n₀ = (1 : R) • (1 : M4 R) := hn₀.1
    rwa [one_smul] at h
  have hXg : adj X * X = (u : R) • (1 : M4 R) := hX
  have hn1' : ∀ W : M4 R, n * (adj n * W) = W := by
    intro W; rw [← Matrix.mul_assoc, hn1, Matrix.one_mul]
  have hn01' : ∀ W : M4 R, n₀ * (adj n₀ * W) = W := by
    intro W; rw [← Matrix.mul_assoc, hn01, Matrix.one_mul]
  obtain ⟨U, hUdef⟩ : ∃ U, U = adj n * X * n₀ := ⟨_, rfl⟩
  rw [← hUdef] at hU
  have hUg : adj U * U = (u : R) • (1 : M4 R) := by
    rw [hUdef, hadj, hadj, hadj2]
    simp only [Matrix.mul_assoc, hn1']
    rw [← Matrix.mul_assoc (adj X) X, hXg, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, hn0]
  have hUa : U * adj U = (u : R) • (1 : M4 R) := gsp_mul_adj hμ hUg
  have hWU : adj n * Z * n * U = U * (adj n₀ * Y * n₀) := by
    rw [hUdef]
    simp only [Matrix.mul_assoc, hn1', hn01']
    rw [← Matrix.mul_assoc Z X, hZ]
    simp only [Matrix.mul_assoc]
  have hνW : (u : R) • (adj n * Z * n) = U * (adj n₀ * Y * n₀) * adj U := by
    rw [← hWU, Matrix.mul_assoc _ U, hUa, Matrix.mul_smul, Matrix.mul_one]
  have hup : IsUp (U * (adj n₀ * Y * n₀) * adj U) := up_mul (up_mul hU hV) (up_adj hU)
  have hWup : IsUp (adj n * Z * n) := by
    intro i j hij
    have h1 := congrFun (congrFun hνW i) j
    rw [Matrix.smul_apply, smul_eq_mul, hup i j hij] at h1
    exact (Units.mul_right_eq_zero u).mp h1
  refine ⟨hWup, fun i => ?_⟩
  have h1 := congrFun (congrFun hνW i) i
  rw [Matrix.smul_apply, smul_eq_mul, up_mul_diag (up_mul hU hV) (up_adj hU), up_mul_diag hU hV] at h1
  have h2 := congrFun (congrFun hUg i) i
  rw [up_mul_diag (up_adj hU) hU, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h2
  apply u.isUnit.mul_left_cancel
  rw [h1, ← h2]
  ring
