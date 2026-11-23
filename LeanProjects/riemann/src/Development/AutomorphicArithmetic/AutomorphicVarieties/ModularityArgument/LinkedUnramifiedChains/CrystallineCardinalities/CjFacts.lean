import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.OkFin

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J.ConjugationUpperEntries

section Abs

variable {C : Type} [CommRing C]

private theorem up_entries {T : Matrix (Fin 3) (Fin 3) C} (h : UpT T) : T 1 0 = 0 ∧ T 2 0 = 0 ∧ T 2 1 = 0 :=
  ⟨h 1 0 (by decide), h 2 0 (by decide), h 2 1 (by decide)⟩

private theorem up_of {T : Matrix (Fin 3) (Fin 3) C} (h1 : T 1 0 = 0) (h2 : T 2 0 = 0) (h3 : T 2 1 = 0) : UpT T := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact h1 | exact h2 | exact h3 | exact absurd hij (by decide)

private theorem inv_entries {T B : Matrix (Fin 3) (Fin 3) C} (hT : UpT T) (hB : UpT B) (h : T * B = 1) :
    T 0 0 * B 0 0 = 1 ∧ T 1 1 * B 1 1 = 1 ∧ T 2 2 * B 2 2 = 1 ∧ T 0 0 * B 0 1 + T 0 1 * B 1 1 = 0 ∧
      T 1 1 * B 1 2 + T 1 2 * B 2 2 = 0 := by
  obtain ⟨a1, a2, a3⟩ := up_entries hT
  obtain ⟨b1, b2, b3⟩ := up_entries hB
  have e : ∀ i j, (T * B) i j = (1 : Matrix (Fin 3) (Fin 3) C) i j := fun i j => by rw [h]
  have e00 := e 0 0
  have e11 := e 1 1
  have e22 := e 2 2
  have e01 := e 0 1
  have e12 := e 1 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, a1, a2, a3, b1, b2, b3,
    mul_zero, zero_mul, add_zero, zero_add] at e00 e11 e22 e01 e12
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa using e00
  · simpa using e11
  · simpa using e22
  · simpa using e01
  · simpa using e12

private theorem conj_apply (T X B : Matrix (Fin 3) (Fin 3) C) (i j : Fin 3) :
    (T * X * B) i j = (T i 0 * X 0 0 + T i 1 * X 1 0 + T i 2 * X 2 0) * B 0 j +
      (T i 0 * X 0 1 + T i 1 * X 1 1 + T i 2 * X 2 1) * B 1 j +
      (T i 0 * X 0 2 + T i 1 * X 1 2 + T i 2 * X 2 2) * B 2 j := by
  simp only [Matrix.mul_apply, Fin.sum_univ_three]

private theorem conj_facts {T B X : Matrix (Fin 3) (Fin 3) C} (hT : UpT T) (hB : UpT B) (h : T * B = 1) (hX : UpT X) :
    UpT (T * X * B) ∧ (∀ i, (T * X * B) i i = X i i) ∧ ∀ i : Fin 2, (T * X * B) i.castSucc i.succ =
      T i.castSucc i.castSucc * B i.succ i.succ * X i.castSucc i.succ -
        T i.castSucc i.succ * B i.succ i.succ * (X i.castSucc i.castSucc - X i.succ i.succ) := by
  obtain ⟨a1, a2, a3⟩ := up_entries hT
  obtain ⟨b1, b2, b3⟩ := up_entries hB
  obtain ⟨x1, x2, x3⟩ := up_entries hX
  obtain ⟨i00, i11, i22, i01, i12⟩ := inv_entries hT hB h
  have d0 : (T * X * B) 0 0 = X 0 0 := by
    rw [conj_apply]
    simp only [a1, a2, a3, b1, b2, b3, x1, x2, x3, mul_zero, zero_mul, add_zero, zero_add]
    linear_combination X 0 0 * i00
  have d1 : (T * X * B) 1 1 = X 1 1 := by
    rw [conj_apply]
    simp only [a1, a2, a3, b1, b2, b3, x1, x2, x3, mul_zero, zero_mul, add_zero, zero_add]
    linear_combination X 1 1 * i11
  have d2 : (T * X * B) 2 2 = X 2 2 := by
    rw [conj_apply]
    simp only [a1, a2, a3, b1, b2, b3, x1, x2, x3, mul_zero, zero_mul, add_zero, zero_add]
    linear_combination X 2 2 * i22
  have s0 : (T * X * B) 0 1 = T 0 0 * B 1 1 * X 0 1 - T 0 1 * B 1 1 * (X 0 0 - X 1 1) := by
    rw [conj_apply]
    simp only [a1, a2, a3, b1, b2, b3, x1, x2, x3, mul_zero, zero_mul, add_zero, zero_add]
    linear_combination X 0 0 * i01
  have s1 : (T * X * B) 1 2 = T 1 1 * B 2 2 * X 1 2 - T 1 2 * B 2 2 * (X 1 1 - X 2 2) := by
    rw [conj_apply]
    simp only [a1, a2, a3, b1, b2, b3, x1, x2, x3, mul_zero, zero_mul, add_zero, zero_add]
    linear_combination X 1 1 * i12
  refine ⟨up_of ?_ ?_ ?_, ?_, ?_⟩
  · rw [conj_apply]
    simp only [a1, a2, a3, b1, b2, b3, x1, x2, x3, mul_zero, zero_mul, add_zero, zero_add]
  · rw [conj_apply]
    simp only [a1, a2, a3, b1, b2, b3, x1, x2, x3, mul_zero, zero_mul, add_zero, zero_add]
  · rw [conj_apply]
    simp only [a1, a2, a3, b1, b2, b3, x1, x2, x3, mul_zero, zero_mul, add_zero, zero_add]
  · intro i
    fin_cases i
    exacts [d0, d1, d2]
  · intro i
    fin_cases i
    exacts [s0, s1]

private theorem conj_single {T B : Matrix (Fin 3) (Fin 3) C} (hT : UpT T) (hB : UpT B) (x : C) :
    T * Matrix.single 0 2 x * B = Matrix.single 0 2 (T 0 0 * B 2 2 * x) := by
  obtain ⟨a1, a2, a3⟩ := up_entries hT
  obtain ⟨b1, b2, b3⟩ := up_entries hB
  ext i j
  rw [conj_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply, a1, a2, a3, b1, b2, b3] <;> ring

private theorem up_of_conj {T B Y : Matrix (Fin 3) (Fin 3) C} (hT : UpT T) (hBT : B * T = 1)
    (hY : UpT (T * Y * B - Y)) (u0 : IsUnit (T 2 2 - T 0 0)) (u1 : IsUnit (T 1 1 - T 0 0))
    (u2 : IsUnit (T 2 2 - T 1 1)) : UpT Y := by
  obtain ⟨a1, a2, a3⟩ := up_entries hT
  have hBT' := hBT
  generalize hZ : T * Y * B - Y = Z at hY
  obtain ⟨z1, z2, z3⟩ := up_entries hY
  have key : T * Y - Y * T = Z * T := by
    rw [← hZ, Matrix.sub_mul, Matrix.mul_assoc (T * Y), hBT', Matrix.mul_one]
  have e20 := congrFun (congrFun key 2) 0
  have e10 := congrFun (congrFun key 1) 0
  have e21 := congrFun (congrFun key 2) 1
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three, a1, a2, a3, z1, z2, z3,
    mul_zero, zero_mul, add_zero, zero_add] at e20 e10 e21
  have y20 : Y 2 0 = 0 := by
    have : (T 2 2 - T 0 0) * Y 2 0 = 0 := by linear_combination e20
    exact u0.mul_right_eq_zero.mp this
  have y10 : Y 1 0 = 0 := by
    have : (T 1 1 - T 0 0) * Y 1 0 = 0 := by linear_combination e10 - T 1 2 * y20
    exact u1.mul_right_eq_zero.mp this
  have y21 : Y 2 1 = 0 := by
    have : (T 2 2 - T 1 1) * Y 2 1 = 0 := by linear_combination e21 + T 0 1 * y20
    exact u2.mul_right_eq_zero.mp this
  exact up_of y10 y20 y21

variable {O : Type} [CommRing O]

private theorem map_pair (φ : O →+* C) {A B : Matrix (Fin 3) (Fin 3) O} (h : A * B = 1) :
    A.map φ * B.map φ = 1 := by
  rw [← Matrix.map_mul, h]
  simp

private theorem up_map (φ : O →+* C) {A : Matrix (Fin 3) (Fin 3) O} (h : UpT A) : UpT (A.map φ) :=
  fun i j hij => by rw [Matrix.map_apply, h i j hij, map_zero]

private theorem smul_q (I : Ideal O) (a : O) (x : O ⧸ I) : a • x = Ideal.Quotient.mk I a * x := by
  rw [Algebra.smul_def]; rfl

end Abs

end UpperTheory.V.Z.J.ConjugationUpperEntries

open UpperTheory.V.Z.J.ConjugationUpperEntries in
theorem UpperTheory.V.Z.J.cjFacts :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (D : Type) [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [CompactSpace D] (t : D →* GL (Fin 3) O) (k : ℕ), (l : O) ≠ 0 → TriRep t → (∃ ρ : Representation ℤ D (Matrix (Fin 3) (Fin 3) (Ok l O k)), (∀ s X, ρ s X = cj k t s X) ∧ IsOpen (ρ.ker : Set D)) ∧ (∀ s, UpT (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) ∧ ∀ i, (t s : Matrix (Fin 3) (Fin 3) O) i i * ((t s)⁻¹ : GL (Fin 3) O) i i = 1) ∧ (∀ s (X : Matrix (Fin 3) (Fin 3) (Ok l O k)), UpT X → UpT (cj k t s X) ∧ (∀ i, cj k t s X i i = X i i) ∧ ∀ i : Fin 2, cj k t s X i.castSucc i.succ = ((t s : Matrix (Fin 3) (Fin 3) O) i.castSucc i.castSucc * ((t s)⁻¹ : GL (Fin 3) O) i.succ i.succ) • X i.castSucc i.succ - ((t s : Matrix (Fin 3) (Fin 3) O) i.castSucc i.succ * ((t s)⁻¹ : GL (Fin 3) O) i.succ i.succ) • (X i.castSucc i.castSucc - X i.succ i.succ)) ∧ (∀ s (x : Ok l O k), cj k t s (Matrix.single 0 2 x) = Matrix.single 0 2 (((t s : Matrix (Fin 3) (Fin 3) O) 0 0 * ((t s)⁻¹ : GL (Fin 3) O) 2 2) • x)) ∧ ∀ Y : Matrix (Fin 3) (Fin 3) (Ok l O k), (∀ s, UpT (cj k t s Y - Y)) → UpT Y := by
  intro l _ O _ _ _ _ _ D _ _ _ _ t k hl ht
  let mk := Ideal.Quotient.mk (Ideal.span {(l : O) ^ k})
  have hT : ∀ s, UpT (t s : Matrix (Fin 3) (Fin 3) O) := ht.tri
  have hTB : ∀ s, (t s : Matrix (Fin 3) (Fin 3) O) * ((t s)⁻¹ : GL (Fin 3) O) = 1 :=
    fun s => (t s).mul_inv
  have hBT : ∀ s, (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) * (t s : Matrix (Fin 3) (Fin 3) O) = 1 :=
    fun s => (t s).inv_mul
  have hB : ∀ s, UpT (((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) := by
    intro s
    letI := (t s).invertible
    have h1 : Matrix.BlockTriangular (t s : Matrix (Fin 3) (Fin 3) O) id :=
      fun i j hij => hT s i j hij
    have h2 := Matrix.blockTriangular_inv_of_blockTriangular h1
    intro i j hij
    rw [Matrix.coe_units_inv]
    exact h2 hij
  have hdiag : ∀ s i, (t s : Matrix (Fin 3) (Fin 3) O) i i * ((t s)⁻¹ : GL (Fin 3) O) i i = 1 := by
    intro s
    obtain ⟨i0, i1, i2, -, -⟩ := inv_entries (hT s) (hB s) (hTB s)
    intro i
    fin_cases i
    exacts [i0, i1, i2]
  refine ⟨?_, fun s => ⟨hB s, hdiag s⟩, ?_, ?_, ?_⟩
  · let F : D → (Matrix (Fin 3) (Fin 3) (Ok l O k) →ₗ[ℤ] Matrix (Fin 3) (Fin 3) (Ok l O k)) := fun s =>
      LinearMap.mulRight ℤ ((((t s)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O).map mk) ∘ₗ
        LinearMap.mulLeft ℤ ((t s : Matrix (Fin 3) (Fin 3) O).map mk)
    let ρ : Representation ℤ D (Matrix (Fin 3) (Fin 3) (Ok l O k)) :=
      { toFun := F
        map_one' := by
          refine LinearMap.ext fun X => ?_
          simp [F]
        map_mul' := by
          intro a b
          refine LinearMap.ext fun X => ?_
          simp [F, Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_inv_rev] }
    refine ⟨ρ, fun s X => rfl, ?_⟩
    obtain ⟨N, hN⟩ := (okFin l O hl).2.2.2.2.1 k
    let U : Set D := ⋂ i, ⋂ j, {g | Ideal.Quotient.mk (maximalIdeal O ^ N) ((t g : Matrix (Fin 3) (Fin 3) O) i j) =
      Ideal.Quotient.mk (maximalIdeal O ^ N) ((t 1 : Matrix (Fin 3) (Fin 3) O) i j)}
    have hU : IsOpen U :=
      isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (ht.cont i j N).isOpen_fiber _
    have h1U : (1 : D) ∈ U := by simp [U]
    have hUK : U ⊆ (ρ.ker : Set D) := by
      intro g hg
      simp only [U, Set.mem_iInter, Set.mem_setOf_eq] at hg
      have hT1 : (t g : Matrix (Fin 3) (Fin 3) O).map mk = (t 1 : Matrix (Fin 3) (Fin 3) O).map mk := by
        ext i j
        exact Ideal.Quotient.eq.mpr (hN (Ideal.Quotient.eq.mp (hg i j)))
      have hone : (t 1 : Matrix (Fin 3) (Fin 3) O).map mk = 1 := by simp
      have hB1 : (((t g)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O).map mk = 1 := by
        have h := map_pair mk (hTB g)
        rw [hT1, hone, Matrix.one_mul] at h
        exact h
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      refine LinearMap.ext fun X => ?_
      change (t g : Matrix (Fin 3) (Fin 3) O).map mk * X * (((t g)⁻¹ : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O).map mk = X
      rw [hT1, hone, hB1, Matrix.one_mul, Matrix.mul_one]
    exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hU.mem_nhds h1U) hUK)
  · intro s X hX
    obtain ⟨u, d, sd⟩ := conj_facts (up_map mk (hT s)) (up_map mk (hB s)) (map_pair mk (hTB s)) hX
    refine ⟨u, d, fun i => ?_⟩
    rw [smul_q, smul_q, map_mul, map_mul]
    exact sd i
  · intro s x
    rw [smul_q, map_mul]
    exact conj_single (up_map mk (hT s)) (up_map mk (hB s)) x
  · intro Y hY
    obtain ⟨s, hd⟩ := ht.dist
    refine up_of_conj (up_map mk (hT s)) (map_pair mk (hBT s)) (hY s) ?_ ?_ ?_
    · rw [Matrix.map_apply, Matrix.map_apply, ← map_sub]
      exact (hd 2 0 (by decide)).map _
    · rw [Matrix.map_apply, Matrix.map_apply, ← map_sub]
      exact (hd 1 0 (by decide)).map _
    · rw [Matrix.map_apply, Matrix.map_apply, ← map_sub]
      exact (hd 2 1 (by decide)).map _
