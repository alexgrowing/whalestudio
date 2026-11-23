import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CornerUnits
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusCornerOrderSkips

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem cor_mul {K : Type} [CommRing K] (A B : Matrix (Fin 3) (Fin 3) K) (h0 : A 0 1 = 0) (h2 : A 2 1 = 0) :
    (A * B).submatrix cor cor = A.submatrix cor cor * B.submatrix cor cor := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [cor, h0, h2]

private theorem mid_mul' {K : Type} [CommRing K] (A B : Matrix (Fin 3) (Fin 3) K) (h0 : B 0 1 = 0) (h2 : B 2 1 = 0) :
    (A * B) 1 1 = A 1 1 * B 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_three, h0, h2]

private theorem cor_one' {K : Type} [CommRing K] :
    (1 : Matrix (Fin 3) (Fin 3) K).submatrix cor cor = 1 :=
  Matrix.submatrix_one _ (by decide)

private theorem cor_sub {K : Type} [CommRing K] (A : Matrix (Fin 3) (Fin 3) K) (t : K) :
    (A - t • (1 : Matrix (Fin 3) (Fin 3) K)).submatrix cor cor = A.submatrix cor cor - t • 1 := by
  simp [Matrix.submatrix_sub, Matrix.submatrix_smul, cor_one']

private theorem cor_J {K : Type} [CommRing K] (A : Matrix (Fin 3) (Fin 3) K) :
    (Jmat K 3 * Aᵀ * Jmat K 3).submatrix cor cor = Jmat K 2 * (A.submatrix cor cor)ᵀ * Jmat K 2 := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [Jmat, cor, Fin.rev]

private theorem ordProd_three {H K : Type} [CommRing K] (r : H → Matrix (Fin 3) (Fin 3) K) (ψ : Fin 3 → H → K)
    (x y z : H) : ordProd r ψ ![x, y, z] =
      (r x - ψ 0 x • 1) * (r y - ψ 1 y • 1) * (r z - ψ 2 z • 1) := by
  simp [ordProd, List.ofFn_succ, mul_assoc]

private theorem ordProd_two {H K : Type} [CommRing K] (r : H → Matrix (Fin 2) (Fin 2) K) (ψ : Fin 2 → H → K)
    (g : Fin 2 → H) : ordProd r ψ g = (r (g 0) - ψ 0 (g 0) • 1) * (r (g 1) - ψ 1 (g 1) • 1) := by
  simp [ordProd, List.ofFn_succ]

theorem UpperTheory.V.Fr.exists_frobenius_corner :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {K : Type} [CommRing K] (ρ : NRep F 3 K), (∀ g i j, Odd (w 3 i - w 3 j) → ρ.r g i j = 0) → CornerUnits ρ → ∃ σ : NRep F 2 K, IsCorner ρ σ := by
  intro l _ k _ F K _ ρ hodd hU
  have hc : ∀ g (i : Fin 3), i ≠ 1 → ρ.r g i 1 = 0 := by
    intro g i hi
    apply hodd
    fin_cases i <;> simp_all [w, Int.odd_iff]
  have hcs : ∀ g (t : K) (i : Fin 3), i ≠ 1 → (ρ.r g - t • 1) i 1 = 0 := by
    intro g t i hi
    rw [Matrix.sub_apply, Matrix.smul_apply, hc g i hi, Matrix.one_apply_ne hi, smul_zero, sub_zero]
  have hinj : Function.Injective cor := by decide
  let s : F.G0 →* Matrix (Fin 2) (Fin 2) K :=
    { toFun := fun g => (ρ.r g).submatrix cor cor
      map_one' := by simp only [map_one, cor_one']
      map_mul' := fun a b => by
        simp only [map_mul]
        exact cor_mul _ _ (hc a 0 (by decide)) (hc a 2 (by decide)) }
  refine ⟨⟨s, fun v i => ρ.ψ v (cor i), ?_, ?_, ?_⟩, ?_⟩
  · intro g
    show (ρ.r (F.star g)).submatrix cor cor = Jmat K 2 * ((ρ.r g).submatrix cor cor)ᵀ * Jmat K 2
    rw [ρ.pol, cor_J]
  · intro i j hij
    have hd := ρ.diag (cor i) (cor j) (hinj.ne hij)
    rw [Matrix.sub_apply] at hd ⊢
    exact hd
  · intro v g
    obtain ⟨g₁, -, -, u1⟩ := hU v
    have key := frobenius_corner_order_skips (s.comp (F.loc0 v)) (fun x => (ρ.ψ v 0 x : K)) ((Units.coeHom K).comp (ρ.ψ v 2)) g₁ (ρ.ψ v 1 g₁ : K) ?det ?three (g 0) (g 1)
    · rw [ordProd_two]
      exact key
    · show IsUnit ((ρ.r (F.loc0 v g₁)).submatrix cor cor - (ρ.ψ v 1 g₁ : K) • 1).det
      rw [← cor_sub, Matrix.det_fin_two]
      simpa [cor, Matrix.one_apply] using u1
    · intro x y
      show ((ρ.r (F.loc0 v x)).submatrix cor cor - (ρ.ψ v 0 x : K) • 1) * ((ρ.r (F.loc0 v g₁)).submatrix cor cor - (ρ.ψ v 1 g₁ : K) • 1) * ((ρ.r (F.loc0 v y)).submatrix cor cor - (ρ.ψ v 2 y : K) • 1) = 0
      have h3 := ρ.ord v ![x, g₁, y]
      rw [ordProd_three] at h3
      beta_reduce at h3
      rw [← cor_sub, ← cor_sub, ← cor_sub, mul_assoc, ← cor_mul _ _ (hcs _ _ 0 (by decide)) (hcs _ _ 2 (by decide)), ← cor_mul _ _ (hcs _ _ 0 (by decide)) (hcs _ _ 2 (by decide)), ← mul_assoc, h3, Matrix.submatrix_zero]
      rfl
  · refine ⟨hodd, fun g i j => rfl, fun v i g => rfl, fun v g => ?_⟩
    obtain ⟨g₁, u0, u2, -⟩ := hU v
    have h3 := ρ.ord v ![g₁, g, g₁]
    rw [ordProd_three] at h3
    beta_reduce at h3
    have h11 := congrFun (congrFun h3 1) 1
    rw [mid_mul' _ _ (hcs _ _ 0 (by decide)) (hcs _ _ 2 (by decide)), mid_mul' _ _ (hcs _ _ 0 (by decide)) (hcs _ _ 2 (by decide))] at h11
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.zero_apply] at h11
    rw [u2.mul_left_eq_zero, u0.mul_right_eq_zero, sub_eq_zero] at h11
    exact h11
