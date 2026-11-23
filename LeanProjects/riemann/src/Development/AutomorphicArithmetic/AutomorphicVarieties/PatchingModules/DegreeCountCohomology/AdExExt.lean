import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem conj_eq_transpose_conj_of_transpose_mul_eq_smul_one {n : ℕ} {R : Type} [CommRing R] (P Q P' Q' X : Matrix (Fin n) (Fin n) R) (a b : R)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (hPQ' : P' * Q' = 1) (ha : Pᵀ * P' = a • 1) (hb : Qᵀ * Q' = b • 1) :
    P' * (X * Q') = Qᵀ * (X * Pᵀ) := by
  have h1 : P' = a • Qᵀ := by
    calc P' = (Qᵀ * Pᵀ) * P' := by rw [← Matrix.transpose_mul, hPQ, Matrix.transpose_one, Matrix.one_mul]
      _ = Qᵀ * (Pᵀ * P') := Matrix.mul_assoc _ _ _
      _ = a • Qᵀ := by rw [ha, Matrix.mul_smul, Matrix.mul_one]
  have h2 : Q' = b • Pᵀ := by
    calc Q' = (Pᵀ * Qᵀ) * Q' := by rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one, Matrix.one_mul]
      _ = Pᵀ * (Qᵀ * Q') := Matrix.mul_assoc _ _ _
      _ = b • Pᵀ := by rw [hb, Matrix.mul_smul, Matrix.mul_one]
  have h3 : P' * Q' = (a * b) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [h1, h2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.transpose_mul, hPQ, Matrix.transpose_one]
  rw [hPQ'] at h3
  rw [h1, h2]
  calc a • Qᵀ * (X * b • Pᵀ) = ((a * b) • (1 : Matrix (Fin n) (Fin n) R)) * (Qᵀ * (X * Pᵀ)) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_comm]
    _ = Qᵀ * (X * Pᵀ) := by rw [← h3, Matrix.one_mul]

theorem UpperTheory.V.Pa.adEx :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (n : ℕ) (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (χ : F.Γ → R) (V : Submodule A (Matrix (Fin n) (Fin n) R)), AdOk F ρ χ V → ∃ rep : Representation A F.Γ V, IsAd F ρ χ V rep := by
  intro l _ F A R _ _ _ n ρ χ V hV
  obtain ⟨h1, hmul, hform, hχ1, hχmul, had, htr⟩ := hV
  have hcinv : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right F.c_sq
  have hχc : χ F.c * χ F.c = 1 := by rw [← hχmul, F.c_sq, hχ1]
  have hρr : ∀ g : F.G₀, ρ g * ρ g⁻¹ = 1 := fun g => by rw [← hmul, mul_inv_cancel, h1]
  have hρl : ∀ g : F.G₀, ρ g⁻¹ * ρ g = 1 := fun g => by rw [← hmul, inv_mul_cancel, h1]
  have hcc' : ∀ x : F.Γ, F.c * (F.c * x) = x := fun x => by rw [← mul_assoc, F.c_sq, one_mul]
  have hcc : ∀ g : F.G₀, F.conj (F.conj g) = g := fun g => by
    apply Subtype.ext
    show F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = g
    simp only [hcinv, mul_assoc, F.c_sq, mul_one, hcc']
  have hχconj : ∀ g : F.G₀, χ (F.conj g : F.Γ) = χ g := fun g => by
    show χ (F.c * (g : F.Γ) * F.c⁻¹) = χ g
    rw [hcinv, hχmul, hχmul]
    linear_combination (χ (g : F.Γ)) * hχc
  let adV : F.G₀ → (V →ₗ[A] V) := fun g =>
    { toFun := fun Z => ⟨χ g • (ρ g * Z * ρ g⁻¹), had g Z Z.2⟩
      map_add' := fun Z W => by
        apply Subtype.ext
        simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun a Z => by
        apply Subtype.ext
        show χ g • (ρ g * (a • (Z : Matrix (Fin n) (Fin n) R)) * ρ g⁻¹) = a • (χ g • (ρ g * (Z : Matrix (Fin n) (Fin n) R) * ρ g⁻¹))
        rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm] }
  let τV : V →ₗ[A] V :=
    { toFun := fun Z => ⟨-(χ F.c • (Z : Matrix (Fin n) (Fin n) R)ᵀ), V.neg_mem (htr Z Z.2)⟩
      map_add' := fun Z W => by
        apply Subtype.ext
        simp [add_comm]
      map_smul' := fun a Z => by
        apply Subtype.ext
        show -(χ F.c • (a • (Z : Matrix (Fin n) (Fin n) R))ᵀ) = a • -(χ F.c • (Z : Matrix (Fin n) (Fin n) R)ᵀ)
        rw [Matrix.transpose_smul, smul_comm, smul_neg] }
  have hadEq : ∀ g g' : F.G₀, (g : F.Γ) = g' → ∀ Z, adV g Z = adV g' Z := by
    intro g g' h Z
    rw [Subtype.ext h]
  have hadone : ∀ Z, adV 1 Z = Z := by
    intro Z
    apply Subtype.ext
    simp [adV, h1, hχ1]
  have hadmul : ∀ g h Z, adV (g * h) Z = adV g (adV h Z) := by
    intro g h Z
    apply Subtype.ext
    simp [adV, hmul, _root_.mul_inv_rev, hχmul, Matrix.mul_assoc, smul_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hττ : ∀ Z, τV (τV Z) = Z := by
    intro Z
    apply Subtype.ext
    simp [τV, smul_smul, hχc]
  have hτad : ∀ g Z, τV (adV g Z) = adV (F.conj g) (τV Z) := by
    intro g Z
    apply Subtype.ext
    obtain ⟨a, ha⟩ := hform g
    obtain ⟨b, hb⟩ := hform g⁻¹
    rw [map_inv] at hb
    have hm := conj_eq_transpose_conj_of_transpose_mul_eq_smul_one (ρ g) (ρ g⁻¹) (ρ (F.conj g)) (ρ (F.conj g)⁻¹) (Z : Matrix (Fin n) (Fin n) R)ᵀ a b
      (hρr g) (hρl g) (hρr _) ha hb
    simp only [adV, τV, LinearMap.coe_mk, AddHom.coe_mk, hχconj]
    simp only [Matrix.transpose_smul, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_smul, Matrix.smul_mul, smul_neg, smul_smul, hm, mul_comm]
  have hswap : ∀ g W, adV g (τV W) = τV (adV (F.conj g) W) := by
    intro g W
    rw [hτad, hcc]
  have hηc : ∀ h : F.Γ, F.η h ≠ 1 → F.η h = -1 := fun h hh => (Int.units_eq_one_or _).resolve_left hh
  have hmemc : ∀ h : F.Γ, F.η h ≠ 1 → F.c * h ∈ F.η.ker := fun h hh => by
    rw [MonoidHom.mem_ker, map_mul, F.η_c, hηc h hh]
    rfl
  let f : F.Γ → (V →ₗ[A] V) := fun h =>
    if hh : F.η h = 1 then adV ⟨h, hh⟩ else τV ∘ₗ adV ⟨F.c * h, hmemc h hh⟩
  have hcne : F.η F.c ≠ 1 := by
    rw [F.η_c]
    decide
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, ?_, ?_⟩
  · apply LinearMap.ext
    intro Z
    simp only [f, dif_pos (map_one F.η)]
    exact hadone Z
  · intro x y
    apply LinearMap.ext
    intro Z
    rw [Module.End.mul_apply]
    by_cases hx : F.η x = 1 <;> by_cases hy : F.η y = 1
    · have hxy : F.η (x * y) = 1 := by rw [map_mul, hx, hy, one_mul]
      simp only [f, dif_pos hxy, dif_pos hx, dif_pos hy]
      rw [← hadmul]
      rfl
    · have hxy : F.η (x * y) ≠ 1 := by rw [map_mul, hx, one_mul]; exact hy
      simp only [f, dif_neg hxy, dif_pos hx, dif_neg hy, LinearMap.comp_apply]
      rw [hswap, ← hadmul]
      congr 1
      apply hadEq
      simp only [Subgroup.coe_mul, MulMemClass.coe_mul]
      show F.c * (x * y) = F.c * x * F.c⁻¹ * (F.c * y)
      simp only [hcinv, mul_assoc, hcc']
    · have hxy : F.η (x * y) ≠ 1 := by rw [map_mul, hy, mul_one]; exact hx
      simp only [f, dif_neg hxy, dif_neg hx, dif_pos hy, LinearMap.comp_apply]
      rw [← hadmul]
      congr 1
      apply hadEq
      simp only [Subgroup.coe_mul, MulMemClass.coe_mul]
      show F.c * (x * y) = F.c * x * y
      rw [mul_assoc]
    · have hxy : F.η (x * y) = 1 := by
        rw [map_mul, hηc x hx, hηc y hy]
        rfl
      simp only [f, dif_pos hxy, dif_neg hx, dif_neg hy, LinearMap.comp_apply]
      rw [hswap, hττ, ← hadmul]
      apply hadEq
      simp only [Subgroup.coe_mul, MulMemClass.coe_mul]
      show x * y = F.c * (F.c * x) * F.c⁻¹ * (F.c * y)
      simp only [hcinv, mul_assoc, hcc']
  · intro g Z
    show ((f (g : F.Γ)) Z : Matrix (Fin n) (Fin n) R) = _
    simp only [f, dif_pos (show F.η (g : F.Γ) = 1 from g.2)]
    rfl
  · intro Z
    show ((f F.c) Z : Matrix (Fin n) (Fin n) R) = _
    simp only [f, dif_neg hcne, LinearMap.comp_apply]
    rw [hadEq _ 1 (by show F.c * F.c = 1; exact F.c_sq) Z, hadone]
    rfl
