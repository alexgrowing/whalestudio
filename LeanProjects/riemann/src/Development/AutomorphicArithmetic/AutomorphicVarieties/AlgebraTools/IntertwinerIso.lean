import Mathlib

open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.intertwiner_iso :
    ∀ {F Γ : Type} [Field F] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (ρ : Γ → Matrix m m F) (ρ' : Γ → Matrix n n F), Submodule.span F (Set.range ρ) = ⊤ → Submodule.span F (Set.range ρ') = ⊤ → (∀ V : Matrix m n F, (∀ g, ρ g * V = V * ρ' g) → V ≠ 0 → ∃ V' : Matrix n m F, V * V' = 1 ∧ V' * V = 1) ∧ ∀ V : Matrix m m F, (∀ g, ρ g * V = V * ρ g) → ∃ c : F, V = c • (1 : Matrix m m F) := by
  intro F Γ _ m n _ _ _ _ ρ ρ' hρ hρ'
  refine ⟨fun V hV hV0 => ?_, fun V hV => ?_⟩
  · have hR : ∀ A : Matrix m m F, ∃ C : Matrix n n F, A * V = V * C := by
      intro A
      have hA : A ∈ Submodule.span F (Set.range ρ) := by rw [hρ]; exact Submodule.mem_top
      induction hA using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        exact ⟨ρ' g, hV g⟩
      | zero => exact ⟨0, by rw [Matrix.zero_mul, Matrix.mul_zero]⟩
      | add x y _ _ hx hy =>
        obtain ⟨C, hC⟩ := hx
        obtain ⟨D, hD⟩ := hy
        exact ⟨C + D, by rw [Matrix.add_mul, Matrix.mul_add, hC, hD]⟩
      | smul a x _ hx =>
        obtain ⟨C, hC⟩ := hx
        exact ⟨a • C, by rw [Matrix.smul_mul, hC, Matrix.mul_smul]⟩
    have hL : ∀ B : Matrix n n F, ∃ A : Matrix m m F, V * B = A * V := by
      intro B
      have hB : B ∈ Submodule.span F (Set.range ρ') := by rw [hρ']; exact Submodule.mem_top
      induction hB using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        exact ⟨ρ g, (hV g).symm⟩
      | zero => exact ⟨0, by rw [Matrix.zero_mul, Matrix.mul_zero]⟩
      | add x y _ _ hx hy =>
        obtain ⟨C, hC⟩ := hx
        obtain ⟨D, hD⟩ := hy
        exact ⟨C + D, by rw [Matrix.add_mul, Matrix.mul_add, hC, hD]⟩
      | smul a x _ hx =>
        obtain ⟨C, hC⟩ := hx
        exact ⟨a • C, by rw [Matrix.smul_mul, ← hC, Matrix.mul_smul]⟩
    have inj : Function.Injective (Matrix.toLin' V) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      rw [Matrix.toLin'_apply] at hx
      by_contra hne
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      have hj' : x j ≠ 0 := by simpa using hj
      apply hV0
      ext i k
      obtain ⟨A, hA⟩ := hL (Matrix.single k j (x j)⁻¹)
      have h1 : V *ᵥ (Matrix.single k j (x j)⁻¹ *ᵥ x) = 0 := by
        rw [Matrix.mulVec_mulVec, hA, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
      rw [Matrix.single_mulVec, inv_mul_cancel₀ hj'] at h1
      have h2 := congrFun h1 i
      change (V *ᵥ Pi.single k 1) i = 0 at h2
      rw [Matrix.mulVec_single_one] at h2
      simpa using h2
    have surj : Function.Surjective (Matrix.toLin' V) := by
      obtain ⟨i0, k0, h0⟩ : ∃ i k, V i k ≠ 0 := by
        by_contra h
        push_neg at h
        exact hV0 (Matrix.ext fun i k => by simp [h i k])
      intro y
      let A : Matrix m m F := Matrix.of fun i a => if a = i0 then y i * (V i0 k0)⁻¹ else 0
      obtain ⟨C, hC⟩ := hR A
      refine ⟨C *ᵥ Pi.single k0 1, ?_⟩
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← hC, ← Matrix.mulVec_mulVec,
        Matrix.mulVec_single_one]
      funext i
      simp [A, Matrix.mulVec, dotProduct, ite_mul, h0]
    let e := LinearEquiv.ofBijective (Matrix.toLin' V) ⟨inj, surj⟩
    have he1 : Matrix.toLin' V ∘ₗ (e.symm : (m → F) →ₗ[F] (n → F)) = LinearMap.id :=
      LinearMap.ext fun y => e.apply_symm_apply y
    have he2 : (e.symm : (m → F) →ₗ[F] (n → F)) ∘ₗ Matrix.toLin' V = LinearMap.id :=
      LinearMap.ext fun y => e.symm_apply_apply y
    refine ⟨LinearMap.toMatrix' (e.symm : (m → F) →ₗ[F] (n → F)), ?_, ?_⟩
    · have h := LinearMap.toMatrix'_comp (Matrix.toLin' V) (e.symm : (m → F) →ₗ[F] (n → F))
      rw [he1, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at h
      exact h.symm
    · have h := LinearMap.toMatrix'_comp (e.symm : (m → F) →ₗ[F] (n → F)) (Matrix.toLin' V)
      rw [he2, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at h
      exact h.symm
  · have hC : ∀ A : Matrix m m F, Commute A V := by
      intro A
      have hA : A ∈ Submodule.span F (Set.range ρ) := by rw [hρ]; exact Submodule.mem_top
      induction hA using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        exact hV g
      | zero => exact Commute.zero_left V
      | add x y _ _ hx hy => exact hx.add_left hy
      | smul a x _ hx => exact hx.smul_left a
    obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (fun i j _ => hC _)
    refine ⟨c, ?_⟩
    rw [← hc]
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]
