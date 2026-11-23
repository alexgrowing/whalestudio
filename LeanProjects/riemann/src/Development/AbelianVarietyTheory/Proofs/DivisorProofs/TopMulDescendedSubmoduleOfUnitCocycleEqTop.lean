import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open TensorProduct GlobalTheory.EtC

namespace GlobalTheory.DescTop

theorem top_mul_descMod_eq_top (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (u : (B ⊗[A] B)ˣ) (hu : UCoc A B u) : (⊤ : Submodule A B) * descMod A B u = ⊤ := by
  set F : B →ₗ[A] B ⊗[A] B := (LinearMap.mulLeft A (u : B ⊗[A] B)) ∘ₗ
    (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toLinearMap with hF
  set G : B →ₗ[A] B ⊗[A] B := (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toLinearMap with hG
  set f13 := Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)
  set f12 := Algebra.TensorProduct.map (AlgHom.id A B) (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)
  set f23 := (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B))
  have hD : descMod A B u = LinearMap.ker (F - G) := by
    rw [← LinearMap.eqLocus_eq_ker_sub]; rfl
  have hLF : LinearMap.lTensor B F = (LinearMap.mulLeft A (f23 (u : B ⊗[A] B))) ∘ₗ f13.toLinearMap := by
    apply TensorProduct.ext'
    intro c b
    simp [hF, f23, f13, Algebra.TensorProduct.tmul_mul_tmul]
  have hLG : LinearMap.lTensor B G = f12.toLinearMap := by
    apply TensorProduct.ext'
    intro c b
    simp [hG, f12]

  have hinv : f23 (u : B ⊗[A] B) * f13 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) = f12 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) := by
    have h1 : f13 (u : B ⊗[A] B) * f13 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h2 : f12 (u : B ⊗[A] B) * f12 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hc : f13 (u : B ⊗[A] B) = f12 (u : B ⊗[A] B) * f23 (u : B ⊗[A] B) := hu
    calc f23 (u : B ⊗[A] B) * f13 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B)
        = f23 (u : B ⊗[A] B) * f13 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) *
            (f12 (u : B ⊗[A] B) * f12 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B)) := by rw [h2, mul_one]
      _ = (f13 (u : B ⊗[A] B) * f13 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B)) * f12 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) := by
            rw [hc]; ring
      _ = f12 ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) := by rw [h1, one_mul]
  have hex := Module.Flat.lTensor_exact B (LinearMap.exact_subtype_ker_map (F - G))
  have hy : ((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B) ∈
      LinearMap.range (LinearMap.lTensor B (LinearMap.ker (F - G)).subtype) := by
    rw [← hex.linearMap_ker_eq, LinearMap.mem_ker, LinearMap.lTensor_sub, LinearMap.sub_apply, sub_eq_zero,
      hLF, hLG]
    simpa using hinv
  obtain ⟨z, hz⟩ := hy
  have hmem : ∀ w : B ⊗[A] LinearMap.ker (F - G),
      Algebra.TensorProduct.lmul' A (LinearMap.lTensor B (LinearMap.ker (F - G)).subtype w) ∈
        (⊤ : Submodule A B) * descMod A B u := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c m =>
      rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
      exact Submodule.mul_mem_mul Submodule.mem_top (by rw [hD]; exact m.2)
    | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
  have hv := hmem z
  rw [hz] at hv
  set v := Algebra.TensorProduct.lmul' A (((u⁻¹ : (B ⊗[A] B)ˣ) : B ⊗[A] B)) with hvdef
  have hvu : IsUnit v := (Units.isUnit (u⁻¹)).map (Algebra.TensorProduct.lmul' A (S := B))
  obtain ⟨w, hw⟩ := hvu.exists_left_inv
  have hle : (⊤ : Submodule A B) * ((⊤ : Submodule A B) * descMod A B u) ≤ (⊤ : Submodule A B) * descMod A B u := by
    rw [← mul_assoc]; first
      | exact Submodule.mul_le_mul le_top le_rfl
      | exact mul_le_mul_right' le_top _
      | (gcongr; exact le_top)
  rw [eq_top_iff]
  intro b _
  have : b = (b * w) * v := by rw [mul_assoc, hw, mul_one]
  rw [this]
  exact hle (Submodule.mul_mem_mul Submodule.mem_top hv)

end GlobalTheory.DescTop
