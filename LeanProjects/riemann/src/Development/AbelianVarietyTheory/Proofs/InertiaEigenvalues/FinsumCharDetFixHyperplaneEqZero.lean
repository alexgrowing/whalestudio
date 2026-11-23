import Mathlib

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

open Matrix in

theorem finsum_char_det_fix_hyperplane_eq_zero :
    ∀ (k : Type) [Field k] [Finite k] (r : ℕ) (ξ : kˣ →* ℂˣ), ξ ≠ 1 → ∀ a : Fin r → k, a ≠ 0 →
      ∑ᶠ g ∈ {g : GL (Fin r) k | ∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) k).mulVec v = v},
        ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) = 0 := by
  intro k _ _ r ξ hξ a ha
  set S : Set (GL (Fin r) k) :=
    {g : GL (Fin r) k | ∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) k).mulVec v = v} with hS
  obtain ⟨c, hc⟩ : ∃ c : kˣ, ξ c ≠ 1 := by
    by_contra h
    push_neg at h
    exact hξ (MonoidHom.ext h)
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha (funext h)
  set v₀ : Fin r → k := Pi.single i (a i)⁻¹ with hv₀
  have hav₀ : a ⬝ᵥ v₀ = 1 := by
    rw [hv₀, dotProduct_single, mul_inv_cancel₀ hi]
  set u : Fin r → k := ((c : k) - 1) • v₀ with hu
  set M : Matrix (Fin r) (Fin r) k :=
    1 + replicateCol (Fin 1) u * replicateRow (Fin 1) a with hM
  have hdet : M.det = (c : k) := by
    have h1 := det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) u a
    rw [hM]
    refine h1.trans ?_
    rw [hu, dotProduct_smul, hav₀, smul_eq_mul, mul_one]
    ring
  have hMfix : ∀ v, a ⬝ᵥ v = 0 → M *ᵥ v = v := by
    intro v hv
    rw [hM, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    have : replicateRow (Fin 1) a *ᵥ v = 0 := by
      ext j
      simp [Matrix.mulVec, replicateRow, hv]
    rw [this, Matrix.mulVec_zero, add_zero]
  let h₀ : GL (Fin r) k := Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact c.ne_zero)
  have hh₀ : (h₀ : Matrix (Fin r) (Fin r) k) = M := rfl
  have hdeth₀ : Matrix.GeneralLinearGroup.det h₀ = c := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, hh₀, hdet]
  have hh₀S : h₀ ∈ S := fun v hv => by rw [hh₀]; exact hMfix v hv
  have hmulS : ∀ g ∈ S, h₀ * g ∈ S := by
    intro g hg v hv
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg v hv, hh₀S v hv]
  have hinvS : ∀ g ∈ S, h₀⁻¹ * g ∈ S := by
    intro g hg v hv
    have h1 : (h₀ : Matrix (Fin r) (Fin r) k) *ᵥ v = v := hh₀S v hv
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg v hv]
    conv_lhs => rw [← h1]
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hbij : Set.BijOn (fun g => h₀ * g) S S := by
    refine ⟨fun g hg => hmulS g hg, fun x _ y _ hxy => mul_left_cancel hxy, ?_⟩
    intro g hg
    exact ⟨h₀⁻¹ * g, hinvS g hg, by simp⟩
  set F : GL (Fin r) k → ℂ := fun g => ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) with hF
  have hFmul : ∀ g, F (h₀ * g) = ((ξ c : ℂˣ) : ℂ) * F g := by
    intro g
    simp [hF, map_mul, hdeth₀]
  have key : ∑ᶠ g ∈ S, F (h₀ * g) = ∑ᶠ g ∈ S, F g :=
    finsum_mem_eq_of_bijOn (fun g => h₀ * g) hbij (fun x _ => rfl)
  simp_rw [hFmul] at key
  rw [← mul_finsum_mem] at key
  have hc' : ((ξ c : ℂˣ) : ℂ) ≠ 1 := by
    intro h
    exact hc (Units.ext h)
  have : (((ξ c : ℂˣ) : ℂ) - 1) * ∑ᶠ g ∈ S, F g = 0 := by
    rw [sub_mul, key, one_mul, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hc'
  · exact h

end GlobalTheory
