import Mathlib

noncomputable section

namespace GlobalTheory.Cusp.Shear

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {N N' : Subgroup G}
  {V : Type} [AddCommGroup V] [TopologicalSpace V] {s : V → G} {π : N → V}

def prodMap (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (z : N' × V) : N :=
  ⟨z.1 * s z.2, N.mul_mem (hle z.1.2) (hs z.2)⟩

theorem coe_prodMap (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (z : N' × V) :
    (prodMap hle hs z : G) = z.1 * s z.2 := rfl

theorem map_inv_of_mul (hπmul : ∀ a b : N, π (a * b) = π a + π b) (a : N) : π a⁻¹ = -π a := by
  have h1 : π 1 = 0 := by simpa using hπmul 1 1
  have := hπmul a a⁻¹
  rw [mul_inv_cancel, h1] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

theorem mul_inv_mem (hs : ∀ v, s v ∈ N) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
    (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N') (n : N) :
    (n : G) * (s (π n))⁻¹ ∈ N' := by
  have h := (hker (n * (⟨s (π n), hs _⟩ : N)⁻¹)).1 (by
    rw [hπmul, map_inv_of_mul hπmul, hπs ⟨s (π n), hs _⟩ _ rfl, add_neg_cancel])
  simpa using h

def prodHomeo (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π)
    (hπmul : ∀ a b : N, π (a * b) = π a + π b) (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v)
    (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N') : N' × V ≃ₜ N where
  toFun := prodMap hle hs
  invFun n := (⟨(n : G) * (s (π n))⁻¹, mul_inv_mem hs hπmul hπs hker n⟩, π n)
  left_inv z := by
    have hv : π (prodMap hle hs z) = z.2 := by
      have e : prodMap hle hs z = ⟨z.1, hle z.1.2⟩ * ⟨s z.2, hs _⟩ := rfl
      rw [e, hπmul, hπs ⟨s z.2, hs _⟩ z.2 rfl, (hker _).2 z.1.2, zero_add]
    refine Prod.ext (Subtype.ext ?_) hv
    simp [hv, coe_prodMap]
  right_inv n := by
    apply Subtype.ext
    simp [coe_prodMap]
  continuous_toFun := by
    unfold prodMap
    fun_prop
  continuous_invFun := by
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) hπc
    fun_prop

@[simp] theorem prodHomeo_apply (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (hsc : Continuous s) (hπc : Continuous π)
    (hπmul : ∀ a b : N, π (a * b) = π a + π b) (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v)
    (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N') (z : N' × V) :
    (prodHomeo hle hs hsc hπc hπmul hπs hker z : G) = z.1 * s z.2 := rfl

@[simp] theorem prodHomeo_symm_apply_fst (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (hsc : Continuous s)
    (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
    (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N') (n : N) :
    (((prodHomeo hle hs hsc hπc hπmul hπs hker).symm n).1 : G) = n * (s (π n))⁻¹ := rfl

@[simp] theorem prodHomeo_symm_apply_snd (hle : N' ≤ N) (hs : ∀ v, s v ∈ N) (hsc : Continuous s)
    (hπc : Continuous π) (hπmul : ∀ a b : N, π (a * b) = π a + π b)
    (hπs : ∀ (a : N) (v : V), (a : G) = s v → π a = v) (hker : ∀ a : N, π a = 0 ↔ (a : G) ∈ N') (n : N) :
    ((prodHomeo hle hs hsc hπc hπmul hπs hker).symm n).2 = π n := rfl

end GlobalTheory.Cusp.Shear

end
