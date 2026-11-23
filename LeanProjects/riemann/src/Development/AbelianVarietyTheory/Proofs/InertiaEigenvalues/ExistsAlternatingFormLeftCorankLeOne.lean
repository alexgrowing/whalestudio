import Mathlib

namespace GlobalTheory.AltCorank

open Module

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def Good (S₁ S₂ : Submodule K V) : Prop :=
  ∃ ω : V →ₗ[K] V →ₗ[K] K, (∀ v, ω v v = 0) ∧ ∀ x : Fin 2 → V, (∀ a, x a ∈ S₁) →
    (∀ a, ∀ y ∈ S₂, ω (x a) y = 0) → ¬ LinearIndependent K x

theorem good_step (S₁ S₂ T₁ T₂ : Submodule K V) (u v : V) (φ ψ : V →ₗ[K] K)
    (hφu : φ u = 1) (hφv : φ v = 0) (hψu : ψ u = 0) (hψv : ψ v = 1) (hv : v ∈ S₂)
    (hu : u ∈ S₂ ∨ ∀ x ∈ S₁, ψ x = 0)
    (h₁ : ∀ x ∈ S₁, φ x = 0 → ψ x = 0 → x ∈ T₁)
    (h₂ : ∀ y ∈ T₂, y ∈ S₂ ∧ φ y = 0 ∧ ψ y = 0) (h : Good T₁ T₂) : Good S₁ S₂ := by
  obtain ⟨ω, hω, hk⟩ := h
  let π : V →ₗ[K] V := LinearMap.id - φ.smulRight u - ψ.smulRight v
  have hπ : ∀ x, π x = x - φ x • u - ψ x • v := fun x => rfl
  let Ω : V →ₗ[K] V →ₗ[K] K :=
    ω.compl₁₂ π π + (LinearMap.mul K K).compl₁₂ φ ψ - (LinearMap.mul K K).compl₁₂ ψ φ
  have hΩ : ∀ x y, Ω x y = ω (π x) (π y) + φ x * ψ y - ψ x * φ y := fun x y => rfl
  have hπu : π u = 0 := by simp [hπ, hφu, hψu]
  have hπv : π v = 0 := by simp [hπ, hφv, hψv]
  refine ⟨Ω, fun x => by rw [hΩ, hω]; ring, fun x hx hz => ?_⟩
  have e1 : ∀ a, φ (x a) = 0 := fun a => by
    have := hz a v hv
    rw [hΩ, hπv, hφv, hψv] at this
    simpa using this
  have e2 : ∀ a, ψ (x a) = 0 := fun a => by
    rcases hu with hu | hu
    · have := hz a u hu
      rw [hΩ, hπu, hφu, hψu] at this
      simpa using this
    · exact hu _ (hx a)
  refine hk x (fun a => h₁ _ (hx a) (e1 a) (e2 a)) fun a y hy => ?_
  obtain ⟨hy, f1, f2⟩ := h₂ y hy
  have := hz a y hy
  rw [hΩ, hπ, hπ, e1, e2, f1, f2] at this
  simpa using this

theorem finrank_inf_ker [Module.Finite K V] (S : Submodule K V) (φ : V →ₗ[K] K) (u : V)
    (hu : u ∈ S) (hφ : φ u = 1) :
    finrank K (S ⊓ LinearMap.ker φ : Submodule K V) + 1 = finrank K S := by
  have hne : (φ.domRestrict S : Module.Dual K S) ≠ 0 := by
    intro h
    have := LinearMap.congr_fun h ⟨u, hu⟩
    simp [hφ] at this
  rw [← Module.Dual.finrank_ker_add_one_of_ne_zero hne, LinearMap.ker_domRestrict,
    ← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]

theorem exists_dual (S : Submodule K V) (u : V) (hu : u ∉ S) :
    ∃ φ : V →ₗ[K] K, φ u = 1 ∧ ∀ x ∈ S, φ x = 0 := by
  obtain ⟨f, hf, hS⟩ := S.exists_dual_map_eq_bot_of_notMem hu inferInstance
  refine ⟨(f u)⁻¹ • f, by simp [hf], fun x hx => ?_⟩
  have : f x ∈ S.map f := ⟨x, hx, rfl⟩
  rw [hS] at this
  simp [(Submodule.mem_bot K).1 this]

theorem good_of_finrank_eq [Module.Finite K V] (n : ℕ) :
    ∀ S₁ S₂ : Submodule K V, finrank K S₁ = n → finrank K S₂ = n → Good S₁ S₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S₁ S₂ h₁ h₂
  by_cases hE : S₁ = S₂
  · subst hE
    by_cases hx : ∃ x : Fin 2 → V, (∀ a, x a ∈ S₁) ∧ LinearIndependent K x
    · obtain ⟨x, hx, hli⟩ := hx
      have n0 : x 0 ∉ Submodule.span K {x 1} := by
        have := hli.notMem_span_image (s := {1}) (x := 0) (by simp)
        simpa using this
      have n1 : x 1 ∉ Submodule.span K {x 0} := by
        have := hli.notMem_span_image (s := {0}) (x := 1) (by simp)
        simpa using this
      obtain ⟨φ, a1, a2⟩ := exists_dual _ _ n0
      obtain ⟨ψ, b1, b2⟩ := exists_dual _ _ n1
      have a3 := a2 _ (Submodule.mem_span_singleton_self _)
      have b3 := b2 _ (Submodule.mem_span_singleton_self _)
      have hlt : finrank K (S₁ ⊓ LinearMap.ker φ ⊓ LinearMap.ker ψ : Submodule K V) < n := by
        have := finrank_inf_ker S₁ φ _ (hx 0) a1
        have := Submodule.finrank_mono
          (inf_le_left : S₁ ⊓ LinearMap.ker φ ⊓ LinearMap.ker ψ ≤ S₁ ⊓ LinearMap.ker φ)
        omega
      refine good_step S₁ S₁ _ _ (x 0) (x 1) φ ψ a1 a3 b3 b1 (hx 1) (Or.inl (hx 0)) ?_ ?_
        (ih _ hlt _ _ rfl rfl)
      · intro y h1 h2 h3
        exact ⟨⟨h1, h2⟩, h3⟩
      · rintro y ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, h3⟩
    · exact ⟨0, fun _ => rfl, fun x h1 _ h2 => hx ⟨x, h1, h2⟩⟩
  · have l1 : ¬ S₁ ≤ S₂ := fun h => hE (Submodule.eq_of_le_of_finrank_eq h (h₁.trans h₂.symm))
    have l2 : ¬ S₂ ≤ S₁ := fun h =>
      hE (Submodule.eq_of_le_of_finrank_eq h (h₂.trans h₁.symm)).symm
    obtain ⟨u, hu1, hu2⟩ := SetLike.not_le_iff_exists.1 l1
    obtain ⟨v, hv2, hv1⟩ := SetLike.not_le_iff_exists.1 l2
    obtain ⟨φ, a1, a2⟩ := exists_dual _ _ hu2
    obtain ⟨ψ, b1, b2⟩ := exists_dual _ _ hv1
    have c1 := finrank_inf_ker S₁ φ u hu1 a1
    have c2 := finrank_inf_ker S₂ ψ v hv2 b1
    refine good_step S₁ S₂ (S₁ ⊓ LinearMap.ker φ) (S₂ ⊓ LinearMap.ker ψ) u v φ ψ a1 (a2 _ hv2)
      (b2 _ hu1) b1 hv2 (Or.inr b2) ?_ ?_ (ih (n - 1) (by omega) _ _ (by omega) (by omega))
    · intro y h1 h2 _
      exact ⟨h1, h2⟩
    · rintro y ⟨h1, h2⟩
      exact ⟨h1, a2 _ h1, h2⟩

theorem exists_alt_corank_le_one :
    ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
      (S₁ S₂ : Submodule K V), Module.finrank K S₁ = Module.finrank K S₂ →
      ∃ ω : V →ₗ[K] V →ₗ[K] K, (∀ v, ω v v = 0) ∧ ∀ x : Fin 2 → V, (∀ a, x a ∈ S₁) →
        (∀ a, ∀ y ∈ S₂, ω (x a) y = 0) → ¬ LinearIndependent K x :=
  fun _ _ _ _ _ _ S₁ S₂ h => good_of_finrank_eq _ S₁ S₂ h rfl

end GlobalTheory.AltCorank
