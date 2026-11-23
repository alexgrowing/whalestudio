import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

noncomputable section

namespace GlobalTheory.FinGL.MackeyCosets

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem mem_eig' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ G V) (S : Set G)
    (χ : G → ℂ) (v : V) : v ∈ eig τ S χ ↔ ∀ g ∈ S, τ g v = χ g • v := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

variable {G : Type} [Group G] {P U : Subgroup G} {V : Type} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ P V) (χ : G → ℂ)

theorem left_eq (φ : eig (Representation.coind P.subtype σ) (U : Set G) χ) (p : P) (g : G) :
    φ.1.1 (p * g) = σ p (φ.1.1 g) := φ.1.2 p g

theorem right_eq (φ : eig (Representation.coind P.subtype σ) (U : Set G) χ) (u : G) (hu : u ∈ U) (g : G) :
    φ.1.1 (g * u) = χ u • φ.1.1 g := by
  have h := (mem_eig' _ _ _ _).1 φ.2 u hu
  exact congrArg (fun f : Representation.coindV P.subtype σ => f.1 g) h

theorem eval_mem (φ : eig (Representation.coind P.subtype σ) (U : Set G) χ) (y : G) :
    φ.1.1 y ∈ eig σ {p | y⁻¹ * (p : G) * y ∈ U} (fun p => χ (y⁻¹ * (p : G) * y)) := by
  rw [mem_eig']
  intro p hp
  rw [← left_eq, ← right_eq σ χ φ _ hp]
  congr 1
  group

theorem eval_dc (φ : eig (Representation.coind P.subtype σ) (U : Set G) χ) (y p u : G) (hp : p ∈ P) (hu : u ∈ U) :
    φ.1.1 (p * y * u) = χ u • σ ⟨p, hp⟩ (φ.1.1 y) := by
  rw [right_eq σ χ φ u hu, ← left_eq]

def evalMap {ι : Type} (x : ι → G) : eig (Representation.coind P.subtype σ) (U : Set G) χ →ₗ[ℂ]
    ∀ i : ι, eig σ {p | (x i)⁻¹ * (p : G) * x i ∈ U} (fun p => χ ((x i)⁻¹ * (p : G) * x i)) where
  toFun φ i := ⟨φ.1.1 (x i), eval_mem σ χ φ (x i)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem key (hχ : ∀ u ∈ U, ∀ u' ∈ U, χ (u * u') = χ u * χ u') (y : G) (v : V)
    (hv : v ∈ eig σ {p | y⁻¹ * (p : G) * y ∈ U} (fun p => χ (y⁻¹ * (p : G) * y)))
    (p p' : P) (u u' : G) (hu : u ∈ U) (hu' : u' ∈ U) (h : (p : G) * y * u = p' * y * u') :
    χ u • σ p v = χ u' • σ p' v := by
  have e : y⁻¹ * ((p'⁻¹ * p : P) : G) * y = u' * u⁻¹ := by
    have : u' = ((p' : G) * y)⁻¹ * (p * y * u) := by rw [h]; group
    rw [this]; push_cast; group
  have hm : u' * u⁻¹ ∈ U := U.mul_mem hu' (U.inv_mem hu)
  have h1 := (mem_eig' _ _ _ _).1 hv (p'⁻¹ * p) (by simp only [Set.mem_setOf_eq, e]; exact hm)
  simp only [e] at h1
  have h2 : σ p v = σ p' (σ (p'⁻¹ * p) v) := by
    rw [← Module.End.mul_apply, ← map_mul]; simp
  have h3 : χ u' = χ (u' * u⁻¹) * χ u := by rw [← hχ _ hm _ hu]; simp
  rw [h2, h1, map_smul, smul_smul, h3, mul_comm]

theorem surj (h1 : χ 1 = 1) (hχ : ∀ u ∈ U, ∀ u' ∈ U, χ (u * u') = χ u * χ u') {ι : Type} (x : ι → G)
    (hx : ∀ i i' : ι, ∀ p ∈ P, ∀ u ∈ U, p * x i = x i' * u → i = i') :
    Function.Surjective (evalMap (U := U) σ χ x) := by
  classical
  intro v
  let R : G → V → Prop := fun g w => ∃ i : ι, ∃ p : P, ∃ u ∈ U, g = p * x i * u ∧ w = χ u • σ p (v i).1
  have huniq : ∀ g w w', R g w → R g w' → w = w' := by
    rintro g w w' ⟨i, p, u, hu, rfl, rfl⟩ ⟨i', p', u', hu', h, rfl⟩
    have hi : i = i' := by
      refine hx i i' ((p' : G)⁻¹ * p) (P.mul_mem (P.inv_mem p'.2) p.2) (u' * u⁻¹) (U.mul_mem hu' (U.inv_mem hu)) ?_
      have : u' = ((p' : G) * x i')⁻¹ * (p * x i * u) := by rw [h]; group
      rw [this]; group
    subst hi
    exact key σ χ hχ (x i) _ (v i).2 p p' u u' hu hu' h
  let f : G → V := fun g => if h : ∃ w, R g w then h.choose else 0
  have hf : ∀ g w, R g w → f g = w := by
    intro g w hw
    have h : ∃ w, R g w := ⟨w, hw⟩
    simp only [f, dif_pos h]
    exact huniq g _ _ h.choose_spec hw
  have hf0 : ∀ g, (¬ ∃ w, R g w) → f g = 0 := by
    intro g h
    simp only [f, dif_neg h]
  have hL : ∀ (q : P) g w, R g w → R (q * g) (σ q w) := by
    rintro q g w ⟨i, p, u, hu, rfl, rfl⟩
    refine ⟨i, q * p, u, hu, by push_cast; group, ?_⟩
    rw [map_smul, map_mul, Module.End.mul_apply]
  have hR : ∀ t ∈ U, ∀ g w, R g w → R (g * t) (χ t • w) := by
    rintro t ht g w ⟨i, p, u, hu, rfl, rfl⟩
    refine ⟨i, p, u * t, U.mul_mem hu ht, by group, ?_⟩
    rw [hχ _ hu _ ht, smul_smul, mul_comm]
  have fL : ∀ (q : P) g, f (q * g) = σ q (f g) := by
    intro q g
    by_cases h : ∃ w, R g w
    · obtain ⟨w, hw⟩ := h
      rw [hf _ _ hw, hf _ _ (hL q g w hw)]
    · rw [hf0 g h, hf0, map_zero]
      rintro ⟨w, hw⟩
      have := hL q⁻¹ _ _ hw
      exact h ⟨_, by simpa using this⟩
  have fR : ∀ t ∈ U, ∀ g, f (g * t) = χ t • f g := by
    intro t ht g
    by_cases h : ∃ w, R g w
    · obtain ⟨w, hw⟩ := h
      rw [hf _ _ hw, hf _ _ (hR t ht g w hw)]
    · rw [hf0 g h, hf0, smul_zero]
      rintro ⟨w, hw⟩
      have := hR t⁻¹ (U.inv_mem ht) _ _ hw
      exact h ⟨_, by simpa using this⟩
  refine ⟨⟨⟨f, fL⟩, (mem_eig' _ _ _ _).2 fun t ht => ?_⟩, ?_⟩
  · ext g
    exact fR t ht g
  · funext i
    apply Subtype.ext
    exact hf _ _ ⟨i, 1, 1, U.one_mem, by simp, by simp [h1]⟩

theorem finrank_eig_coind : ∀ (G : Type) [Group G] (P U : Subgroup G) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (σ : Representation ℂ P V) (χ : G → ℂ), χ 1 = 1 → (∀ u ∈ U, ∀ u' ∈ U, χ (u * u') = χ u * χ u') → ∀ (ι : Type) [Fintype ι] (x : ι → G), (∀ i i' : ι, ∀ p ∈ P, ∀ u ∈ U, p * x i = x i' * u → i = i') → (∀ g : G, (∃ i : ι, ∃ p ∈ P, ∃ u ∈ U, g = p * x i * u) ∨ ∃ y : G, (∃ p ∈ P, ∃ u ∈ U, g = p * y * u) ∧ eig σ {p | y⁻¹ * (p : G) * y ∈ U} (fun p => χ (y⁻¹ * (p : G) * y)) = ⊥) → finrank ℂ (eig (Representation.coind P.subtype σ) (U : Set G) χ) = ∑ i : ι, finrank ℂ (eig σ {p | (x i)⁻¹ * (p : G) * x i ∈ U} (fun p => χ ((x i)⁻¹ * (p : G) * x i))) := by
  intro G _ P U V _ _ _ σ χ h1 hχ ι _ x hx hcov
  have hinj : Function.Injective (evalMap (U := U) σ χ x) := by
    rw [injective_iff_map_eq_zero]
    intro φ hφ
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change φ.1.1 g = 0
    rcases hcov g with ⟨i, p, hp, u, hu, rfl⟩ | ⟨y, ⟨p, hp, u, hu, rfl⟩, hy⟩
    · have : φ.1.1 (x i) = 0 := congrArg Subtype.val (congrFun hφ i)
      rw [eval_dc σ χ φ _ _ _ hp hu, this, map_zero, smul_zero]
    · have : φ.1.1 y = 0 := by
        have := eval_mem σ χ φ y
        rwa [hy, Submodule.mem_bot] at this
      rw [eval_dc σ χ φ _ _ _ hp hu, this, map_zero, smul_zero]
  rw [(LinearEquiv.ofBijective _ ⟨hinj, surj σ χ h1 hχ x hx⟩).finrank_eq, Module.finrank_pi_fintype]

end GlobalTheory.FinGL.MackeyCosets
