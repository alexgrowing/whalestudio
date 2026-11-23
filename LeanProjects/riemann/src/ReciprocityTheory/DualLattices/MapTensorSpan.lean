import ReciprocityTheory.DualLattices.TensorSpan

noncomputable section

namespace ReciprocityTheory.PGsh.L2.SecondCohomologyLattice

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem map_tensorSpan {X Y : Type} (σ : Y → X) (M : Submodule R (X → C)) :
    (tensorSpan R M).map (LinearMap.funLeft R C (Prod.map σ σ)) =
      tensorSpan R (M.map (LinearMap.funLeft R C σ)) := by
  rw [tensorSpan, tensorSpan, Submodule.map_span]
  congr 1
  ext F
  constructor
  · rintro ⟨_, ⟨g, hg, h, hh, rfl⟩, rfl⟩
    exact ⟨_, Submodule.mem_map_of_mem hg, _, Submodule.mem_map_of_mem hh, by
      funext p; simp [LinearMap.funLeft_apply]⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, _, ⟨h, hh, rfl⟩, rfl⟩
    exact ⟨_, ⟨g, hg, h, hh, rfl⟩, by funext p; simp [LinearMap.funLeft_apply]⟩

def slice2 {X : Type} (E : (X → C) →ₗ[C] (X → C)) : (X × X → C) →ₗ[C] (X × X → C) where
  toFun F p := E (fun a => E (fun b => F (a, b)) p.2) p.1
  map_add' F G := by
    funext p
    have h2 : (fun a => E (fun b => (F + G) (a, b)) p.2) =
        (fun a => E (fun b => F (a, b)) p.2) + (fun a => E (fun b => G (a, b)) p.2) := by
      funext a
      rw [show (fun b => (F + G) (a, b)) = (fun b => F (a, b)) + (fun b => G (a, b)) from rfl,
        map_add]
      rfl
    show E (fun a => E (fun b => (F + G) (a, b)) p.2) p.1 =
      E (fun a => E (fun b => F (a, b)) p.2) p.1 + E (fun a => E (fun b => G (a, b)) p.2) p.1
    rw [h2, map_add]
    rfl
  map_smul' c F := by
    funext p
    have h2 : (fun a => E (fun b => (c • F) (a, b)) p.2) =
        c • (fun a => E (fun b => F (a, b)) p.2) := by
      funext a
      rw [show (fun b => (c • F) (a, b)) = c • (fun b => F (a, b)) from rfl, map_smul]
      rfl
    show E (fun a => E (fun b => (c • F) (a, b)) p.2) p.1 =
      c • E (fun a => E (fun b => F (a, b)) p.2) p.1
    rw [h2, map_smul]
    rfl

theorem slice2_tmul {X : Type} (E : (X → C) →ₗ[C] (X → C)) (g h : X → C) :
    slice2 E (fun p => g p.1 * h p.2) = fun p => E g p.1 * E h p.2 := by
  funext p
  show E (fun a => E (fun b => g a * h b) p.2) p.1 = E g p.1 * E h p.2
  have h1 : (fun a => E (fun b => g a * h b) p.2) = E h p.2 • g := by
    funext a
    rw [show (fun b => g a * h b) = g a • h from rfl, map_smul]
    simp [mul_comm]
  rw [h1, map_smul]
  simp [mul_comm]

theorem slice2_eq_self {X : Type} (E : (X → C) →ₗ[C] (X → C)) (W : Submodule C (X → C))
    (hE : ∀ f ∈ W, E f = f) (F : X × X → C) (h1 : ∀ a, (fun b => F (a, b)) ∈ W)
    (h2 : ∀ y, (fun a => F (a, y)) ∈ W) : slice2 E F = F := by
  funext p
  show E (fun a => E (fun b => F (a, b)) p.2) p.1 = F p
  have h3 : (fun a => E (fun b => F (a, b)) p.2) = fun a => F (a, p.2) := by
    funext a
    rw [hE _ (h1 a)]
  rw [h3, hE _ (h2 p.2)]

theorem slice2_mem {X : Type} (E : (X → C) →ₗ[C] (X → C)) (M M' : Submodule R (X → C))
    (hM : ∀ f ∈ M, E f ∈ M') {F : X × X → C} (hF : F ∈ tensorSpan R M) :
    slice2 E F ∈ tensorSpan R M' := by
  induction hF using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨g, hg, h, hh, rfl⟩ := hF
    rw [slice2_tmul]
    exact Submodule.subset_span ⟨E g, hM g hg, E h, hM h hh, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add F G _ _ hF hG => rw [map_add]; exact Submodule.add_mem _ hF hG
  | smul r F _ hF =>
    rw [← algebraMap_smul C r F, map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ r hF

theorem apply_eq_sum {X : Type} [Fintype X] [DecidableEq X] (E : (X → C) →ₗ[C] (X → C))
    (f : X → C) (y : X) :
    E f y = ∑ a, f a * E (fun j => if a = j then 1 else 0) y := by
  have hf : f = ∑ a, f a • (fun j => if a = j then (1 : C) else 0) := by
    funext j
    simp [Finset.sum_apply]
  conv_lhs => rw [hf]
  rw [map_sum, Finset.sum_apply]
  simp [map_smul]

end ReciprocityTheory.PGsh.L2.SecondCohomologyLattice
