import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenGraph
open GlobalTheory.PrimLift

namespace GlobalTheory.PrimLift.SphericalEisensteinCover

variable {X : Type} [TopologicalSpace X] {P : Set X → (X → ℂ) → Prop}

theorem mem_graph_iff {O : Set X} {g : X → ℂ} (e : Etale P) :
    e ∈ (fun y => Etale.mk P y (g y)) '' O ↔ Etale.proj P e ∈ O ∧ e.val = g (Etale.proj P e) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨Etale.proj P e, h1, ?_⟩
    show Etale.mk P _ (g _) = e
    rw [← h2]
    rfl

theorem continuous_proj
    (hopen : ∀ O f, P O f → IsOpen O)
    (hmono : ∀ O O' f, P O f → IsOpen O' → O' ⊆ O → P O' f)
    (hadd : ∀ O f (c : ℂ), P O f → P O (fun y => f y + c))
    (hcov : ∀ x, ∃ O f, x ∈ O ∧ P O f) :
    Continuous (Etale.proj P) := by
  rw [continuous_def]
  intro V hV
  rw [isOpen_iff_forall_mem_open]
  intro e he
  obtain ⟨O1, f1, h1, hP1⟩ := hcov (Etale.proj P e)
  have hP' : P (O1 ∩ V) (fun y => f1 y + (e.val - f1 (Etale.proj P e))) :=
    hadd _ _ _ (hmono _ _ _ hP1 ((hopen _ _ hP1).inter hV) Set.inter_subset_left)
  refine ⟨_, ?_, Etale.isOpen_graph hP', ?_⟩
  · intro e' he'
    exact ((mem_graph_iff e').1 he').1.2
  · rw [mem_graph_iff]
    refine ⟨⟨h1, he⟩, ?_⟩
    simp

end GlobalTheory.PrimLift.SphericalEisensteinCover

open GlobalTheory.PrimLift.SphericalEisensteinCover in
theorem GlobalTheory.PrimLift.Etale.isCoveringMap_proj
    {X : Type} [TopologicalSpace X] (P : Set X → (X → ℂ) → Prop)
    (hopen : ∀ O f, P O f → IsOpen O)
    (hmono : ∀ O O' f, P O f → IsOpen O' → O' ⊆ O → P O' f)
    (hadd : ∀ O f (c : ℂ), P O f → P O (fun y => f y + c))
    (hcov : ∀ x, ∃ O f, x ∈ O ∧ P O f)
    (heq : ∀ O f g, P O f → P O g → IsOpen {y | y ∈ O ∧ f y = g y}) :
    IsCoveringMap (GlobalTheory.PrimLift.Etale.proj P) := by
  have hproj := continuous_proj hopen hmono hadd hcov
  intro x
  obtain ⟨O, f, hxO, hP⟩ := hcov x
  letI : TopologicalSpace ℂ := ⊥
  haveI : DiscreteTopology ℂ := ⟨rfl⟩
  have hO : IsOpen O := hopen _ _ hP
  let H : Etale.proj P ⁻¹' O ≃ₜ O × ℂ :=
    { toFun := fun e => (⟨Etale.proj P e.1, e.2⟩, e.1.val - f (Etale.proj P e.1))
      invFun := fun p => ⟨Etale.mk P p.1.1 (f p.1.1 + p.2), p.1.2⟩
      left_inv := by
        intro e
        apply Subtype.ext
        show Etale.mk P _ _ = e.1
        rw [add_sub_cancel]
        rfl
      right_inv := by
        intro p
        ext <;> simp
      continuous_toFun := by
        refine Continuous.prodMk ?_ ?_
        · exact (hproj.comp continuous_subtype_val).subtype_mk _
        · rw [continuous_discrete_rng]
          intro c
          have hG := Etale.isOpen_graph (hadd _ _ c hP)
          convert hG.preimage continuous_subtype_val using 1
          ext e
          simp only [Set.mem_preimage, Set.mem_singleton_iff, mem_graph_iff]
          constructor
          · intro h
            refine ⟨e.2, ?_⟩
            rw [← h]
            ring
          · rintro ⟨_, h⟩
            rw [h]
            ring
      continuous_invFun := by
        apply Continuous.subtype_mk
        apply continuous_generateFrom_iff.mpr
        rintro S ⟨O', g, hP'', rfl⟩
        have hU : ∀ c : ℂ, IsOpen {y : O | (y : X) ∈ O ∩ O' ∧ f y + c = g y} := by
          intro c
          have hOO' : IsOpen (O ∩ O') := hO.inter (hopen _ _ hP'')
          have h1 : P (O ∩ O') (fun y => f y + c) :=
            hmono _ _ _ (hadd _ _ c hP) hOO' Set.inter_subset_left
          have h2 : P (O ∩ O') g := hmono _ _ _ hP'' hOO' Set.inter_subset_right
          exact (heq _ _ _ h1 h2).preimage continuous_subtype_val
        have : (fun p : O × ℂ => Etale.mk P p.1.1 (f p.1.1 + p.2)) ⁻¹'
            ((fun y => Etale.mk P y (g y)) '' O') =
            ⋃ c : ℂ, {y : O | (y : X) ∈ O ∩ O' ∧ f y + c = g y} ×ˢ {c} := by
          ext ⟨y, c⟩
          simp only [Set.mem_preimage, mem_graph_iff, Etale.proj_mk, Etale.val_mk, Set.mem_iUnion,
            Set.mem_prod, Set.mem_setOf_eq, Set.mem_singleton_iff]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨c, ⟨⟨y.2, h1⟩, h2⟩, rfl⟩
          · rintro ⟨c', ⟨⟨_, h1⟩, h2⟩, rfl⟩
            exact ⟨h1, h2⟩
        show IsOpen ((fun p : O × ℂ => Etale.mk P p.1.1 (f p.1.1 + p.2)) ⁻¹'
            ((fun y => Etale.mk P y (g y)) '' O'))
        rw [this]
        exact isOpen_iUnion fun c => (hU c).prod (isOpen_discrete _) }
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage (I := ℂ)
    ⟨inferInstance, O, hxO, hO, hO.preimage hproj, H, fun e => rfl⟩
