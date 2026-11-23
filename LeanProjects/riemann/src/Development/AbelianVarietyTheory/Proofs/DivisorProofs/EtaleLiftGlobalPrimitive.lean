import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenGraph
open GlobalTheory.PrimLift

namespace GlobalTheory

theorem exists_global_of_isCoveringMap_etale :
    ∀ {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (P : Set X → (X → ℂ) → Prop),
    (∀ O f, P O f → IsOpen O) →
    (∀ O O' f, P O f → IsOpen O' → O' ⊆ O → P O' f) →
    (∀ O f (c : ℂ), P O f → P O (fun y => f y + c)) →
    (∀ x, ∃ O f, x ∈ O ∧ P O f) →
    IsCoveringMap (GlobalTheory.PrimLift.Etale.proj P) →
    ∃ F : X → ℂ, ∀ x, ∃ O f, x ∈ O ∧ P O f ∧ Set.EqOn F f O := by
  intro X _ _ _ P hopen hmono hadd hcov hproj
  have x₀ : X := Classical.arbitrary X
  obtain ⟨s, ⟨-, hs⟩, -⟩ :=
    hproj.existsUnique_continuousMap_lifts (ContinuousMap.id X) x₀ (Etale.mk P x₀ 0) rfl
  have hsx : ∀ y, Etale.proj P (s y) = y := fun y => congrFun hs y
  refine ⟨fun x => (s x).val, fun x => ?_⟩
  obtain ⟨O, f, hxO, hP⟩ := hcov x
  set c : ℂ := (s x).val - f x with hc
  have hPc := hadd O f c hP
  have hG : IsOpen ((fun y => Etale.mk P y (f y + c)) '' O) := Etale.isOpen_graph hPc
  have hW : IsOpen (s ⁻¹' ((fun y => Etale.mk P y (f y + c)) '' O)) := hG.preimage s.continuous
  refine ⟨O ∩ s ⁻¹' ((fun y => Etale.mk P y (f y + c)) '' O), fun y => f y + c, ⟨hxO, ?_⟩,
    hmono _ _ _ hPc ((hopen O f hP).inter hW) Set.inter_subset_left, ?_⟩
  · refine ⟨x, hxO, ?_⟩
    have e1 : f x + c = (s x).val := by rw [hc]; ring
    show Etale.mk P x (f x + c) = s x
    rw [e1]
    conv_rhs => rw [← Etale.mk_proj_val (s x)]
    rw [hsx x]
  · rintro y ⟨-, z, -, hz⟩
    have hzy : z = y := by
      have h1 := congrArg (Etale.proj P) hz
      rwa [Etale.proj_mk, hsx] at h1
    subst hzy
    have h2 := congrArg Etale.val hz
    rw [Etale.val_mk] at h2
    exact h2.symm

end GlobalTheory
