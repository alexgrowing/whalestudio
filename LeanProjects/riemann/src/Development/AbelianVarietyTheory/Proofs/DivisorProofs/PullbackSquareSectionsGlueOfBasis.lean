import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Glues
open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option autoImplicit false

namespace GlobalTheory.PinchLift

theorem app_res {X Y : Scheme.{0}} (f : Y ⟶ X) {W W' : X.Opens} (h : W' ≤ W) (s : Γ(X, W)) :
    (f.app W').hom ((X.presheaf.map (homOfLE h).op).hom s) =
      (Y.presheaf.map ((Opens.map f.base).map (homOfLE h)).op).hom ((f.app W).hom s) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.naturality]
  rfl

theorem compat_res {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z)
    {W W' : X.Opens} (h : W' ≤ W) (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W))
    (hab : (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
      (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b) :
    (i'.appLE (p ⁻¹ᵁ W') (i' ⁻¹ᵁ (p ⁻¹ᵁ W') ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W')) inf_le_left).hom
        ((X'.presheaf.map ((Opens.map p.base).map (homOfLE h)).op).hom a) =
      (p'.appLE (i ⁻¹ᵁ W') (i' ⁻¹ᵁ (p ⁻¹ᵁ W') ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W')) inf_le_right).hom
        ((Z.presheaf.map ((Opens.map i.base).map (homOfLE h)).op).hom b) := by
  have hV : i' ⁻¹ᵁ (p ⁻¹ᵁ W') ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W') ≤ i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W) :=
    fun x hx => ⟨h hx.1, h hx.2⟩
  have := congrArg (Z'.presheaf.map (homOfLE hV).op).hom hab
  simp only [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE] at this ⊢
  exact this

theorem unique_of_basis {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z)
    (B : Set X.Opens) (hbasis : ∀ (W : X.Opens) (x : X), x ∈ W → ∃ W' ∈ B, x ∈ W' ∧ W' ≤ W)
    (hB : ∀ W ∈ B, ∀ (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W)),
      (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
        (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b →
      ∃! s : Γ(X, W), (p.app W).hom s = a ∧ (i.app W).hom s = b)
    (W : X.Opens) (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W))
    (hab : (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
      (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b)
    (s s' : Γ(X, W)) (hs : (p.app W).hom s = a ∧ (i.app W).hom s = b)
    (hs' : (p.app W).hom s' = a ∧ (i.app W).hom s' = b) : s = s' := by
  have hcover : W ≤ ⨆ j : {W' : X.Opens // W' ∈ B ∧ W' ≤ W}, j.1 := by
    intro x hx
    obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W x hx
    exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
  refine X.sheaf.eq_of_locally_eq' (fun j : {W' : X.Opens // W' ∈ B ∧ W' ≤ W} => j.1) W
    (fun j => homOfLE j.2.2) hcover s s' fun j => ?_
  have hc := compat_res p i i' p' j.2.2 a b hab
  refine (hB j.1 j.2.1 _ _ hc).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · exact (app_res p j.2.2 s).trans (congrArg _ hs.1)
  · exact (app_res i j.2.2 s).trans (congrArg _ hs.2)
  · exact (app_res p j.2.2 s').trans (congrArg _ hs'.1)
  · exact (app_res i j.2.2 s').trans (congrArg _ hs'.2)

theorem glues_of_basis : ∀ {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z)
    (B : Set X.Opens), (∀ (W : X.Opens) (x : X), x ∈ W → ∃ W' ∈ B, x ∈ W' ∧ W' ≤ W) →
    (∀ W ∈ B, ∀ (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W)),
      (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
        (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b →
      ∃! s : Γ(X, W), (p.app W).hom s = a ∧ (i.app W).hom s = b) → GlobalTheory.PinchLift.Glues p i i' p' := by
  intro X X' Z Z' p i i' p' B hbasis hB W a b hab
  let I := {W' : X.Opens // W' ∈ B ∧ W' ≤ W}
  have hcover : W ≤ ⨆ j : I, j.1 := by
    intro x hx
    obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W x hx
    exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
  choose t ht using fun j : I => (hB j.1 j.2.1 _ _ (compat_res p i i' p' j.2.2 a b hab)).exists
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun j : I => j.1) t := by
    intro j k
    have hjk : j.1 ⊓ k.1 ≤ W := inf_le_left.trans j.2.2
    refine unique_of_basis p i i' p' B hbasis hB (j.1 ⊓ k.1) _ _ (compat_res p i i' p' hjk a b hab) _ _
      ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · refine (app_res p inf_le_left (t j)).trans ?_
      rw [(ht j).1, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    · refine (app_res i inf_le_left (t j)).trans ?_
      rw [(ht j).2, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    · refine (app_res p inf_le_right (t k)).trans ?_
      rw [(ht k).1, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    · refine (app_res i inf_le_right (t k)).trans ?_
      rw [(ht k).2, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun j : I => j.1) W (fun j => homOfLE j.2.2)
    hcover t hcompat
  have key : (p.app W).hom s = a ∧ (i.app W).hom s = b := by
    constructor
    · have hcov' : p ⁻¹ᵁ W ≤ ⨆ j : I, p ⁻¹ᵁ j.1 := by
        intro x hx
        obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W (p.base x) hx
        exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
      refine X'.sheaf.eq_of_locally_eq' (fun j : I => p ⁻¹ᵁ j.1) (p ⁻¹ᵁ W)
        (fun j => (Opens.map p.base).map (homOfLE j.2.2)) hcov' _ _ fun j => ?_
      refine (app_res p j.2.2 s).symm.trans ?_
      rw [show (X.presheaf.map (homOfLE j.2.2).op).hom s = t j from hs j]
      exact (ht j).1
    · have hcov' : i ⁻¹ᵁ W ≤ ⨆ j : I, i ⁻¹ᵁ j.1 := by
        intro x hx
        obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W (i.base x) hx
        exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
      refine Z.sheaf.eq_of_locally_eq' (fun j : I => i ⁻¹ᵁ j.1) (i ⁻¹ᵁ W)
        (fun j => (Opens.map i.base).map (homOfLE j.2.2)) hcov' _ _ fun j => ?_
      refine (app_res i j.2.2 s).symm.trans ?_
      rw [show (X.presheaf.map (homOfLE j.2.2).op).hom s = t j from hs j]
      exact (ht j).2
  exact ⟨s, key, fun s' hs' => unique_of_basis p i i' p' B hbasis hB W a b hab s' s hs' key⟩

end GlobalTheory.PinchLift
