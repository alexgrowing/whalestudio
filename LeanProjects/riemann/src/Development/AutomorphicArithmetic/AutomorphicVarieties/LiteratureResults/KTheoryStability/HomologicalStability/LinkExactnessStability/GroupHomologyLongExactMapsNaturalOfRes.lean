import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PermRepSingle

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab

namespace GlobalTheory.HomStab

private theorem groupHomology_chainsMap_comp_comm_of_compat (k G H : Type) [CommRing k] [Group G] [Group H]
    (φ : H →* G) (A B : Rep k H) (C D : Rep k G)
    (f : A ⟶ B) (g : C ⟶ D) (u : A ⟶ Rep.res φ C) (v : B ⟶ Rep.res φ D)
    (h : ∀ a, v.hom (f.hom a) = g.hom (u.hom a)) :
    groupHomology.chainsMap (MonoidHom.id H) f ≫ groupHomology.chainsMap φ v =
      groupHomology.chainsMap φ u ≫ groupHomology.chainsMap (MonoidHom.id G) g := by
  ext n : 1
  apply groupHomology.inhomogeneousChains.ext
  intro x
  ext a : 2
  simp [groupHomology.chainsMap_f_single, h]

theorem groupHomology_δ_natural_changeGroup : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G) (X : ShortComplex (Rep k H)) (Y : ShortComplex (Rep k G)) (hX : X.ShortExact) (hY : Y.ShortExact) (u₁ : X.X₁ ⟶ Rep.res φ Y.X₁) (u₂ : X.X₂ ⟶ Rep.res φ Y.X₂) (u₃ : X.X₃ ⟶ Rep.res φ Y.X₃), (∀ a, u₂.hom (X.f.hom a) = Y.f.hom (u₁.hom a)) → (∀ a, u₃.hom (X.g.hom a) = Y.g.hom (u₂.hom a)) → ∀ n : ℕ, groupHomology.δ hX (n + 1) n rfl ≫ groupHomology.map φ u₁ n = groupHomology.map φ u₃ (n + 1) ≫ groupHomology.δ hY (n + 1) n rfl ∧ hMap X.f n ≫ groupHomology.map φ u₂ n = groupHomology.map φ u₁ n ≫ hMap Y.f n ∧ hMap X.g n ≫ groupHomology.map φ u₃ n = groupHomology.map φ u₂ n ≫ hMap Y.g n := by
  intro k G H _ _ _ φ X Y hX hY u₁ u₂ u₃ h₁ h₂ n
  have c₁ := groupHomology_chainsMap_comp_comm_of_compat k G H φ _ _ _ _ X.f Y.f u₁ u₂ h₁
  have c₂ := groupHomology_chainsMap_comp_comm_of_compat k G H φ _ _ _ _ X.g Y.g u₂ u₃ h₂
  have d₁ := congrArg (fun f => HomologicalComplex.homologyMap f n) c₁
  have d₂ := congrArg (fun f => HomologicalComplex.homologyMap f n) c₂
  simp only [HomologicalComplex.homologyMap_comp] at d₁ d₂
  refine ⟨?_, d₁, d₂⟩
  let Φ : X.map (groupHomology.chainsFunctor k H) ⟶ Y.map (groupHomology.chainsFunctor k G) :=
    { τ₁ := groupHomology.chainsMap φ u₁
      τ₂ := groupHomology.chainsMap φ u₂
      τ₃ := groupHomology.chainsMap φ u₃
      comm₁₂ := c₁.symm
      comm₂₃ := c₂.symm }
  exact HomologicalComplex.HomologySequence.δ_naturality Φ
    (groupHomology.map_chainsFunctor_shortExact hX) (groupHomology.map_chainsFunctor_shortExact hY)
    (n + 1) n rfl

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab
theorem _root_.GlobalTheory.T.groupHomology_longExact_maps_natural_of_res : ∀ (k G H : Type) [CommRing k] [Group G] [Group H] (φ : H →* G) (X : ShortComplex (Rep k H)) (Y : ShortComplex (Rep k G)) (hX : X.ShortExact) (hY : Y.ShortExact) (u₁ : X.X₁ ⟶ Rep.res φ Y.X₁) (u₂ : X.X₂ ⟶ Rep.res φ Y.X₂) (u₃ : X.X₃ ⟶ Rep.res φ Y.X₃), (∀ a, u₂.hom (X.f.hom a) = Y.f.hom (u₁.hom a)) → (∀ a, u₃.hom (X.g.hom a) = Y.g.hom (u₂.hom a)) → ∀ n : ℕ, groupHomology.δ hX (n + 1) n rfl ≫ groupHomology.map φ u₁ n = groupHomology.map φ u₃ (n + 1) ≫ groupHomology.δ hY (n + 1) n rfl ∧ hMap X.f n ≫ groupHomology.map φ u₂ n = groupHomology.map φ u₁ n ≫ hMap Y.f n ∧ hMap X.g n ≫ groupHomology.map φ u₃ n = groupHomology.map φ u₂ n ≫ hMap Y.g n := by
  first
  | exact @GlobalTheory.HomStab.groupHomology_δ_natural_changeGroup
end
