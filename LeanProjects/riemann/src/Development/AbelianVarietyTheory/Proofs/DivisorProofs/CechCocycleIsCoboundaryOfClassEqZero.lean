import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpOfIsCocycle

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CechCmp

theorem IsCocycle.res_on {Z : Scheme.{0}} {J : Type} {W : J → Z.Opens}
    {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')} (hc : IsCocycle W c) {U : Z.Opens} {i j k : J}
    (hi : U ≤ W i) (hj : U ≤ W j) (hk : U ≤ W k) :
    resG Z (le_inf hi hj) (c i j) + resG Z (le_inf hj hk) (c j k) =
      resG Z (le_inf hi hk) (c i k) := by
  have e := congrArg (resG Z (le_inf (le_inf hi hj) hk)) (hc i j k)
  simp only [map_add, resG_resG'] at e
  exact e

theorem exists_coboundary_of_cmp_eq_zero (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R)
    (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (hWa : ∀ i, IsAffineOpen (W i))
    (hWb : ∀ i i', IsAffineOpen (W i ⊓ W i')) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i'))
    (hc : IsCocycle W c) (h0 : cmp s W hW c = 0) :
    ∃ h : ∀ i : J, Γ(Z, W i), ∀ i i',
      c i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') := by
  have h1 := restrict_cmp s W hW hc
  rw [h0, map_zero] at h1
  obtain ⟨g, hg⟩ := CatCoh.H1.mk_eq_zero.1 h1.symm
  let g' : ∀ V : Bas W, Γ(Z, V.1.1) := fun V ↦ g (Opposite.op V)
  have key : ∀ (V V' : Bas W) (h : V'.1.1 ≤ V.1.1),
      g' V' - resG Z h (g' V) =
        resG Z (le_inf (h.trans (le_idx V)) (le_idx V')) (c (idx V) (idx V')) := by
    intro V V' h
    exact congrFun (congrFun (congrFun hg (Opposite.op V)) (Opposite.op V'))
      (homOfLE (show V' ≤ V from h)).op
  let Ω : J → Bas W := fun i ↦ ⟨⟨W i, hWa i⟩, i, le_rfl⟩
  have hΩ : ∀ i, W i ≤ W (idx (Ω i)) := fun i ↦ le_idx (Ω i)
  let g₁ : ∀ i, Γ(Z, W i) := fun i ↦ g' (Ω i)
  refine ⟨fun i ↦ resG Z (le_inf le_rfl (hΩ i)) (c i (idx (Ω i))) - g₁ i, fun i i' ↦ ?_⟩
  let Ω₂ : Bas W := ⟨⟨W i ⊓ W i', hWb i i'⟩, i, inf_le_left⟩
  have hd : W i ⊓ W i' ≤ W (idx Ω₂) := le_idx Ω₂
  let g₂ : Γ(Z, W i ⊓ W i') := g' Ω₂
  have k1 : g₂ - resG Z inf_le_left (g₁ i) =
      resG Z (le_inf (inf_le_left.trans (hΩ i)) hd) (c (idx (Ω i)) (idx Ω₂)) :=
    key (Ω i) Ω₂ inf_le_left
  have k2 : g₂ - resG Z inf_le_right (g₁ i') =
      resG Z (le_inf (inf_le_right.trans (hΩ i')) hd) (c (idx (Ω i')) (idx Ω₂)) :=
    key (Ω i') Ω₂ inf_le_right
  have e1 := hc.res_on (inf_le_left : W i ⊓ W i' ≤ _) (inf_le_left.trans (hΩ i)) hd
  have e2 := hc.res_on (inf_le_right : W i ⊓ W i' ≤ _) (inf_le_right.trans (hΩ i')) hd
  have e3 := hc.res_on (inf_le_left : W i ⊓ W i' ≤ _) inf_le_right hd
  have e4 : resG Z (le_inf (inf_le_left : W i ⊓ W i' ≤ _) inf_le_right) (c i i') = c i i' := by
    have : (homOfLE (le_inf (inf_le_left : W i ⊓ W i' ≤ _) inf_le_right)).op = 𝟙 _ := rfl
    simp only [resG, this, CategoryTheory.Functor.map_id]
    rfl
  rw [e4] at e3
  simp only [map_sub, resG_resG']
  linear_combination e3 - e1 + e2 - k1 + k2

end GlobalTheory.CechCmp
