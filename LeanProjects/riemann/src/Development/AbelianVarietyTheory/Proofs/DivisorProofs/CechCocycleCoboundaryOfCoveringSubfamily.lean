import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.CechCobGlue

theorem resG_comp {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)) :
    resG X h₂ (resG X h₁ a) = resG X (h₂.trans h₁) a := by
  change ((X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom) a = _
  rw [← Functor.map_comp]
  rfl

theorem cocycle_coboundary_of_subcover : ∀ (Y : Scheme.{0}) (J : Type) (W : J → Y.Opens) (κ : Type) (σ : κ → J), ⨆ k, W (σ k) = ⊤ → ∀ (E : ∀ i i' : J, Γ(Y, W i ⊓ W i')), (∀ i i' i'', resG Y (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (E i i') + resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (E i' i'') = resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (E i i'')) → ∀ (h' : ∀ k, Γ(Y, W (σ k))), (∀ k k', E (σ k) (σ k') = resG Y inf_le_left (h' k) - resG Y inf_le_right (h' k')) → ∃ h : ∀ i, Γ(Y, W i), ∀ i i', E i i' = resG Y inf_le_left (h i) - resG Y inf_le_right (h i') := by
  intro Y J W κ σ hcov E hE h' hh'
  have hcovi : ∀ i, W i ≤ ⨆ k, (W i ⊓ W (σ k)) := by
    intro i x hx
    have hx' : x ∈ (⨆ k, W (σ k)) := by rw [hcov]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx, hk⟩
  let f : ∀ i k, Γ(Y, W i ⊓ W (σ k)) := fun i k => E i (σ k) + resG Y inf_le_right (h' k)
  have hf : ∀ i k k', resG Y (inf_le_left : (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W i ⊓ W (σ k)) (f i k)
      = resG Y (inf_le_right : (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W i ⊓ W (σ k')) (f i k') := by
    intro i k k'
    have hPT : (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W i ⊓ W (σ k) ⊓ W (σ k') :=
      le_inf inf_le_left (inf_le_right.trans inf_le_right)
    have e1 := congrArg (resG Y hPT) (hE i (σ k) (σ k'))
    have e2 := congrArg (resG Y (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      (W i ⊓ W (σ k)) ⊓ (W i ⊓ W (σ k')) ≤ W (σ k) ⊓ W (σ k'))) (hh' k k')
    simp only [map_add, map_sub, resG_comp] at e1 e2
    simp only [f, map_add, resG_comp]
    linear_combination e1 - e2
  have hg : ∀ i, ∃ s : Γ(Y, W i), ∀ k, resG Y (inf_le_left : W i ⊓ W (σ k) ≤ W i) s = f i k := by
    intro i
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun k => W i ⊓ W (σ k)) (W i)
      (fun k => homOfLE (inf_le_left : W i ⊓ W (σ k) ≤ W i)) (hcovi i) (fun k => f i k)
      (fun k k' => hf i k k')
    exact ⟨s, hs⟩
  choose h hh using hg
  refine ⟨h, fun i i' => ?_⟩
  have hcov2 : W i ⊓ W i' ≤ ⨆ k, (W i ⊓ W i' ⊓ W (σ k)) := by
    intro x hx
    have hx' : x ∈ (⨆ k, W (σ k)) := by rw [hcov]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx, hk⟩
  apply Y.sheaf.eq_of_locally_eq' (fun k => W i ⊓ W i' ⊓ W (σ k)) (W i ⊓ W i')
    (fun k => homOfLE (inf_le_left : W i ⊓ W i' ⊓ W (σ k) ≤ W i ⊓ W i')) hcov2
  intro k
  show resG Y inf_le_left (E i i') = resG Y inf_le_left (resG Y inf_le_left (h i) - resG Y inf_le_right (h i'))
  have A := congrArg (resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
    W i ⊓ W i' ⊓ W (σ k) ≤ W i ⊓ W (σ k))) (hh i k)
  have B := congrArg (resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
    W i ⊓ W i' ⊓ W (σ k) ≤ W i' ⊓ W (σ k))) (hh i' k)
  have C := hE i i' (σ k)
  simp only [f, map_add, resG_comp] at A B
  simp only [map_sub, resG_comp]
  linear_combination C - A + B

end GlobalTheory.CechCobGlue
