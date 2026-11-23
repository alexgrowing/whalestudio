import Formalism.SharpRestriction.CuspSpanNormBounds.GramProductBounds

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.GramProductBounds

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem one_le_prod_max {ι : Type} (s : Finset ι) (f : ι → ℝ) : 1 ≤ ∏ l ∈ s, max 1 (f l) := by
  calc (1 : ℝ) = ∏ _l ∈ s, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun _ _ => le_max_left _ _)

theorem le_prod_max {ι : Type} [DecidableEq ι] {s : Finset ι} {a : ι} (ha : a ∈ s) (f : ι → ℝ) :
    max 1 (f a) ≤ ∏ l ∈ s, max 1 (f l) := by
  rw [← Finset.mul_prod_erase s _ ha]
  exact le_mul_of_one_le_right (le_trans zero_le_one (le_max_left _ _)) (one_le_prod_max _ _)

section Bound

variable (D : D7) (u u' : D.what₂.Word)

theorem absDl_nonneg (Z : GramM D) (l : ℕ) (τ : D.what₂.Tau) : 0 ≤ Cnt.absDl D Z l τ := by
  unfold Cnt.absDl absReal
  refine mul_nonneg (norm_nonneg _) (Real.rpow_nonneg ?_ _)
  unfold Formalism.BasicNotions.Host.rdE
  exact Real.rpow_nonneg (abs_nonneg _) _

theorem one_le_sizeZ (b C : ℝ) (Z : GramM D) : 1 ≤ Cnt.sizeZ D b C Z := by
  unfold Cnt.sizeZ
  calc (1 : ℝ) = ∏ _τ : D.what₂.Tau, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun _ _ => one_le_prod_max _ _)

end Bound

section Fam

def LatticeIdentitySignsGeneric : Prop :=
  ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ),
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' →
    G0 Λ (gS D) (lf D F0) F' = localGramProduct D u u' (ZhatL (lf D F0) F') ∧
    (∀ τ, 0 ≤ Cnt.Gz D (Tu D u) (Tu D u') (ZhatL (lf D F0) F') τ) ∧ 1 ≤ G0 Λ (gS D) (lf D F0) F'

end Fam

end Formalism.MainNotions.GramProductBounds

end
