import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleCoboundaryOfCoveringSubfamily
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechCocycle_coboundary_of_coveringSubfamily : ∀ (Y : Scheme.{0}) (J : Type) (W : J → Y.Opens) (κ : Type) (σ : κ → J), ⨆ k, W (σ k) = ⊤ → ∀ (E : ∀ i i' : J, Γ(Y, W i ⊓ W i')), (∀ i i' i'', resG Y (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (E i i') + resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'') (E i' i'') = resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'') (E i i'')) → ∀ (h' : ∀ k, Γ(Y, W (σ k))), (∀ k k', E (σ k) (σ k') = resG Y inf_le_left (h' k) - resG Y inf_le_right (h' k')) → ∃ h : ∀ i, Γ(Y, W i), ∀ i i', E i i' = resG Y inf_le_left (h i) - resG Y inf_le_right (h i') := by
  first | exact @GlobalTheory.CechCobGlue.cocycle_coboundary_of_subcover | exact GlobalTheory.CechCobGlue.cocycle_coboundary_of_subcover | (intros; apply GlobalTheory.CechCobGlue.cocycle_coboundary_of_subcover <;> assumption)
