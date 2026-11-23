import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFirstCohomologyDimensionBoundCocycles
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_first_cohomology_dimension_bound_cocycles : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (s : Y ⟶ Sp K) (g : ℕ) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), Module.Finite K ((GlobalTheory.AbLaw.cechLB s (LB.triv Y) D).homology 1) → Module.finrank K ((GlobalTheory.AbLaw.cechLB s (LB.triv Y) D).homology 1) ≤ g → ∀ (e : Fin (g + 1) → ∀ i i' : κ, Γ(Y, D i ⊓ D i')), (∀ b i i' i'', resG Y (inf_le_left : D i ⊓ D i' ⊓ D i'' ≤ D i ⊓ D i') (e b i i') + resG Y (le_inf (inf_le_left.trans inf_le_right) inf_le_right : D i ⊓ D i' ⊓ D i'' ≤ D i' ⊓ D i'') (e b i' i'') = resG Y (le_inf (inf_le_left.trans inf_le_left) inf_le_right : D i ⊓ D i' ⊓ D i'' ≤ D i ⊓ D i'') (e b i i'')) → ∃ c : Fin (g + 1) → K, c ≠ 0 ∧ ∃ h : ∀ i, Γ(Y, D i), ∀ i i', ∑ b, (s.appLE ⊤ (D i ⊓ D i') le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c b)) * e b i i' = resG Y inf_le_left (h i) - resG Y inf_le_right (h i') := by
  first | exact @GlobalTheory.OrdCechDep.exists_comb_coboundary | exact GlobalTheory.OrdCechDep.exists_comb_coboundary | (intros; apply GlobalTheory.OrdCechDep.exists_comb_coboundary <;> assumption)
