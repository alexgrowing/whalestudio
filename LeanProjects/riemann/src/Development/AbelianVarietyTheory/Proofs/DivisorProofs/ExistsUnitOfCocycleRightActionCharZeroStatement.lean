import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfCocycleRightActionCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert90_finite_rightAction_charZero_field : ∀ (K : Type) [Field K] [CharZero K] (Γ : Type) [Group Γ] [Finite Γ] (σ : Γ → K →+* K),
    (∀ γ δ a, σ (γ * δ) a = σ δ (σ γ a)) → ∀ (c : Γ → Kˣ),
    (∀ γ δ, (c (γ * δ) : K) = σ δ (c γ) * c δ) → (∀ γ, (∀ a, σ γ a = a) → c γ = 1) →
    ∃ f : Kˣ, ∀ γ, σ γ f = c γ * f := by
  first | exact @GlobalTheory.exists_unit_of_cocycle_rightAction_charZero | exact GlobalTheory.exists_unit_of_cocycle_rightAction_charZero | (intros; apply GlobalTheory.exists_unit_of_cocycle_rightAction_charZero <;> assumption)
