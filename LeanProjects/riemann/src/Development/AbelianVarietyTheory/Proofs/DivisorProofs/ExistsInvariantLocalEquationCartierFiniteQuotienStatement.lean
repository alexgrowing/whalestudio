import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantLocalEquationCartierFiniteQuotien
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
theorem _root_.GlobalTheory.T.exists_invariant_localEquation_cartier_finiteQuotient : ∀ (F : Type) [Field F] [CharZero F] (X W : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp F)
    (Γ : Type) [Group Γ] [Finite Γ] (ρ : Γ →* Aut X) (q : X ⟶ W), IsAffineQuotient ρ q → ∀ (D : CartierDiv X),
    (∀ γ x g, D.IsEqn ((ρ γ).hom x) g → D.IsEqn x (fnAct ρ γ g)) →
    (∀ γ x g, X.fromSpecResidueField x ≫ (ρ γ).hom = X.fromSpecResidueField x → D.IsEqn x g →
      ZeroAt x (((fnAct ρ γ g * g⁻¹ : X.functionFieldˣ) : X.functionField) - 1)) →
    ∀ x : X, ∃ g : X.functionFieldˣ, (∀ γ, fnAct ρ γ g = g) ∧ D.IsEqn x g := by
  first | exact @GlobalTheory.InvEqn.exists_invariant_isEqn | exact GlobalTheory.InvEqn.exists_invariant_isEqn | (intros; apply GlobalTheory.InvEqn.exists_invariant_isEqn <;> assumption)
