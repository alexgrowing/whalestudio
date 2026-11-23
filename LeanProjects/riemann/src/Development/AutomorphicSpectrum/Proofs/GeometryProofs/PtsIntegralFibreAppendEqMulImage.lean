import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.GenericFibreIntersectionPullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystemStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open SheetDecomposition.PF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.ptsIntegral_fibre_append_eq_mul_image : ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ρ : K → Type) [∀ k, Fintype (ρ k)] (K' : Type) [Fintype K'] (ρ' : K' → Type) [∀ k, Fintype (ρ' k)] (κ : K → K') (v : (Σ k, ρ k) → (Σ k', ρ' k')) (P' : Ideal (MRing ρ')) (d r : ℕ) (G : GenFibre v P') (Jf : IFamily G.Φ (fibreIdx ρ' κ)) (L : Fin d → HermLine ρ) (L' : Fin d → HermLine ρ') (N : Fin r → HermLine ρ'), IsBlockMap κ v → IsArithVar P' (d + 1 + r) → IsArithVar (imageZ v P') (d + 1) → IsFieldIntersection Jf → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) → ptsIntegral (e := d + r) P' (fun i z => Real.log ((Fin.append L' N i).h z)) (fun _ => 1) = (Jf (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * ptsIntegral (e := d) (imageZ v P') (fun i z => Real.log ((L i).h z)) (fun _ => 1) := by
  intro II hII K _ ρ _ K' _ ρ' _ κ v P' d r G Jf L L' N hv hP' hP hJ hL hLL' hN
  have hA : IsArithVar P' (d + r + 1) := by rwa [Nat.add_right_comm] at hP'
  have hs : ∀ j, IsSmoothHerm (Fin.append L' N j) := fun j => by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [Fin.append_left]
      exact GroundTheory.Heights₂.Heights.Inter.IsPullHerm.isSmoothHerm hv (hLL' j) (hL j)
    · rw [Fin.append_right]
      exact hN j
  have h := GlobalTheory.T.projection_formula_of_arith_system ⟨II, hII⟩ II hII.1 K ρ K' ρ' κ v P' (d + 1) r G Jf
    (Fin.snoc (α := fun _ => HermLine ρ) L (cst ρ)) (Fin.snoc (α := fun _ => HermLine ρ') L' (cst ρ')) N hv hP' hP hJ
    (LevelTowerAlt.snoc_cst_smooth L hL)
    (fun j => by
      refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [Fin.snoc_last, Fin.snoc_last]
        refine ⟨?_, fun z => rfl⟩
        show (0 : K' → ℤ) = pullDeg κ 0
        funext k
        by_cases hk : ∃ a, κ a = k
        · obtain ⟨a, rfl⟩ := hk
          exact (hv.1.extend_apply (0 : K → ℤ) (0 : K' → ℤ) a).symm
        · exact (Function.extend_apply' (0 : K → ℤ) (0 : K' → ℤ) _ hk).symm
      · simpa using hLL' j)
    hN
  rw [LevelTowerAlt.ii_cst_int hII.1 hP L hL, ← position_eq, ii_cast hII.1 _ hA _ (LevelTowerAlt.snoc_cst_smooth _ hs), LevelTowerAlt.ii_cst_int hII.1 hA _ hs,
    mul_neg, neg_inj] at h
  exact h
