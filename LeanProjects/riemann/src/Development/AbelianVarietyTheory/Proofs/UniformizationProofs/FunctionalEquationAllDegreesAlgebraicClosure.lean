import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleSectionsTorusTorsionWeightSpacesStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFunctionalEquationSectionNonzeroClassStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecZeroOfPull
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem fe_all_degrees : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U =>
    D.TauBimult → U.FE (Kbar V) 1 → ∀ N : ℕ, 1 ≤ N → U.FE (Kbar V) N := by
  intro h1 h2 V _ _ _ hV D A G _ _ U hτ hFE
  have hsupp : ∀ N : ℕ, 1 ≤ N → ∃ β, U.Supp (Kbar V) N β := fun N hN => by
    obtain ⟨mu, hmu⟩ := (GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces h1 h2 V hV D A G U N hN).2.1 0
    exact ⟨_, hmu⟩
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact hFE
  | succ k hk ih =>
    exact GlobalTheory.UU.SchurConst.main h1 h2 V hV D A G U (k + 1) (by omega)
      (GlobalTheory.T.exists_functionalEquation_section_nonzero_class h1 h2 V hV D A G U hτ k hk hFE ih (hsupp 1 le_rfl) (hsupp k hk))

end GlobalTheory.UU
