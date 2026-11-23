import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GenericOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem isModel_of_isIso_restrict : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) (U : X.Opens),
    (U : Set X).Nonempty → IsIso (π ∣_ U) → ∃ φ : X.functionField →+* Y.functionField, IsModel π φ := by
  intro X Y _ _ π U hU hiso
  obtain ⟨h₁, h₂⟩ := GlobalTheory.Published.generic_of_isIso_restrict π U hU
  have e : closure ({genericPoint X} : Set X) = Set.univ := (genericPoint_spec X).def
  have hd : IsDominant π := ⟨dense_iff_closure_eq.mpr
    (Set.eq_univ_of_univ_subset (e ▸ closure_mono (Set.singleton_subset_iff.mpr ⟨_, h₁⟩)))⟩
  exact ⟨functionFieldMap π, h₁, h₂, fun y a => functionFieldMap_algebraMap π y a⟩

end GlobalTheory.HSNef
