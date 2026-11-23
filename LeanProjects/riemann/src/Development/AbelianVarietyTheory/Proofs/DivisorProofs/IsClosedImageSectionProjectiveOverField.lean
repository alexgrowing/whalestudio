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
open GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem secClosed_closedPoint (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Sp K) (z : Sp K ⟶ X)
    (_hq : IsProjOver q) (hz : z ≫ q = 𝟙 _) :
    IsClosed ({z (IsLocalRing.closedPoint K)} : Set X) := by
  have : IsClosedImmersion z := isClosedImmersion_of_comp_eq_id q z hz
  have hc : IsClosed (Set.range z.base) := z.isClosedEmbedding.isClosed_range
  convert hc using 1
  ext x
  constructor
  · rintro rfl; exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    rw [Set.mem_singleton_iff, Subsingleton.elim y (IsLocalRing.closedPoint K)]

end GlobalTheory
