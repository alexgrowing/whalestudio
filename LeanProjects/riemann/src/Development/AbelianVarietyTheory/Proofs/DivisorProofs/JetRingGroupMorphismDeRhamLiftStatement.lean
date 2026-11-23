import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingGroupMorphismDeRhamLift
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_ring_group_morphism_de_rham_lift : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
      (∃ N' : Submodule J.B (Crys J.κ (spMap J.π) X.A), IsCompl (Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}) N') ∧
      ∀ y : HdR X.A, y ∈ Fil X.A ↔ ∃ d ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, (GlobalTheory.Published.GrothendieckMessing.crysRedMor J.κ rfl X.A).Corr d y := by
  first | exact @GlobalTheory.LatJet.jetFil_summand_reduces | exact GlobalTheory.LatJet.jetFil_summand_reduces | (intros; apply GlobalTheory.LatJet.jetFil_summand_reduces <;> assumption)
