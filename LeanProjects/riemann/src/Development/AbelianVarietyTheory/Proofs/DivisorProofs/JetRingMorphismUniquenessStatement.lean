import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismUniqueness
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
theorem _root_.GlobalTheory.T.jet_ring_morphism_uniqueness : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
      ∀ (c : 𝔠.elt) (φ : Crys J.κ (spMap J.π) X.A →ₗ[J.B] Crys J.κ (spMap J.π) X.A →ₗ[J.B] J.B),
        GlobalTheory.AbDual.IsCorrForm J.κ (spMap J.π) X.A X.A (X.P c) φ → ∀ a ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, ∀ b ∈ Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d}, φ a b = 0 := by
  first | exact @GlobalTheory.JetIsotropic.jetFil_isotropic | exact GlobalTheory.JetIsotropic.jetFil_isotropic | (intros; apply GlobalTheory.JetIsotropic.jetFil_isotropic <;> assumption)
