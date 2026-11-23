import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeLiftAlongNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingGroupMorphismDeRhamLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismCompatibleNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetRingMorphismUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowersStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetLiftMain

theorem exists_jetLift : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R : Type) [CommRing R] [IsDomain R] [CharZero R]
    [IsLocalRing R] (I : Type) [Fintype I] (n : ℕ) (J : JetRing R I n) (X : Obj F 𝔠 (Sp R))
    (N : I → Module.End R (HdR X.A)), admitted X N →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))),
    ∃ (X' : Obj F 𝔠 (Sp J.B)) (i : X.A.left ⟶ X'.A.left) (pull : X.IsPullBy X' (spMap J.π) i),
      liftFil J.κ pull.grp = Submodule.span J.B {d | ∃ x ∈ Fil X.A, IsJetElt J X N m x d} := by
  intro hGD hDR hDC F _ _ _ 𝔠 R _ _ _ _ I _ n J X N hN m
  have hs : J.π.comp (algebraMap R J.B) = RingHom.id R := RingHom.ext fun r ↦ JetRing.π_algebraMap J r
  obtain ⟨A, _, i, h, hA, hg⟩ := GlobalTheory.T.abelian_scheme_lift_along_split_surjection J.B R J.π (algebraMap R J.B) hs X.A _ X.ab X.dim
  obtain ⟨hsum, hred⟩ := GlobalTheory.T.jet_ring_group_morphism_de_rham_lift hGD hDR hDC F 𝔠 R I n J X N hN m
  exact GlobalTheory.T.group_object_lift_divided_powers hGD hDR hDC F 𝔠 J.B R (RingHom.ker J.π) J.κ J.nil J.π
    (fun r ↦ ⟨algebraMap R J.B r, JetRing.π_algebraMap J r⟩) rfl X A i h hA hg _ hsum hred
    (GlobalTheory.T.jet_ring_morphism_compatible_nilpotent hGD hDR hDC F 𝔠 R I n J X N hN m) (GlobalTheory.T.jet_ring_morphism_uniqueness hGD hDR hDC F 𝔠 R I n J X N hN m)

end GlobalTheory.JetLiftMain
