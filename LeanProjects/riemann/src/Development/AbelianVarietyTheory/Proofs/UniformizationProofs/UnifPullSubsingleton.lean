import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.UniformizationBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullDegEquivApply
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsoEqOfMapsAlongSection
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedIsoRespectsCubeAndSymmetry
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifPullCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification (CarriesAt PullIdent)
open GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBaseChange (CarriesFam GrpPull RigPull UnifPull GenericInPsiLocus UnifBaseChange)
open GlobalTheory.PullDegCompare
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

section Bundle

end Bundle

section Main

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']

omit [IsDomain R] [IsDomain R'] in
theorem isGrpPullback_of_bc (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (hbc : IsMonHom bc.hom) :
    IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
  ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl

def toGrpPull (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (hbc : IsMonHom bc.hom) : GrpPull φ G G' where
  F := bc.hom.left ≫ pullback.fst G.hom (specOf φ)
  cart := (isGrpPullback_of_bc bc hbc).1
  F_one := PolBaseChange.eSec_comm (isGrpPullback_of_bc bc hbc)
  F_mul := (isGrpPullback_iff (isGrpPullback_of_bc bc hbc).1).1 (isGrpPullback_of_bc bc hbc)

omit [IsDomain R] [IsDomain R'] in
theorem exists_toGrpPull_eq (p : GrpPull φ G G') :
    ∃ (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (hbc : IsMonHom bc.hom), toGrpPull bc hbc = p := by
  obtain ⟨e, me, he⟩ := grpPullback_iso ((isGrpPullback_iff p.cart).2 p.F_mul)
    (isGrpPullback_pullback G (specOf φ))
  obtain ⟨F, cart, F₁, Fm⟩ := p
  dsimp only at he
  subst he
  exact ⟨e, me, rfl⟩

def grpPullEquiv (φ : R →+* R') (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] :
    {bc : G' ≅ (Over.pullback (specOf φ)).obj G // IsMonHom bc.hom} ≃ GrpPull φ G G' :=
  Equiv.ofBijective (fun b => toGrpPull b.1 b.2)
    ⟨fun b b' H => Subtype.ext (Iso.ext (Over.OverMorphism.ext (pullback.hom_ext (congrArg GrpPull.F H)
      ((Over.w b.1.hom).trans (Over.w b'.1.hom).symm)))),
     fun p => let ⟨bc, hbc, e⟩ := exists_toGrpPull_eq p; ⟨⟨bc, hbc⟩, e⟩⟩

variable [IsCommMonObj G] [IsCommMonObj G']

def rigPullEquiv (p : GrpPull φ G G') (L : RigLB G) (L' : RigLB G') :
    {w : LB.Iso L'.L (L.L.pull p.F) // w.IsGen ∧
      LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig
        (rigPullOf p.F (specOf φ) p.F_one L.L L.rig)} ≃ RigPull p L L' where
  toFun w := ⟨w.1, w.2.1, (rig_iff _ _ p.F_one _ _ w.1 L.rig L'.rig).1 w.2.2⟩
  invFun r := ⟨r.w, r.w_gen, (rig_iff _ _ p.F_one _ _ r.w L.rig L'.rig).2 r.w_rig⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {I : Ideal R} {I' : Ideal R'}

variable {D : DegData R I} {D' : DegData R' I'} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))}

end Main

end GlobalTheory.UnifPullCompare
