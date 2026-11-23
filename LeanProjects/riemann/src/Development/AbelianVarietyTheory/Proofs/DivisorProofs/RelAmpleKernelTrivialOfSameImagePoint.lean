import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarisationExtendsOverDvrGoodReduction
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.FibreTransfer

theorem exists_residueField_factor (S : Scheme.{0}) (p : S) (K : Type) [Field K] (x : Sp K ⟶ S)
    (hx : x (closedPoint K) = p) :
    ∃ θ : S.residueField p ⟶ CommRingCat.of K, Spec.map θ ≫ S.fromSpecResidueField p = x := by
  subst hx
  exact ⟨_, Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S x⟩

theorem isGrpPullback_fibre {S : Scheme.{0}} (G : Over S) [GrpObj G] (p : S) (K : Type) [Field K]
    (θ : S.residueField p ⟶ CommRingCat.of K) :
    IsGrpPullback ((Over.pullback (Spec.map θ ≫ S.fromSpecResidueField p)).obj G)
      ((Over.pullback (S.fromSpecResidueField p)).obj G) (Spec.map θ)
      (pullback.lift (pullback.fst G.hom _) (pullback.snd G.hom _ ≫ Spec.map θ)
        (by rw [pullback.condition, Category.assoc])) := by
  refine (isGrpPullback_pullback G (S.fromSpecResidueField p)).cancel
    ((isGrpPullback_pullback G (Spec.map θ ≫ S.fromSpecResidueField p)).congr rfl
      (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)

theorem lbIso_fibre {S : Scheme.{0}} (G : Over S) {L : LB G.left} (hL : L.IsLB) (p : S) (K : Type) [Field K]
    (θ : S.residueField p ⟶ CommRingCat.of K) :
    LBIso (L.pull (pullback.fst G.hom (Spec.map θ ≫ S.fromSpecResidueField p)))
      ((L.pull (pullback.fst G.hom (S.fromSpecResidueField p))).pull
        (pullback.lift (pullback.fst G.hom _) (pullback.snd G.hom _ ≫ Spec.map θ)
          (by rw [pullback.condition, Category.assoc]))) := by
  have e := GlobalTheory.FibreAmple.lbIso_pull_pull hL
    (pullback.lift (pullback.fst G.hom (Spec.map θ ≫ S.fromSpecResidueField p))
      (pullback.snd G.hom _ ≫ Spec.map θ) (by rw [pullback.condition, Category.assoc]))
    (pullback.fst G.hom (S.fromSpecResidueField p))
  rw [pullback.lift_fst] at e
  exact e.symm

end GlobalTheory.FibreTransfer

open GlobalTheory.FibreTransfer in

theorem GlobalTheory.FibreTransfer.relAmple_kTriv_of_same_point : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], QuasiCompact G.hom → IsSeparated G.hom → Smooth G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (K₁ : Type) [Field K₁] (z : Sp K₁ ⟶ S), IsProper (pullback.snd G.hom z) → RelAmple ((Over.pullback z).obj G) (L.pull (pullback.fst G.hom z)) → KTriv ((Over.pullback z).obj G) (L.pull (pullback.fst G.hom z)) → ∀ (K : Type) [Field K] (x : Sp K ⟶ S), x (closedPoint K) = z (closedPoint K₁) → RelAmple ((Over.pullback x).obj G) (L.pull (pullback.fst G.hom x)) ∧ KTriv ((Over.pullback x).obj G) (L.pull (pullback.fst G.hom x)) := by
  intro S G _ hqc hsep hsm L hL K₁ _ z hP hA hK K _ x hx
  generalize hy : z (closedPoint K₁) = y at hx
  obtain ⟨θ₁, hz⟩ := exists_residueField_factor S y K₁ z hy
  obtain ⟨θ, rfl⟩ := exists_residueField_factor S y K x hx
  clear hy
  subst hz
  haveI := hqc; haveI := hsep; haveI := hsm
  have hLy := pull_isLB hL (pullback.fst G.hom (S.fromSpecResidueField y))
  have i₁ : QuasiCompact ((Over.pullback (S.fromSpecResidueField y)).obj G).hom :=
    show QuasiCompact (pullback.snd G.hom _) from inferInstance
  have i₂ : IsSeparated ((Over.pullback (S.fromSpecResidueField y)).obj G).hom :=
    show IsSeparated (pullback.snd G.hom _) from inferInstance
  have i₃ : Smooth ((Over.pullback (S.fromSpecResidueField y)).obj G).hom :=
    show Smooth (pullback.snd G.hom _) from inferInstance
  have hd := GlobalTheory.AmpleDescent.proper_relAmple_kTriv_of_fieldExtension (S.residueField y) K₁ θ₁.hom
    ((Over.pullback (S.fromSpecResidueField y)).obj G) ((Over.pullback (Spec.map θ₁ ≫ S.fromSpecResidueField y)).obj G) _
    (isGrpPullback_fibre G y K₁ θ₁) _ _ hLy (pull_isLB hL _) (lbIso_fibre G hL y K₁ θ₁) hP hA hK
  have h₂ := isGrpPullback_fibre G y K θ
  obtain ⟨w, hw⟩ := lbIso_fibre G hL y K θ
  exact ⟨relAmple_pull h₂.1 hLy (pull_isLB hL _) ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) hd.2.1,
    kTriv_pull h₂ hLy (pull_isLB hL _) ((isGen_iff w).1 hw) hd.2.2⟩
