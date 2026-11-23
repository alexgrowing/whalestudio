import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinsetRepresentatives
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.VGeIffExtended
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymFrameClause
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.UpExt
open GlobalTheory.FieldBaseChange
variable {R : Type} [CommRing R] [IsDomain R]

def baseK (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F]
    [IsScalarTower (FractionRing R) E F] : TFK (R := R) F ⟶ TFK (R := R) E :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap E F))) (by
    show Spec.map (CommRingCat.ofHom (algebraMap E F)) ≫ jFK (R := R) E = jFK (R := R) F
    rw [jFK, jFK, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])

variable (A : PolAV (Sp (FractionRing R)))

def secBase (F : Type) [Field F] [Algebra (FractionRing R) F] :
    (TFK (R := R) F ⊗ A.A).left ⟶ Spec (CommRingCat.of F) := (fst (TFK (R := R) F) A.A).left

abbrev SecF (F : Type) [Field F] [Algebra (FractionRing R) F] (N : ℕ) : Type :=
  SecOver (secBase A F) (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) F) A.A).left) (fun _ => (N : ℤ)))

variable (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F]
    [IsScalarTower (FractionRing R) E F]

def secMap : TFK (R := R) F ⊗ A.A ⟶ TFK (R := R) E ⊗ A.A := lift (fst _ _ ≫ baseK E F) (snd _ _)

theorem secMap_snd : secMap A E F ≫ snd _ _ = snd _ _ := lift_snd _ _

theorem secMap_fst : secMap A E F ≫ fst _ _ = fst _ _ ≫ baseK E F := lift_fst _ _

theorem secMap_base : (secMap A E F).left ≫ secBase A E =
    secBase A F ≫ Spec.map (CommRingCat.ofHom (algebraMap E F)) :=
  congrArg (fun q => q.left) (secMap_fst A E F)

def secPull (N : ℕ) : SecF A E N →ₛₗ[algebraMap E F] SecF A F N :=
  pullOver A.L _ (secMap_base A E F) (fun _ => (congrArg (fun q => q.left) (secMap_snd A E F)).symm)

theorem isPullback_secMap : IsPullback (secMap A E F).left (secBase A F) (secBase A E)
    (Spec.map (CommRingCat.ofHom (algebraMap E F))) := by
  have h₁ : IsPullback (snd (TFK (R := R) E) A.A).left (secBase A E)
      A.A.hom (TFK (R := R) E).hom := (IsPullback.of_hasPullback _ _).flip
  have h₂ : IsPullback (snd (TFK (R := R) F) A.A).left (secBase A F)
      A.A.hom (TFK (R := R) F).hom := (IsPullback.of_hasPullback _ _).flip
  refine IsPullback.of_right ?_ (secMap_base A E F) h₁
  have e₁ : (secMap A E F).left ≫ (snd (TFK (R := R) E) A.A).left =
      (snd (TFK (R := R) F) A.A).left := congrArg (fun q => q.left) (secMap_snd A E F)
  have e₂ : Spec.map (CommRingCat.ofHom (algebraMap E F)) ≫
      (TFK (R := R) E).hom = (TFK (R := R) F).hom := Over.w (baseK (R := R) E F)
  rw [e₁, e₂]
  exact h₂

instance noeth : TopologicalSpace.NoetherianSpace (TFK (R := R) E ⊗ A.A).left := by
  have := A.isAb.proper
  have : IsProper (secBase A E) := inferInstanceAs (IsProper (pullback.fst _ _))
  have : IsLocallyNoetherian (TFK (R := R) E ⊗ A.A).left := LocallyOfFiniteType.isLocallyNoetherian (secBase A E)
  have : CompactSpace (TFK (R := R) E ⊗ A.A).left := QuasiCompact.compactSpace_of_compactSpace (secBase A E)
  have : IsNoetherian (TFK (R := R) E ⊗ A.A).left := {}
  infer_instance

theorem isExtension_secPull (N : ℕ) : IsExtension (secPull A E F N) :=
  isExtension_pullOver (isPullback_secMap A E F) A.isLB _ _

end GlobalTheory.Mum.UpExt
