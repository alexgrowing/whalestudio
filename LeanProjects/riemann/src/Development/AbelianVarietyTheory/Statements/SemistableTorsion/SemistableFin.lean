import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.SS

def IsModel {K W L : Type} [Field K] [CommRing W] [Field L] [Algebra K L] [Algebra W L]
    (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G] : Prop :=
  ∃ e : (Over.pullback (spMap (algebraMap W L))).obj G ≅ (Over.pullback (spMap (algebraMap K L))).obj A, IsMonHom e.hom

noncomputable abbrev spFibre {W : Type} [CommRing W] [IsLocalRing W] (G : Over (Sp W)) : Over (Sp (IsLocalRing.ResidueField W)) :=
  (Over.pullback (spMap (IsLocalRing.residue W))).obj G

def PotModel (V K : Type) [CommRing V] [Field K] [Algebra V K] (A : Over (Sp K)) [GrpObj A]
    (Q : ∀ (W : Type) [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G], Prop) : Prop :=
  ∃ (W L : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Field L) (_ : Algebra V W)
    (_ : Algebra W L) (_ : Algebra K L) (_ : IsFractionRing W L),
    (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ Module.Finite V W ∧
    IsLocalHom (algebraMap V W) ∧ IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧
    ∃ (G : Over (Sp W)) (_ : GrpObj G), IsModel (L := L) A G ∧ Q W G

def SSRedFor (C : ∀ (k : Type) [Field k], Prop)
    (Q : ∀ (W : Type) [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G], Prop) : Prop :=
  ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], C (IsLocalRing.ResidueField V) →
    ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → PotModel V K A Q

def SplitSemi (W : Type) [CommRing W] [IsLocalRing W] (G : Over (Sp W)) [GrpObj G] : Prop :=
  IsSemiAbelian G ∧ ∃ E : SplitExt (Sp (IsLocalRing.ResidueField W)), E.IsGt (spFibre G)

def SemistableAll : Prop := SSRedFor (fun _ _ => True) SplitSemi

def SemistableFin : Prop := SSRedFor (fun k _ => Finite k) SplitSemi

def SemistablePol : Prop :=
  ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]
    [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) →
    ∀ A : Out.PolAV (Sp K), PotModel V K A.A SplitSemi
end GlobalTheory.SS
