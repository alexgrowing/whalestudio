import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DVRSplitting

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

def IsFinUnram (V W : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra V W] : Prop :=
  Function.Injective (algebraMap V W) ∧ Module.Finite V W ∧ Algebra.FormallyUnramified V W

theorem IsFinUnram.map_maximalIdeal {V W : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra V W] (h : IsFinUnram V W) :
    IsLocalHom (algebraMap V W) ∧ (maximalIdeal V).map (algebraMap V W) = maximalIdeal W := by
  obtain ⟨hi, hf, hu⟩ := h
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective V W).mpr hi
  have : IsLocalHom (algebraMap V W) := inferInstance
  exact ⟨this, Algebra.FormallyUnramified.map_maximalIdeal⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def SplitsOver {Y : Model Xo c β} (P : ValPt Y) (W : Type) [CommRing W] [IsLocalRing W] [Algebra P.V W] : Prop :=
  ∃ S : SplitExt (Sp (ResidueField W)),
    S.IsGt ((Over.pullback (spMap ((residue W).comp (algebraMap P.V W)))).obj P.G.G)

def UnifOver {Y : Model Xo c β} (P : ValPt Y) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] [Algebra P.V W] :
    Prop :=
  (∃ t : SAB H (Sp W), Nonempty (SABMap t P.G (spMap (algebraMap P.V W)))) ∧
    ∀ (t : SAB H (Sp W)) (_ : SABMap t P.G (spMap (algebraMap P.V W))),
      UniformisationConclusion t ((spMap (algebraMap P.V W) ≫ P.yt) ⁻¹' abLocus Y.t.G)

def SplitAtPts (Y : Model Xo c β) : Prop :=
  ∀ P : ValPt Y, ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra P.V W),
    IsFinUnram P.V W ∧ SplitsOver P W

def UnifAtPts (Y : Model Xo c β) : Prop :=
  ∀ (P : ValPt Y) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Algebra P.V W],
    IsFinUnram P.V W → SplitsOver P W → UnifOver P W

def DvrOut (Y : Model Xo c β) : Prop :=
  ∀ P : ValPt Y, ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra P.V W),
    IsFinUnram P.V W ∧ SplitsOver P W ∧ UnifOver P W

def DvrIn (Y : Model Xo c β) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → Finite (ResidueField V) →
    ∀ (b : O →+* V), IsLocalHom b → ∀ (ϖ : V), Irreducible ϖ → ∀ a : ArcIn D l β V b,
      ∃ y : Sp V ⟶ Y.X, y ≫ Y.s = spMap b ∧ Set.range (Out.jK V ≫ y) ⊆ Set.range Y.j ∧
        Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id V) ϖ y

def DvrData : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β),
    (Y.SplitFibres → SplitAtPts Y) ∧ (Y.N3 → UnifAtPts Y) ∧ (Y.N4 → DvrIn Y)

end GlobalTheory.IndefiniteRowSideFullHecke.DVRSplitting
