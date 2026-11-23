import Mathlib
import Formalism.LocalRingCardinality.DataNChTie

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion

open Formalism.BasicNotions

variable {D : D7}

def fracBase (D : D7) (i : D.ntw.Tw) : FractionRing (D.ntw.O0 i) →+* FractionRing (D.ntw.O i) :=
  IsFractionRing.map (j := algebraMap (D.ntw.O0 i) (D.ntw.O i)) (D.ntw.O_inj i)

theorem algebraMap_ext_injective (c : NChoice D) (w : D.what₂.places.Pl) :
    Function.Injective (algebraMap (D.ntw.O (c.twI w)) (c.Oe w)) := by
  rw [IsScalarTower.algebraMap_eq (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w), RingHom.coe_comp]
  exact (c.Oe_inj w).comp (D.ntw.Ok_inj _ _)

def fracExt (c : NChoice D) (w : D.what₂.places.Pl) : FractionRing (D.ntw.O (c.twI w)) →+* FractionRing (c.Oe w) :=
  IsFractionRing.map (j := algebraMap (D.ntw.O (c.twI w)) (c.Oe w)) (algebraMap_ext_injective c w)

def embSide (D : D7) (i : D.ntw.Tw) (b : Bool) : D.LL0 →+* FractionRing (D.ntw.O0 i) :=
  if b then D.ntw.emb0 i else D.ntw.emb0b i

def IsInclusion (D : D7) (K : Type) [Field K] [Algebra K D.what₂.LL] (κ : K →+* D.LL0) : Prop :=
  ∀ x : K, ((κ x : D.LL0) : D.what₂.LL) = algebraMap K D.what₂.LL x

def smallEmb (c : NChoice D) (w : D.what₂.places.Pl) {K : Type} [Field K] (κ : K →+* D.LL0) :
    K →+* FractionRing (D.ntw.O (c.twI w)) :=
  (fracBase D (c.twI w)).comp ((embSide D (c.twI w) (c.sd w)).comp κ)

def CompatAt (c : NChoice D) (w : D.what₂.places.Pl) (K : Type) [Field K] [Algebra K D.what₂.LL]
    (ιK : K →+* FractionRing (D.ntw.O (c.twI w))) : Prop :=
  (c.embW w).comp (algebraMap K D.what₂.LL) = (fracExt c w).comp ιK

def EmbCompat : Prop :=
  ∀ (D : D7) (c : NChoice D), NChTie D c →
    ∀ (K : Type) [Field K] [NumberField K] [Algebra K D.what₂.LL] (κ : K →+* D.LL0), IsInclusion D K κ →
      ∀ (w : D.what₂.places.Pl) (ιK : K →+* FractionRing (D.ntw.O (c.twI w))), ιK = smallEmb c w κ →
        CompatAt c w K ιK

example (D : D7) : IsInclusion D D.LL0 (RingHom.id _) := fun _ => rfl

example (c : NChoice D) (w : D.what₂.places.Pl) (y : D.ntw.O0 (c.twI w)) :
    fracExt c w (fracBase D (c.twI w) (algebraMap _ (FractionRing (D.ntw.O0 (c.twI w))) y)) =
      algebraMap (c.Oe w) (FractionRing (c.Oe w))
        (algebraMap (D.ntw.O (c.twI w)) (c.Oe w) (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y)) := by
  simp [fracExt, fracBase, IsFractionRing.map]

end GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion

end
