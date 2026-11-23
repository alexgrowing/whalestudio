import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.Foundations.Schemes.AffineOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.SpanSingletonProduct
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open AlgebraicGeometry CategoryTheory

namespace FunctorialResolution.EmbeddedResolution

variable {X : Scheme.{u}}

def OrderLE (I : X.IdealSheafData) (m : ℕ) : Prop :=
  ∀ x : X, orderAt I x ≤ (m : ℕ∞)

theorem orderLE_iff (I : X.IdealSheafData) (m : ℕ) :
    OrderLE I m ↔ ∀ x : X, orderAt I x ≤ (m : ℕ∞) := Iff.rfl

structure MaxOrderEq (I : X.IdealSheafData) (m : ℕ) : Prop where
  orderLE : OrderLE I m
  coSupport_nonempty : (orderAtLeastLocus I m).Nonempty

def lcmUpTo (m : ℕ) : ℕ := (List.range' 1 m).foldr Nat.lcm 1

theorem lcmUpTo_eq_foldr (m : ℕ) : lcmUpTo m = (List.range' 1 m).foldr Nat.lcm 1 := rfl

theorem lcmUpTo_one : lcmUpTo 1 = 1 := rfl

def tuningExponent (m : ℕ) : ℕ := if m ≤ 1 then 1 else (m - 1) * lcmUpTo m

theorem tuningExponent_of_le_one {m : ℕ} (h : m ≤ 1) : tuningExponent m = 1 := by
  unfold tuningExponent
  exact if_pos h

theorem tuningExponent_of_two_le {m : ℕ} (h : 2 ≤ m) : tuningExponent m = (m - 1) * lcmUpTo m := by
  unfold tuningExponent
  exact if_neg (by omega)

theorem tuningExponent_one : tuningExponent 1 = 1 := tuningExponent_of_le_one le_rfl

noncomputable def tunedSheaf (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData)
    (m s : ℕ) : X.IdealSheafData :=
  ⨆ c : {c : ℕ → ℕ // s ≤ ∑ j ∈ Finset.range m, (m - j) * c j},
    ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ (c.1 j))).prod

theorem tunedSheaf_eq_iSup (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData)
    (m s : ℕ) :
    tunedSheaf k p I m s =
      ⨆ c : {c : ℕ → ℕ // s ≤ ∑ j ∈ Finset.range m, (m - j) * c j},
        ((List.range m).map (fun j => derivIdealSheafIterate k p j I ^ (c.1 j))).prod := rfl

noncomputable def balancedTunedSheaf (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData)
    (m : ℕ) : X.IdealSheafData :=
  tunedSheaf k p I m (tuningExponent m)

theorem balancedTunedSheaf_eq (k : Type u) [CommRing k] [IsNoetherianRing k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] (I : X.IdealSheafData)
    (m : ℕ) : balancedTunedSheaf k p I m = tunedSheaf k p I m (tuningExponent m) := rfl

def TunedSheafSuccLe : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ s : ℕ, tunedSheaf k p I m (s + 1) ≤ tunedSheaf k p I m s

def TunedSheafMulLeAdd : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ s t : ℕ, tunedSheaf k p I m s * tunedSheaf k p I m t ≤ tunedSheaf k p I m (s + t)

def DerivIdealSheafTunedSheafSucc : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ s : ℕ, derivIdealSheaf k p (tunedSheaf k p I m (s + 1)) = tunedSheaf k p I m s

def MaxContactIdealTunedSheafEq : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ s : ℕ, 1 ≤ s →
      derivIdealSheafIterate k p (s - 1) (tunedSheaf k p I m s) =
        derivIdealSheafIterate k p (m - 1) I

def IsMaxContactInvariantTunedSheaf : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ s : ℕ, 1 ≤ s →
      derivIdealSheafIterate k p (s - 1) (tunedSheaf k p I m s) *
          derivIdealSheaf k p (tunedSheaf k p I m s) ≤ tunedSheaf k p I m s

def TunedSheafMulEqAdd : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ r t : ℕ, (m - 1) * lcmUpTo m ≤ t →
      tunedSheaf k p I m (r * lcmUpTo m) * tunedSheaf k p I m t =
        tunedSheaf k p I m (r * lcmUpTo m + t)

def TunedSheafPowEqMul : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ r : ℕ, m - 1 ≤ r → ∀ j : ℕ, 1 ≤ j →
      tunedSheaf k p I m (r * lcmUpTo m) ^ j = tunedSheaf k p I m (j * (r * lcmUpTo m))

def IsDerivBalancedTunedSheafMulLcm : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ r : ℕ, m - 1 ≤ r → ∀ i : ℕ, i < r * lcmUpTo m →
      derivIdealSheafIterate k p i (tunedSheaf k p I m (r * lcmUpTo m)) ^ (r * lcmUpTo m) ≤
        tunedSheaf k p I m (r * lcmUpTo m) ^ (r * lcmUpTo m - i)

def CoSupportTunedSheafEqAndOrderLE : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ s : ℕ, 1 ≤ s →
      orderAtLeastLocus (tunedSheaf k p I m s) s = orderAtLeastLocus I m ∧ OrderLE (tunedSheaf k p I m s) s

theorem CoSupportTunedSheafEqAndOrderLE.orderLE (h : CoSupportTunedSheafEqAndOrderLE.{u}) (k : Type u) [Field k]
    [CharZero k] [IsNoetherianRing k] (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p] (I : X.IdealSheafData) (m : ℕ)
    (hm : 1 ≤ m) (hmax : MaxOrderEq I m) (s : ℕ) (hs : 1 ≤ s) :
    OrderLE (tunedSheaf k p I m s) s :=
  (h k X p I m hm hmax s hs).2

def IsMarkedIffOfPowLeOfLeTunedSheaf : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ s : ℕ, 1 ≤ s → ∀ J : X.IdealSheafData, I ^ s ≤ J → J ≤ tunedSheaf k p I m (m * s) →
      ∀ (E : List X.IdealSheafData) (d : BlowupSequenceData X),
        (d.IsMarked p I m E ↔ d.IsMarked p J (m * s) E) ∧
        (d.IsMarked p I m E → ∀ i : ℕ, i ≤ d.length →
          orderAtLeastLocus (d.controlledTransform J (m * s) i) (m * s) = orderAtLeastLocus (d.controlledTransform I m i) m)

def IsMarkedIffBalancedTunedSheaf : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] [IsNoetherianRing k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p] [LocallyOfFiniteType p]
    (I : X.IdealSheafData) (m : ℕ), 1 ≤ m → MaxOrderEq I m →
    ∀ (E : List X.IdealSheafData) (d : BlowupSequenceData X),
      (d.IsMarked p I m E ↔ d.IsMarked p (balancedTunedSheaf k p I m) (tuningExponent m) E) ∧
      (d.IsMarked p I m E → ∀ i : ℕ, i ≤ d.length →
        orderAtLeastLocus (d.controlledTransform (balancedTunedSheaf k p I m) (tuningExponent m) i) (tuningExponent m) =
          orderAtLeastLocus (d.controlledTransform I m i) m) ∧
      (derivIdealSheafIterate k p (tuningExponent m - 1) (balancedTunedSheaf k p I m) *
          derivIdealSheaf k p (balancedTunedSheaf k p I m) ≤ balancedTunedSheaf k p I m) ∧
      (∀ i : ℕ, i < tuningExponent m →
        derivIdealSheafIterate k p i (balancedTunedSheaf k p I m) ^ tuningExponent m ≤
          balancedTunedSheaf k p I m ^ (tuningExponent m - i))

structure TunedSheafProperties : Prop where
  isMarked_tuned_iff : IsMarkedIffBalancedTunedSheaf.{u}
  tunedSheaf_succ_le : TunedSheafSuccLe.{u}
  tunedSheaf_mul_le : TunedSheafMulLeAdd.{u}
  derivIdealSheaf_tunedSheaf_succ : DerivIdealSheafTunedSheafSucc.{u}
  derivIdealSheafIter_pred_tunedSheaf : MaxContactIdealTunedSheafEq.{u}
  derivIdealSheafIter_mul_derivIdealSheaf_le_tunedSheaf : IsMaxContactInvariantTunedSheaf.{u}
  tunedSheaf_mul_eq : TunedSheafMulEqAdd.{u}
  tunedSheaf_pow : TunedSheafPowEqMul.{u}
  derivIdealSheafIter_tunedSheaf_pow_le : IsDerivBalancedTunedSheafMulLcm.{u}
  coSupport_tunedSheaf_eq_and_orderLE : CoSupportTunedSheafEqAndOrderLE.{u}
  isMarked_iff_of_pow_le_of_le_tunedSheaf : IsMarkedIffOfPowLeOfLeTunedSheaf.{u}

end FunctorialResolution.EmbeddedResolution
