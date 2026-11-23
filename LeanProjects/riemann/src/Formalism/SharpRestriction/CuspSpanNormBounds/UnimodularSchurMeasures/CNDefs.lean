import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionIntegrableOfLocal
import Formalism.FlagUnipotentLattices.HalfDeltaL1Bound
import Formalism.FlagUnipotentLattices.KappaAssemblyOf
import Formalism.FlagUnipotentLattices.CuspThresholdBound
import Formalism.FlagUnipotentLattices.FlagUnipotentLatticeOfRel

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

structure CSize (X : CData) where
  tau1 : X.I.GA → ℝ
  I0 : Set X.I.GA
  str : ∀ J : ℕ, Composition J → Set X.I.GA
  tau : ∀ (J : ℕ) (c : Composition J), X.I.GA → Fin c.length → ℝ
  kap : ∀ J : ℕ, Composition J → ℝ

def cn_Y (X : CData) : ℝ := Formalism.HermitianLatticeCounting.S7.Ydat X.I.n X.I.f X.I.rd (X.g : ℝ) X.b

def cn_tauS (X : CData) (C₁ : ℝ) : ℝ := cn_Y X ^ (-(C₁ * (X.qq : ℝ)))

def CSize.Mod {X : CData} (S : CSize X) (C₁ : ℝ) : Set X.I.GA := {x | cn_tauS X C₁ ≤ S.tau1 x}

def CSize.Strata {X : CData} (S : CSize X) : Prop :=
  Measurable S.tau1 ∧ (∀ J c, MeasurableSet (S.str J c)) ∧ (∀ J c, Measurable (S.tau J c)) ∧
    (∀ x, x ∈ S.I0 ∨ ∃ J, 1 ≤ J ∧ J ≤ X.qq ∧ ∃ c, x ∈ S.str J c) ∧ (∀ x ∈ S.I0, S.tau1 x = 1 / 2) ∧
    (∀ x, 0 < S.tau1 x ∧ S.tau1 x ≤ 1 / 2) ∧
    ∀ J c, ∀ x ∈ S.str J c, ∀ a, S.tau1 x ≤ S.tau J c x a

theorem CSize.measurableSet_Mod {X : CData} (S : CSize X) (h : S.Strata) (C₁ : ℝ) : MeasurableSet (S.Mod C₁) :=
  measurableSet_le measurable_const h.1

end Formalism.MainNotions.LeviCoordinates

end
