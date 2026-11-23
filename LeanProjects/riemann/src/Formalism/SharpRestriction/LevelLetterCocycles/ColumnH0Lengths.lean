import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition

noncomputable section

namespace Formalism.MainNotions.ColumnH0Lengths

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KillingConditions NumberField IsDedekindDomain

variable {D : D7}

def ColumnLengthInvariantsBound (L : SizeData₂ D) (X : HubData D) (c : ℝ) : Prop := InvariantsBoundConditions L X c

def CondCB (L : SizeData₂ D) (X : HubData D) (c : ℝ) : Prop :=
  ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D → RangeAD L X.exc (D.nd.l i) →
    (X.cB i : ℝ) ≤ c * D.R.t * D.R.n * D.R.nV * Formalism.MainNotions.TwistedPlaces.large₂ L

def H0CyclotomicLengthBound (L : SizeData₂ D) (X : HubData D) (c : ℝ) : Prop :=
  ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D → RangeAD L X.exc (D.nd.l i) →
    (h0 D.nd i (X.dc i).col : ℝ) ≤ c * D.R.t

def H0ConstantBound (L : SizeData₂ D) (X : HubData D) (c : ℝ) : Prop :=
  ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D → RangeAD L X.exc (D.nd.l i) →
    Formalism.MainNotions.TwistedPlaces.SplitK D (D.nd.l i) → ∀ u ∈ (X.dc i).col, (X.c0 i u : ℝ) ≤ c * D.R.r * Formalism.MainNotions.TwistedPlaces.large₂ L

def H0BoundAtColumnPlace (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (X : HubData D) : Prop :=
  LocalSituation.Conclusion2 D HW F → ∀ i, Formalism.MainNotions.TwistedPlaces.TwLoc D i → D.nd.l i ∉ Formalism.MainNotions.TwistedPlaces.gset D →
    Formalism.MainNotions.TwistedPlaces.SplitK D (D.nd.l i) → ∀ u ∈ (X.dc i).col, ∀ π ∈ D.nd.Zgood i,
      (Br.h0W i u (X.ρ i) π : ℝ) ≤ D.R.r * (X.c0 i u : ℝ)

def ColumnLengthHypotheses (L : SizeData₂ D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (X : HubData D) (c : ℝ) : Prop :=
  CondCB L X c ∧ H0CyclotomicLengthBound L X c ∧ H0ConstantBound L X c ∧ LocalSituation.Conclusion2 D HW F ∧ H0BoundAtColumnPlace HW F X

def ColumnLengthTheorem (L : SizeData₂ D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (X : HubData D) (c : ℝ) : Prop := ColumnLengthHypotheses L HW F X c → ColumnLengthInvariantsBound L X c

end Formalism.MainNotions.ColumnH0Lengths
