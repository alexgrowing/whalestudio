import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

open GlobalTheory.NeronCurve

def NeronLieSeminegative : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C →
    ∀ (K : Type) [Field K] (x : Sp K ⟶ C), IsGen x →
    ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ (N : Over C) [GrpObj N] (φ : A.left ⟶ N.left), IsGrpPullback A N x φ → IsNeron x N → SemiNeg k (Lie N)

end GlobalTheory.Published
