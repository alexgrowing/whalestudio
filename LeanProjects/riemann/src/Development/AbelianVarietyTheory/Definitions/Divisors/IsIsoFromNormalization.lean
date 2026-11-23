import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NeronCurve

def IsCurve (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] : Prop :=
  SmoothOfRelativeDimension 1 (strHom k C) ∧ IsProjOver (strHom k C) ∧ GeometricallyConnected (strHom k C)

def SemiNeg (k : Type) [Field k] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] (F : C.Modules) : Prop :=
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ i : W ⟶ F, Mono i → interNum k (structureModule C) ![det W r] ≤ 0

def IsGen {K : Type} [Field K] {C : Scheme.{0}} (x : Sp K ⟶ C) : Prop := IsDominant x ∧ IsPreimmersion x

theorem isGen_fromSpecStalk (C : Scheme.{0}) [IsIntegral C] :
    IsGen (K := C.functionField) (C.fromSpecStalk (genericPoint C)) :=
  ⟨show IsDominant (C.fromSpecStalk (genericPoint C)) from ⟨by
      refine Dense.mono (s₁ := {genericPoint C}) ?_ (dense_iff_closure_eq.2 (genericPoint_spec C).def)
      rintro _ rfl
      exact ⟨_, Scheme.fromSpecStalk_closedPoint⟩⟩,
    inferInstanceAs (IsPreimmersion (C.fromSpecStalk (genericPoint C)))⟩

structure IsNeron {K : Type} [Field K] {C : Scheme.{0}} (x : Sp K ⟶ C) (N : Over C) : Prop where
  smooth : Smooth N.hom
  separated : IsSeparated N.hom
  quasiCompact : QuasiCompact N.hom
  ext : ∀ Y : Over C, Smooth Y.hom → Function.Bijective fun f : Y ⟶ N ↦ (Over.pullback x).map f

end GlobalTheory.NeronCurve
