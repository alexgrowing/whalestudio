import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFits

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepK

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Geo Plane Chars RealMaps IsMatched IsConst)

variable {D : D7}

def InLat (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (z : V.V) : Prop := V.frame.equivFun z ∈ Λ

def PlaneSplit (S S₁ : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (Λ₁ : Submodule (𝓞 D.host.E) (Fin S₁.rank → D.host.E)) (ι : S₁.V →ₗ[D.host.E] S.V) (x y : S.V) : Prop :=
  S.rank = S₁.rank + 2 ∧ Formalism.BasicNotions.HSpace.IsIsomEmb S₁ S ι ∧ S.hD x x = 0 ∧ S.hD y y = 0 ∧ S.hD x y = 1 ∧
    (∀ u, S.hD (ι u) x = 0 ∧ S.hD (ι u) y = 0) ∧ (∀ u, InLat S₁ Λ₁ u ↔ InLat S Λ (ι u)) ∧
    ∀ z, InLat S Λ z → ∃ (s r : D.host.E) (u : S₁.V), InLat S Λ (s • x) ∧ InLat S Λ (r • y) ∧ InLat S₁ Λ₁ u ∧
      z = s • x + ι u + r • y

def IsStepB {T : Type} {A A' WW B' WW₁ : HSp D} (X : Tri T A A' WW) (Y : Tri T A B' WW₁) : Prop :=
  Y.rA = X.rA ∧ (∃ ι x y, PlaneSplit A' B' X.rA'.Λ Y.rA'.Λ ι x y) ∧ ∃ ι x y, PlaneSplit WW WW₁ X.rW.Λ Y.rW.Λ ι x y

def HasConstR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {a a' : ℕ} (Γ : Geo σ a a') (R : RealMaps F a a') (χ : Chars F E) (κ : ℂ) : Prop :=
  ∃ om om' Rf, IsMatched B Γ χ om om' R Rf ∧ IsConst B Γ χ om om' R Rf κ

end GlobalTheory.SqStepK
