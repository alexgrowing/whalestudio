import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood

noncomputable section

namespace GlobalTheory.LiftLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

section Rec

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def ParUpRec (i : N.Loc) : Prop :=
  ∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig →
    (MjSig N A i Sig).map (what₂.thetaT (N.mu i) (N.j i)) ≤ eigC N A i x

def DownMemRec (i : N.Loc) : Prop :=
  ∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig →
    (eigC N A i x).map (what₂.thetaP (N.mu i) (N.j i)) ≤ MjSig N A i Sig

def TypeNZRec (i : N.Loc) : Prop :=
  ∀ x ∈ ZgoodN N A i, ∀ F ∈ eigC N A i x, what₂.thetaP (N.mu i) (N.j i) F = 0 → F = 0

def GoodPartRec (i : N.Loc) : Prop :=
  goodPartM N A i = ⨆ x ∈ ZgoodN N A i, ⨆ Sig ∈ {Sig | HasParamX N A i x Sig}, MjSig N A i Sig

def PtDet (i : N.Loc) : Prop :=
  ∀ P P' : A.AV i, (∀ w, IsSplitPl H w → A.locV i P w = A.locV i P' w) → A.ptV i P = A.ptV i P'

def LocCongr (i : N.Loc) : Prop :=
  ∀ Sig Sig' : List (Part A.CG), (∀ p ∈ Sig, 1 ≤ p.d) → (∀ p ∈ Sig', 1 ≤ p.d) →
    (∀ w, IsSplitPl H w → isoLoc N A Sig w = isoLoc N A Sig' w) →
    ∀ w, IsSplitPl H w → isoLoc N A (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv) w =
      isoLoc N A (twistIso N A (Sig' ++ [muPart N A i]) A.etaTinv) w

def ThetaPt (i : N.Loc) : Prop := ∀ σ P, AtM N A i σ → thetaOf N A i σ P → ∃ x, A.ptV i P = some x

def LabCompat (i : N.Loc) : Prop := ∀ σ Sig, HasParamW N A i σ Sig → (N.goodRow σ ↔ goodSig N A Sig)

def GoodParamX (i : N.Loc) : Prop := ∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig → goodSig N A Sig

def AtMOfParam (i : N.Loc) : Prop :=
  ∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig → ∀ σ, HasParamW N A i σ Sig → AtM N A i σ

def PtAt (i : N.Loc) : Prop :=
  ∀ P : A.AV i, (∃ x : N.X i, ∀ w, SplitOut N i w → ∃ p : Polynomial (N.O i),
    p.map (iotaO N A i) = galPol A (A.lpTw (A.locV i P w) ((1 - (R.nV : ℝ)) / 2)) ∧
    p.map (IsLocalRing.residue (N.O i)) = (heckePol N i x w).map (IsLocalRing.residue (N.O i))) → ∃ x, A.ptV i P = some x

def CharSum : Prop :=
  ∀ (w : PlE H) (a b χ : A.LP w) (s : ℝ), A.lpDim χ = 1 →
    A.lpChar (A.lpSum a b) χ = A.lpSum (A.lpChar a χ) (A.lpChar b χ) ∧
    A.lpChar (A.lpTw a s) χ = A.lpTw (A.lpChar a χ) s ∧ A.lpChar (A.lpZero w) χ = A.lpZero w

end Rec

def RowSize (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ →
    ∀ w : PlE D.host, IsSplitPl D.host w → D.naut.unr (D.naut.locW i σ w) →
    ∀ α ∈ D.naut.frobEig (D.naut.locW i σ w),
      ‖α‖ < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((D.R.t : ℝ) - 1) / 2)

def HeckeSplitOne (D : D7) : Prop :=
  ∀ ν ν' : D.naut.CG 1,
    (∀ᶠ w in Filter.cofinite, IsSplitPl D.host w → D.naut.locG ν w = D.naut.locG ν' w) → ν = ν'

def ThetaOne (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → ∃ P, thetaOf D.nd D.naut i σ P

def LamPos (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  ∀ σ : D.what₂.FT,
    (∀ f ∈ D.what₂.isot j σ, D.what₂.thetaP μ j (D.what₂.thetaT μ j f) = ((D.what₂.lamP μ j σ : ℝ) : ℂ) • f) ∧
    (D.what₂.isot j σ ≠ ⊥ → 0 < D.what₂.lamP μ j σ)

section Exp

open Formalism.MainNotions.IntegralHeckeForms

def CommG (D : D7) : Prop :=
  ∀ (i : D.ntw.Tw), D.ntw.NonzeroIndexPlace i → ∀ (b : Bool), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ g k P, HkIdx i k P →
    (D.nexp.actG i j b g).toLinearMap ∘ₗ D.nexp.hkF i j b k P = D.nexp.hkF i j b k P ∘ₗ (D.nexp.actG i j b g).toLinearMap

def IntRest (D : Formalism.BasicNotions.D7) (E : XD D) : Prop :=
  ∀ (i : D.ntw.Tw), D.ntw.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ (b : Bool),
    (∀ g, (D.nexp.Bsup i j b).map ((D.nexp.actG i j b g).toLinearMap.restrictScalars (D.ntw.O i)) ≤
      D.nexp.Bsup i j b) ∧
    Submodule.span (FractionRing (D.ntw.O i)) (Mall D.nexp i j b : Set (D.nexp.Fm i j b)) =
      Fm0 D.nexp i j b ∧
    (∀ a ∈ E.Dat0 i j b, ∃ c : ℕ, ∀ Q M, (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) → ClsQ (D := D) Q →
      Disjoint Q (D.ntw.S0 i) → Disjoint Q (D.nexp.lev i j b a) →
      ((D.ntw.l i : D.ntw.O i) ^ c) • D.nexp.thU i j b Q M a ∈
        LinearMap.range ((Mall D.nexp i j b).subtype.rTensor _)) ∧
    (∀ k Q (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), TwOK i k Q ψ → UnrG ψ →
      ∀ a ∈ E.Dat0 i j b,
      D.nexp.thPsi i j b k Q ψ a ⊆
        ((((Fm0 D.nexp i j b).restrictScalars (D.ntw.O i)).baseChange (D.ntw.Ok i k) :
          Submodule (D.ntw.Ok i k) (D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i j b)) :
            Set (D.ntw.Ok i k ⊗[D.ntw.O i] D.nexp.Fm i j b)))

end Exp

end GlobalTheory.LiftLeaf
