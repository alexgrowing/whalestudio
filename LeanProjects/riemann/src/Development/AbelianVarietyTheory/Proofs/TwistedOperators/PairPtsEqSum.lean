import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def thetaSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  add_mem' := by
    intro f g hf hg
    obtain ⟨U₁, hU₁, h₁⟩ := hf.level
    obtain ⟨U₂, hU₂, h₂⟩ := hg.level
    refine ⟨fun γ w => ?_, ⟨U₁ ⊓ U₂, hU₁.inter hU₂, fun u hu hu0 => ?_⟩, hf.cont.add hg.cont,
      fun k L hL h0 w => (hf.smooth k L hL h0 w).add (hg.smooth k L hL h0 w)⟩
    · simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
    · funext w
      have e₁ := congrFun (h₁ u hu.1 hu0) w
      have e₂ := congrFun (h₂ u hu.2 hu0) w
      simp only [heisO, Pi.add_apply] at e₁ e₂ ⊢
      rw [mul_add, e₁, e₂]
  zero_mem' := ⟨fun γ w => by simp, ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun u _ _ => by funext w; simp [heisO]⟩, continuous_const,
    fun k L hL h0 w => contDiff_const⟩
  smul_mem' := by
    intro c f hf
    obtain ⟨U₁, hU₁, h₁⟩ := hf.level
    refine ⟨fun γ w => ?_, ⟨U₁, hU₁, fun u hu hu0 => ?_⟩, hf.cont.const_smul c,
      fun k L hL h0 w => (hf.smooth k L hL h0 w).const_smul c⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hf.quasi]; ring
    · funext w
      have e₁ := congrFun (h₁ u hu hu0) w
      simp only [heisO, Pi.smul_apply, smul_eq_mul] at e₁ ⊢
      rw [← e₁]; ring

variable (t : T) in

def positionPair (m : ℕ) : Fin m ⊕ Fin m → Pair T
  | .inl j => .top t j
  | .inr i => .chi i m

variable (G) in

abbrev FactorFn (t : T) (a : Fin D.R.m ⊕ Fin D.R.m) : Type :=
  WO (G.pS (positionPair t D.R.m a)) (G.pT (positionPair t D.R.m a)) → ℂ

def vecOf (S : GridChoice W U) {t : T} (d : PureDat G t) : ∀ a, FactorFn G t a
  | .inl j => S.Z.vec (d.1 j)
  | .inr i => S.Z.vec (d.2 i)

def kkV (S : GridChoice W U) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) (a : FinPt G p.small) (b : FinPt G p.big) :
    VV ℂ (wt G p.small) →ₗ[ℂ] VV ℂ (wt G p.big) :=
  S.Z.scal 1 p • fockComp W S.N.frC p f (a * S.N.u _) (b * S.N.u _)

def colV (S : GridChoice W U) {t : T} (v : ∀ a, FactorFn G t a) (x : ∀ j, FinPt G (.top j)) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m)) :=
  chainTo (V := fun j => VV ℂ (wt G (.top j)))
    (fun j => if h : j < D.R.m then kkV S (.top t j) (v (.inl ⟨j, h⟩)) (x j) (x (j + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹

def rowV (S : GridChoice W U) {t : T} (v : ∀ a, FactorFn G t a) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) :=
  chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then kkV S (.chi i D.R.m) (v (.inr ⟨i, h⟩)) (y i) (y (i + 1)) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ ∘ₗ funOf (listedWt G (.grid 0 D.R.m))

def pairFn (S : GridChoice W U) {t : T} (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (v : ∀ a, FactorFn G t a) : VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ :=
  (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂ (colV S v x) (rowV S v y)

theorem pairPts_eq_sum (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (x : ∀ j, FinPt G (.top j))
    (y : ∀ i, FinPt G (.grid i D.R.m)) : pairPts S τ x y = τ.sum fun d c => c • pairFn S x y (vecOf S d) := rfl

def moved (S : GridChoice W U) (j : ℕ) (k : FinPt G (.grid (j + 1) D.R.m)) : GA D (G.V (.grid (j + 1) D.R.m)) :=
  ((S.N.u (.grid (j + 1) D.R.m))⁻¹ * k * S.N.u (.grid (j + 1) D.R.m) : FinPt G (.grid (j + 1) D.R.m))

def moveV (S : GridChoice W U) {t : T} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.grid (j + 1) D.R.m))
    (v : ∀ a, FactorFn G t a) : ∀ a, FactorFn G t a :=
  Function.update
    (Function.update v (.inr ⟨j, by omega⟩)
      (W.om (.chi j D.R.m) (G.toPair (.chi j D.R.m) 1 (moved S j k)) (v (.inr ⟨j, by omega⟩)) : FactorFn G t (.inr ⟨j, by omega⟩)))
    (.inr ⟨j + 1, hj⟩)
    (W.om (.chi (j + 1) D.R.m) (G.toPair (.chi (j + 1) D.R.m) (moved S j k) 1) (v (.inr ⟨j + 1, hj⟩)) : FactorFn G t (.inr ⟨j + 1, hj⟩))

end GlobalTheory.RowVertexInv
