import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Definitions.Divisors.FrameSignSimple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T}

def thSub (W : G.Weil) (p : Pair T) : Submodule ℂ (WO (G.pS p) (G.pT p) → ℂ) where
  carrier := {f | IsThetaFunO W.ψ (G.pS p) (G.pT p) f}
  add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg

open Classical in

def toTh (W : G.Weil) (p : Pair T) (f : WO (G.pS p) (G.pT p) → ℂ) : thSub W p :=
  if h : IsThetaFunO W.ψ (G.pS p) (G.pT p) f then ⟨f, h⟩ else 0

theorem coe_toTh (W : G.Weil) (p : Pair T) {f : WO (G.pS p) (G.pT p) → ℂ} (h : IsThetaFunO W.ψ (G.pS p) (G.pT p) f) :
    (toTh W p f : WO (G.pS p) (G.pT p) → ℂ) = f := by
  simp [toTh, h]

def lastIx (D : D7) : Fin D.R.m := ⟨D.R.m - 1, by have := D.R.two_le_m; omega⟩

theorem lastIx_succ (D : D7) : D.R.m = (lastIx D : ℕ) + 1 := by
  have := D.R.two_le_m
  simp only [lastIx]
  omega

variable {W : G.Weil}

def colMapV (S : GridChoice W U) {t : T} (fs : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)
    (x : ∀ j, FinPt G (.top j)) : VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m)) :=
  chainTo (V := fun j => VV ℂ (wt G (.top j)))
    (fun j => if h : j < D.R.m then S.Z.scal 1 (.top t j) •
      fockComp W S.N.frC (.top t j) (fs ⟨j, h⟩) (x j * S.N.u _) (x (j + 1) * S.N.u _) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹

def rowMapV (S : GridChoice W U)
    (gs : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
    (y : ∀ i, FinPt G (.grid i D.R.m)) : VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) :=
  chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then S.Z.scal 1 (.chi i D.R.m : Pair T) •
      fockComp W S.N.frC (.chi i D.R.m : Pair T) (gs ⟨i, h⟩) (y i * S.N.u _) (y (i + 1) * S.N.u _) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ ∘ₗ funOf (listedWt G (.grid 0 D.R.m))

theorem colMap_eq (S : GridChoice W U) {t : T} (d : PureDat G t) (x : ∀ j, FinPt G (.top j)) :
    S.colMap d x = colMapV S (fun j => S.Z.vec (d.1 j)) x := rfl

theorem rowMap_eq (S : GridChoice W U) {t : T} (d : PureDat G t) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    S.rowMap d y = rowMapV S (fun i => S.Z.vec (d.2 i)) y := rfl

def topLast (g : FinPt G (.top D.R.m)) : FinPt G (.top ((lastIx D : ℕ) + 1)) := lastIx_succ D ▸ g

def gridLast (g : FinPt G (.grid D.R.m D.R.m)) : FinPt G (.grid ((lastIx D : ℕ) + 1) D.R.m) := lastIx_succ D ▸ g

def colShift (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m)) :
    (WO (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D))) → ℂ) →ₗ[ℂ]
      (WO (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D))) → ℂ) :=
  W.om (.top t (lastIx D)) (G.toPair (.top t (lastIx D)) 1
    (topLast ((S.N.u (.top D.R.m))⁻¹ * g * S.N.u (.top D.R.m))).1)

def rowShift (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m)) :
    (WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)) → ℂ) →ₗ[ℂ]
      (WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)) → ℂ) :=
  W.om (.chi (lastIx D) D.R.m) (G.toPair (.chi (lastIx D) D.R.m) 1
    (gridLast ((S.N.u (.grid D.R.m D.R.m))⁻¹ * k * S.N.u (.grid D.R.m D.R.m))).1)

end GlobalTheory.LastVertexInv

namespace GlobalTheory.LastVertexInv

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem inRange_top (t : T) (j : Fin D.R.m) : (Pair.top t (j : ℕ) : Pair T).InRange D.R.m := by
  have := j.2
  simp [Pair.InRange, Node.InRange]

theorem inRange_chi (i : Fin D.R.m) : (Pair.chi (i : ℕ) D.R.m : Pair T).InRange D.R.m := by
  have := i.2
  simp [Pair.InRange, Node.InRange]

theorem defPair_top (t : T) (j : Fin D.R.m) : DefPair D.R.m (Pair.top t (j : ℕ) : Pair T) := by
  have := j.2
  simp [DefPair]

theorem defPair_chi (i : Fin D.R.m) : DefPair D.R.m (Pair.chi (i : ℕ) D.R.m : Pair T) := by
  have := i.2
  simp [DefPair]

theorem vec_theta (S : GridChoice W U) {t : T} {p : Pair T} (hp : DefPair D.R.m p) (hIn : p.InRange D.R.m)
    (d : FinDatum G t p) (h : S.Z.HasVec d) : IsThetaFunO W.ψ (G.pS p) (G.pT p) (S.Z.vec d) := by
  obtain ⟨f, hf⟩ := h
  rw [Normal.vec, FinDatum.vec_eq W hf]
  exact (W.om_is p hIn).om_pres _ _
    (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hf (S.Z.vac_is p hp).2.theta)

theorem colShift_theta (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m))
    {f : WO (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D))) → ℂ} (h : IsThetaFunO W.ψ _ _ f) :
    IsThetaFunO W.ψ _ _ (colShift S t g f) :=
  (W.om_is _ (inRange_top t (lastIx D))).om_pres _ _ h

theorem rowShift_theta (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m))
    {f : WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)) → ℂ} (h : IsThetaFunO W.ψ _ _ f) :
    IsThetaFunO W.ψ _ _ (rowShift S k f) :=
  (W.om_is _ (inRange_chi (lastIx D))).om_pres _ _ h

end GlobalTheory.LastVertexInv
