import Mathlib
import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.LocalToGlobal.Divisibility.InertRationalAdjoint

open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.L2.Indef

section Dat

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}

structure FamIn3 (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
    (Pl0 I0 Ty T : Type) (m : ℕ) where

  A : FamIn K G Pl0 T m

  okI : T → Set I0

  heckeRI : ∀ τ, okI τ × Ty → Module.End K (A.MtildeCSD τ).Forms

  heckeLI : ∀ j τ, okI τ × Ty → Module.End K (A.MtCSD j τ).Forms

  trI : Fin m → (I0 × Ty → K) → I0 × Ty → K

namespace FamIn3

variable {I0 Ty T : Type} {m : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m)

def rowI (τ : T) : InertDat3 (A3.A.fam.R τ) I0 Ty where
  PlI := A3.okI τ
  plI := Subtype.val
  opI := A3.heckeRI τ

def liftI (j : Fin m) (τ : T) : InertDat3 (A3.A.fam.L j τ) I0 Ty where
  PlI := A3.okI τ
  plI := Subtype.val
  opI := A3.heckeLI j τ

def fam3 : DefFam3 K G Pl0 I0 Ty T (Fin m) where
  F := A3.A.fam
  RI := A3.rowI
  LI := A3.liftI
  trI := A3.trI

def side3 (P : Subgroup G) (ψ : P →* Kˣ) (Zs : DefSub A3.fam3.amb3) : DefSide A3.fam3.base3 := A3.fam3.side3 P ψ Zs

end FamIn3

def FamIn.triv3 {T : Type} {m : ℕ} (A : FamIn K G Pl0 T m) : FamIn3 K G Pl0 PEmpty Unit T m where
  A := A
  okI _ := ∅
  heckeRI _ _ := 1
  heckeLI _ _ _ := 1
  trI _ e := e

end Dat

end Formalism.L2.DIV
