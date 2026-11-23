import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipReal

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB

section Defs

variable {D : D7} (X : HidaSetting D)

abbrev RA : Type := X.B.I.E ⊗[X.B.I.F] Af X.B.I.F

abbrev ic : X.B.I.E →+* RA X := Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)

instance inv2 : Invertible (2 : RA X) :=
  (Invertible.map (ic X) (2 : X.B.I.E)).copy 2 (map_ofNat (ic X) 2).symm

def Bf : Matrix (Fin X.B.I.n) (Kap X) (RA X) := (Bm X).map (ic X)
def Bf' : Matrix (Kap X) (Fin X.B.I.n) (RA X) := (Bm' X).map (ic X)
def JBf : Matrix (Kap X) (Kap X) (RA X) := (JB X).map (ic X)

def Mf (x : X.B.I.Gf) : Matrix (Kap X) (Kap X) (RA X) := Bf' X * X.B.I.fmat x * Bf X

def Cg {α β : Type*} (c : ℕ) (A : Matrix α β (RA X)) : Prop :=
  ∀ i j, ∃ t ∈ IntAf X.B.I.F X.B.I.E, A i j = (c : RA X) * t

end Defs

def NfPat : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (x : X.B.I.Gf), x ∈ X.NfinU u → InPat (lvk X) 1 (Mf X x - 1)

def NfOfPat : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (x : X.B.I.Gf), InPat (lvk X) 1 (Mf X x - 1) → x ∈ X.NfinU u

def CayInvR : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (x : X.B.I.Gf), InPat (lvk X) 1 (Mf X x - 1) →
    ∃ Z : Matrix (Kap X) (Kap X) (RA X), InPat (lvk X) 1 Z ∧
      Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) Z * JBf X = -(JBf X * Z) ∧ cay (2 * D.R.rS + 2) Z = Mf X x

def SkewApprox : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Z : Matrix (Kap X) (Kap X) (RA X)), InPat (lvk X) 1 Z →
    Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) Z * JBf X = -(JBf X * Z) → ∀ c : ℕ, 1 ≤ c →
      ∃ Y : Matrix (Kap X) (Kap X) X.B.I.E, InPat (lvk X) 1 Y ∧ Yᴴ * JB X = -(JB X * Y) ∧
        Cg X c (Y.map (ic X) - Z)

def CayCont : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Z : Matrix (Kap X) (Kap X) (RA X)) (c : ℕ), 1 ≤ c →
    ∃ c' : ℕ, 1 ≤ c' ∧ ∀ Z' : Matrix (Kap X) (Kap X) (RA X), Cg X c' (Z' - Z) →
      Cg X c (cay (2 * D.R.rS + 2) Z' - cay (2 * D.R.rS + 2) Z)

def KgOfClose : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (x : X.B.I.Gf) (g : ℕ), 1 ≤ g →
    ∃ c : ℕ, 1 ≤ c ∧ ∀ y : X.B.I.Gf, Cg X c (Mf X y - Mf X x) → x⁻¹ * y ∈ X.B.I.Kg g

end Formalism.L2.SG.Pf.SlabNDensePf
