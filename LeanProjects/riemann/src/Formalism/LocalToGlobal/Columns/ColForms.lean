import Mathlib
import Formalism.LocalToGlobal.Columns.RhoEqOfSmulEq
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Formalism.LocalToGlobal.Columns.CoefCol

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

structure Lev (κ K : Type) [CommRing κ] [Field K] (n : ℕ) where

  H : Subgroup (GL (Fin n) κ)

  lam : ↥H →* Kˣ

def Lev.inv {κ K : Type} [CommRing κ] [Field K] {n : ℕ} (l : Lev κ K n) : Lev κ K n := ⟨l.H, l.lam⁻¹⟩

abbrev LevFam (E K : Type) [Field E] [NumberField E] [Field K] (n : ℕ)
    (SG : Finset (HeightOneSpectrum (𝓞 E))) : Type :=
  ∀ w : SG, Lev (𝓞 E ⧸ w.1.asIdeal) K n

namespace LevFam

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
  (Λ : LevFam E K n SG)

def grp : Subgroup (GLG E n SG) := Subgroup.pi Set.univ fun w => (Λ w).H

def chr : ↥Λ.grp →* Kˣ := piChar (fun w => (Λ w).H) fun w => (Λ w).lam

def inv : LevFam E K n SG := fun w => (Λ w).inv

end LevFam

section Form

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}

abbrev FormG (Λ : LevFam X.E X.K n SG) : Type := UF X.E n × ↥Λ.grp

@[reducible] def FormG.incl (Λ : LevFam X.E X.K n SG) : FormG Λ →* UF X.E n × GLG X.E n SG :=
  MonoidHom.prodMap (MonoidHom.id _) Λ.grp.subtype

instance formAct (Λ : LevFam X.E X.K n SG) : MulAction (FormG Λ) (DecoSet X.E n ST SG) :=
  MulAction.compHom _ (FormG.incl Λ)

def formRho (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG) :
    FormG Λ →* Module.End X.K C.V where
  toFun a := ((Λ.chr a.2 : X.Kˣ) : X.K) • C.rho a.1
  map_one' := by simp
  map_mul' a b := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Units.val_mul]
    rw [smul_mul_smul_comm]

open Classical in

@[reducible] def formGSD (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG) : GSD X.K where
  G := FormG Λ
  D := DecoSet X.E n ST SG
  actD := formAct Λ
  V := C.V
  ιV := VVIdx C.lam
  bV := C.bV
  pair := C.pair
  ρ := formRho C Λ
  Nab := C.Nab
  Del := C.Del

structure CoefPk.Eqv (C : CoefPk X n (DecoSet X.E n ST SG)) : Prop where
  nab_smul : ∀ (a : UF X.E n × GLG X.E n SG) (d : DecoSet X.E n ST SG),
    C.Nab (a • d) = (C.Nab d).map ((C.rho a.1).restrictScalars (𝓞 X.K))
  del_smul : ∀ (a : UF X.E n × GLG X.E n SG) (d : DecoSet X.E n ST SG),
    C.Del (a • d) = (C.Del d).map ((C.rho a.1).restrictScalars (𝓞 X.K))
  inv : ∀ (γ : UF X.E n) (x y : C.V), C.pair (C.rho γ x) (C.rho γ y) = C.pair x y

instance formModO (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG) :
    Module (𝓞 X.K) (formGSD C Λ).EqFun :=
  (fun S : GSD X.K => (inferInstance : Module (𝓞 X.K) S.EqFun)) (formGSD C Λ)

end Form

section Cols

variable {X : Fields} {Pr : Primes X} {R : Ranks}

def colLev (Ch : Chars X Pr R.m) (j : ℕ) : LevFam X.E X.K (R.N j) Pr.vGs := fun w =>
  if j < R.m then
    ⟨HX (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k R.t j,
      lamX (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.k R.m R.t j⟩
  else
    ⟨HXm (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.r R.t R.m,
      lamXm (Ch.psi0 w) (extChi fun s => Ch.chi s w) (R.N j) R.r R.t R.m⟩

variable (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)

@[reducible] def colGSD (u : Pr.Word) (j : ℕ) : GSD X.K :=
  formGSD (colVal W u j (Pr.vT u) Pr.vGs) (colLev Ch j)

abbrev ColV (u : Pr.Word) (j : ℕ) : Submodule X.K ((colGSD W Ch u j).D → (colGSD W Ch u j).V) :=
  (colGSD W Ch u j).EqFun

def ColL (u : Pr.Word) (j : ℕ) : Submodule (𝓞 X.K) (ColV W Ch u j) := (colGSD W Ch u j).intDel

def ColLnab (u : Pr.Word) (j : ℕ) : Submodule (𝓞 X.K) (ColV W Ch u j) := (colGSD W Ch u j).intNab

@[reducible] def ColCSD (u : Pr.Word) (j : ℕ) (h : (colGSD W Ch u j).Ok) : CSD X.K := (colGSD W Ch u j).toCSD h

abbrev MfV (u : Pr.Word) : Submodule X.K ((colGSD W Ch u 0).D → (colGSD W Ch u 0).V) := ColV W Ch u 0

def MfL (u : Pr.Word) : Submodule (𝓞 X.K) (MfV W Ch u) := ColL W Ch u 0

end Cols

end Formalism.L2.Col
