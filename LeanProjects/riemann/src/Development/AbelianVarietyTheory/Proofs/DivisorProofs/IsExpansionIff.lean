import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest

namespace GlobalTheory.DepthUnf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def flatProd (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t)
    (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
    (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) : ℂ :=
  ∏ w, (S.term t Φ β w).datum (S.colAt t w x) (S.rowAt t w y)

def DepthOK (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (K : ℕ) : Prop :=
  (∀ (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (∀ j, IsHalf e (x j)) → (∀ i, IsHalf e (y i)) → flatProd S t Φ β x y ≠ 0 →
        (∀ j : Fin D.R.m, K • x j ∈ pairLat G (.top t j)) ∧ ∀ i : Fin D.R.m, K • y i ∈ pairLat G (.chi i D.R.m)) ∧
  ∀ (x u : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
    (y v : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
    (∀ j, IsHalf e (x j)) → (∀ i, IsHalf e (y i)) → (∀ j : Fin D.R.m, IsHalf e (u j) ∧ u j ∈ pairLat G (.top t j)) →
      (∀ i : Fin D.R.m, IsHalf e (v i) ∧ v i ∈ pairLat G (.chi i D.R.m)) → flatProd S t Φ β (x + K • u) (y + K • v) = flatProd S t Φ β x y

def ExpWith (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) (τ : PureDat G t →₀ ℂ) : Prop :=
  (∀ d ∈ τ.support, (∀ j, (d.1 j).P = locPl G t ∧ (d.1 j).e = e ∧ (d.1 j).z = 1) ∧
      ∀ i, (d.2 i).P = locPl G t ∧ (d.2 i).e = e ∧ (d.2 i).z = 1) ∧
    ∀ (x : ∀ j : Fin D.R.m, WO (G.V (.top j)) (G.V (.top (j + 1))))
      (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (∀ j, IsHalf e (x j)) → (∀ i, IsHalf e (y i)) →
        (τ.sum fun d c => c * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i)) = flatProd S t Φ β x y

example (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (e : AE D) : DepthOK S t Φ β e 0 :=
  ⟨fun _ _ _ _ _ => ⟨fun _ => by rw [zero_smul]; exact zero_mem _, fun _ => by rw [zero_smul]; exact zero_mem _⟩,
    fun x u y v _ _ _ _ => by simp only [zero_smul, add_zero]⟩

end GlobalTheory.DepthUnf

end
