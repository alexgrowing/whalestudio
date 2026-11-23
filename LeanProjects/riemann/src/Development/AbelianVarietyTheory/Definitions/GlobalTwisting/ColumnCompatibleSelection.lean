import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SquareIntegrableColumnsCompatible
import Formalism.LocalToGlobal.ThresholdSelection
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
import Formalism.LocalToGlobal.IndefiniteReal.RealTB
import Formalism.LocalToGlobal.Divisibility.NumericScaleExponentEqExtended

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top

namespace GlobalTheory.Cp

abbrev BaseLevelCompatibleSelection (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    {P : Formalism.L2.Rows.RowSideFamily (Fm.ex x hx i) // Formalism.L2.Rows.RowSideDetermined ((sel Fm hc).2 x hx h i).T P}

abbrev SelDH (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    {p : ℕ × ℕ // (Fm.D x i).s.Del = (p.1 : ℚ) ∧ (Fm.L x i).etaSz = ((Fm.D x i).R.m : ℝ) * (p.2 : ℝ)}

abbrev ColumnCompatibleSelection (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) (selP : BaseLevelCompatibleSelection 𝒜 sel) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    SquareIntegrableColumnsCompatible ((sel Fm hc).2 x hx h i).T (selP Fm hc x hx h i).1

abbrev SelS (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    Formalism.L2.SG.SpectralTiesReal.STiesR ((sel Fm hc).2 x hx h i)

def ZscAt {𝒜 : FamClass} (sel : Formalism.L2.TSel 𝒜) (selP : BaseLevelCompatibleSelection 𝒜 sel) (selDH : SelDH 𝒜 sel) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm)
    (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x) :
    Formalism.L2.Indef.DefSub (selP Fm hc x hx h i).1.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale (selP Fm hc x hx h i).1.A3.fam3.base3 :=
  fun Zs =>
    let z := Formalism.L2.DIV.ZscOfNum3 (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0
      (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2) (Equiv.refl _) (Fm.L x i).Nc Zs
    { z with l6m := fun j => z.l6m j - Fm.Csz * z.l6u, l6u := 0 }

abbrev SelB (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) (selS : SelS 𝒜 sel) (selP : BaseLevelCompatibleSelection 𝒜 sel) (selDH : SelDH 𝒜 sel) (selC : ColumnCompatibleSelection 𝒜 sel selP) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    Formalism.IndefR.RealTB ((sel Fm hc).2 x hx h i) (selP Fm hc x hx h i).1 (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp
      (ZscAt sel selP selDH Fm hc x hx h i) (selS Fm hc x hx h i)

def EvSel {𝒜 : FamClass} (sel : Formalism.L2.TSel 𝒜) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm)
    (Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Prop) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x), x0 ≤ x → ∀ i : Fm.Ix x, Q x hx h i

end GlobalTheory.Cp

namespace GlobalTheory.Fc

open GlobalTheory.Cp

def zsc {D : D7} {O : Obj D} (P : Formalism.L2.Rows.RowSideFamily O.ex) (Del h0 : ℕ) (c : ℝ) :
    Formalism.L2.Indef.DefSub P.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale P.A3.fam3.base3 :=
  fun Zs =>
    let z := Formalism.L2.DIV.ZscOfNum3 P.A3 P.P0 P.ψ0 (Formalism.L2.DIV.ofRecord D O.L Del h0) (Equiv.refl _) O.L.Nc Zs
    { z with l6m := fun j => z.l6m j - c * z.l6u, l6u := 0 }

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure Bundle (D : D7) (O : Obj D) (c : ℝ) : Type 1 where
  R : Formalism.L2.RecT O.ex
  S : Formalism.L2.SG.SpectralTiesReal.STiesR R
  P : Formalism.L2.Rows.RowSideFamily O.ex
  pin : Formalism.L2.Rows.RowSideDetermined R.T P
  DH : {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)}
  C : SquareIntegrableColumnsCompatible R.T P
  B : Formalism.IndefR.RealTB R P C.c.face C.Sp (zsc P DH.1.1 DH.1.2 c) S

abbrev BdR : BdT := fun _ O _ => Formalism.L2.RecT O.ex

variable {𝒜 : FamClass} (σ : RawSel Bundle 𝒜)

def sel : Formalism.L2.TSel 𝒜 := fun Fm hc => ⟨Fm.x1, fun x hx _ i => (σ Fm hc x hx i).R⟩

def selS : SelS 𝒜 (sel σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).S

def selP : BaseLevelCompatibleSelection 𝒜 (sel σ) := fun Fm hc x hx _ i => ⟨(σ Fm hc x hx i).P, (σ Fm hc x hx i).pin⟩

def selDH : SelDH 𝒜 (sel σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).DH

def selC : ColumnCompatibleSelection 𝒜 (sel σ) (selP σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).C

def selB : SelB 𝒜 (sel σ) (selS σ) (selP σ) (selDH σ) (selC σ) := fun Fm hc x hx _ i => (σ Fm hc x hx i).B

end GlobalTheory.Fc

end
