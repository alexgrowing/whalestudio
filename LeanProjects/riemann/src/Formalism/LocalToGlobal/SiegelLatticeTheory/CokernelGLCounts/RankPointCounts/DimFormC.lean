import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KappaOffDiagonal
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Attr

variable {D : D7} {X : HidaSetting D}

abbrev GTu (Y : Full X) (u : D.what₂.Word) : Type :=
  GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)

def jT {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) : ℕ :=
  D.R.rS - Module.finrank D.host.E (Isp (lf D (X.Fu u)).fl (frq X t.rep).fl)

def labT {Y : Full X} {u : D.what₂.Word} (t : GTu Y u) : ℕ → D.host.E :=
  fun l => if l ≤ jT t then Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l else 0

def relSet (Y : Full X) (u : D.what₂.Word) : Set (GTu Y u) := (Y.tO u u).degSet ∩ {t | t.relevant}

def massC (Y : Full X) (u : D.what₂.Word) : ℝ := massRows D (X.Fu u) (Y.what₂ u)

def dpiC (X : HidaSetting D) (u : D.what₂.Word) : ℝ := (Module.finrank ℂ (X.Vpi u) : ℝ)

def H1C (large₂ : SizeData₂ D) (CH : ℝ) : ℝ := large₂.sc.b ^ (CH * (D.R.m : ℝ))

end Attr

section Steps

def TypeAt {D : D7} (large₂ : SizeData₂ D) {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) (CH Cs C Ch Cp : ℝ) : Prop :=
  ∀ j' ∈ Finset.Icc 1 D.R.rS, ∀ j'' ∈ Finset.Icc 1 D.R.rS, ∀ (δ' δ'' : ℕ → D.host.E) (S : Finset (GTu Y u × GTu Y u)),
    (∀ p ∈ S, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ jT p.1 = j' ∧ jT p.2 = j'' ∧ labT p.1 = δ' ∧ labT p.2 = δ'') →
    ∑ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≤
      dpiC X u * massC Y u * ((k2a large₂ CH Cs C j' δ' * k2e large₂ CH Ch Cp j' δ') *
        (k2a large₂ CH Cs C j'' δ'' * k2e large₂ CH Ch Cp j'' δ''))

def IrrVecC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
    FundExists X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) →
    OOIntAll X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) →
    ∀ t ∈ (Y.tO u u).degSet, ¬ t.relevant → (Y.tO u u).vec t = 0

def JPosC : Prop :=
  ∀ (Cg cb Cw cT CT C0 C' Cl : ℝ) (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
    Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.RowsConc.ConcTie X Y →
    ∀ t ∈ relSet Y u, 1 ≤ jT t

def TypeC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ CH Ch Cp : ℝ, 0 ≤ CH ∧ 0 ≤ Ch ∧ 0 ≤ Cp ∧ ∀ Cs : ℝ, Cp + 4 ≤ Cs → ∃ C₀ : ℝ,
    ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
      ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
        Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.RowsConc.ConcTie X Y →
        TypeAt large₂ Y u CH Cs C Ch Cp

def DelC : Prop :=
  ∀ Cg cb Cw cT CT C0 CH : ℝ, 0 ≤ CH → ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.RowsConc.ConcTie X Y →
      ∀ t ∈ relSet Y u, 0 < k2Del D (jT t) (labT t) ∧
        k2Del D (jT t) (labT t) ≤ Hb large₂.sc.b C D.R.m D.R.f * k2S D (H1C large₂ CH) (jT t) (labT t) ^ 2

def CosetsC : Prop :=
  ∀ Cg cb Cw cT CT C0 CH : ℝ, 0 ≤ CH → ∃ Cc : ℝ, 0 ≤ Cc ∧ ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.RowsConc.ConcTie X Y →
      ∀ j ∈ Finset.Icc 1 D.R.rS, ∀ T : Finset (ℕ → D.host.E),
        (∀ δ ∈ T, ∃ t ∈ relSet Y u, jT t = j ∧ labT t = δ) →
        ∑ δ ∈ T, k2S D (H1C large₂ CH) j δ ^ (-(3 * (D.R.rS : ℝ))) ≤ Hb large₂.sc.b Cc D.R.m D.R.f ^ (Cc * (D.R.rS : ℝ))

def DimFormC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Formalism.L2.SG.RowsConc.ConcTie X Y →
    0 ≤ (Y.tO u u).Gam1 ∧ (Y.tO u u).Gam1 * massC Y u * dpiC X u ≤ Formalism.L2.SG.RowsConc.duC X Y u

def PgLeC : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X),
      Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 → Formalism.L2.SG.RowsConc.PgC Y ≤ 2

end Steps

end Formalism.L2.SG.KappaOffDiagonal
