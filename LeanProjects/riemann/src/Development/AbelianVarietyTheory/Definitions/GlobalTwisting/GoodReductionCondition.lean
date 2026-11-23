import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DRS
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.Divisors.MapBaseTiedSel
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl

namespace GlobalTheory.Fc.RL

open GlobalTheory.Fc

variable (Q : V4.Slot) (Lk : LkT Bundle)

def Row_tie : Prop := Row Q Lk (AtAll HasTie)

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2 in

def LabelCondition : Prop := Row Q Lk (AtAll fun D _ _ _ => ∃ (X : HidaSetting D) (G : GoodOp X) (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X),
  AutTie D X.B X.pl ∧ RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι)

def GoodReductionCondition : Prop := Row Q Lk (Ind.EvW (Bd := Bundle) fun D _ _ _ => Formalism.BasicNotions.GoodFTAll D)

def GeometricBoundCondition (CF : ℝ) : Prop := Row Q Lk (AtAll fun D O c (b : Bundle D O c) => ∃ t : b.Comparison₂, Ind.PIota D O c (b.part t) ∧
  GlobalTheory.ExportPin.ClassSumPin (b.part t).pt ∧ (b.part t).pt.Ties ∧ GlobalTheory.CovTop.RecTied D O.L ∧ GlobalTheory.BigOn.More (b.part t).pt ∧
  GlobalTheory.BigTop.Fun.HasGrid @GlobalTheory.BigTop.Fun.Fld (b.part t).pt CF)

def MultiplicityCondition' : Prop := Row Q Lk (Ind.EvW (Bd := Bundle) fun _ _ _ b =>
  (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE)

def KappaCondition : Prop := Row Q Lk (Ind.EvW (Bd := Bundle) fun _ _ _ b => Formalism.L2.Rows.RowsHoldKap3 b.P)

def DifferentialCondition : Prop := Row Q Lk (Ind.EvWC (Bd := Bundle) (fun _ => True) fun C CH D O c b => DRS D O c b C CH)

variable {hL : GlobalTheory.Published.LocalLanglandsGL}

def At (p : Prm hL) (r : V4.Slot → LkT Bundle → Prop) : Prop :=
  Lg1 KPx (IsBuiltE p.s) (IsGoodE p.s) fun S => r S (IsLinked p)

theorem At.of_row {p : Prm hL} {H : ∀ 𝒜 : FamClass, RawSel Bundle 𝒜 → Prop} (h : Row (IsGoodE p.s) (IsLinked p) H) :
    At p fun S L => Row S L H :=
  ⟨fun _ _ _ _ _ => True, largeBaseProperty_true, h.strengthen fun _ _ _ _ _ t => t.1⟩

structure Open (p : Prm hL) (N : FamClass → Prop) : Prop where
  hPA : At p R1.PeriodAdmissibilityAtBundlePoints
  hLamP : At p R1.LambdaPositivityAtBundlePoints
  hDivG : At p R1.DivisorConditionAtBundlePoints
  hDcPtG : At p R1.DecompositionConditionAtBundlePoints
  selJ : At p R1.JSelectionAtBundlePoints
  tie : At p Row_tie
  lab : At p LabelCondition
  good : At p GoodReductionCondition
  geo : ∀ CF0 : ℝ, ∃ CF, CF0 ≤ CF ∧ At p fun S L => GeometricBoundCondition S L CF
  mi : At p MultiplicityCondition'
  kap : At p KappaCondition
  df : At p DifferentialCondition
  nRest : At p fun S L => R1.PredicateAtBundlePoints S L N

end GlobalTheory.Fc.RL

end
