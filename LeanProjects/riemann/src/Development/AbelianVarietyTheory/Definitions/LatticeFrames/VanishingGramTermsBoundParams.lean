import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.LocalRingCardinality.DataTies

noncomputable section
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2
namespace GlobalTheory.Core.Deg

def HypL (D : D7) (L C' Cl Cg cb Cu cT CT : ℝ) : Prop :=
  let k : ℝ := D.R.k
  let m : ℝ := D.R.m
  let f : ℝ := D.R.f
  let n : ℝ := D.R.r
  let r : ℝ := D.R.rS
  let b : ℝ := Real.exp L
  let Del : ℝ := D.s.Del
  let g1 : ℝ := D.host.g 0
  let g2 : ℝ := D.host.g 1
  1 < L ∧ C' * m ^ 5 * f * L ≤ k ∧
  D.R.m ^ 4 ≤ D.R.f ∧ D.R.f ≤ D.R.k ∧
  Real.log f ≤ Real.sqrt r ∧
  Cl * L ≤ f * Real.log k ∧
  Cl * (m ^ 2 * L) ≤ k ∧
  (∀ τ j, 1 ≤ j → j ≤ D.R.m → Cl * (m * k * Del) ≤ bOne D τ j) ∧
  Cl * (m * Real.log D.host.v) ≤ k ∧
  Cl * (m ^ 3 * L * Real.log D.host.rdE) ≤ k * Real.log k ^ 2 ∧
  Real.log D.host.rdE ≤ L / Cl ∧
  (k * b) ^ 8 ≤ g1 ∧ g1 ≤ b ^ Cg ∧ (k * b) ^ 8 ≤ g2 ∧ g2 ≤ b ^ Cg ∧
  (∀ τ j, 1 ≤ j → j ≤ D.R.m → max (k ^ Cl) (b ^ cb) ≤ bOne D τ j ∧ bOne D τ j ≤ b ^ (2 : ℝ)) ∧
  (∀ τ, bOne D τ D.R.m ≤ 2 * bOne D τ 1) ∧
  (∀ u τ, uOne D u τ 1 ≤ b ^ Cu) ∧
  1 ≤ D.host.v ∧
  (k * f * L) ^ Cl ≤ Del ∧
  (∀ τ j, 1 ≤ j → j + 1 ≤ D.R.m → Cl * n ^ 19 * f ^ 5 * L ≤ bOne D τ (j + 1) - bOne D τ j) ∧
  (∀ τ (i : Fin D.R.r) (h : i.1 + 1 < D.R.r),
    Cl * k * m ^ 4 + n * m ^ 10 < lamS D.R (D.hc τ) i - lamS D.R (D.hc τ) ⟨i.1 + 1, h⟩) ∧
  (∀ u, b ^ (cT * m) ≤ Tr D u ∧ Tr D u ≤ b ^ (CT * m)) ∧
  Cl ≤ m ∧ 0 < Cl

def DataNW (D : D7) : Prop :=
  let k : ℝ := D.R.k
  let Del : ℝ := D.s.Del
  (∀ τ l, 1 ≤ l → l ≤ D.R.k - 1 → 0 ≤ vOne D τ l ∧ vOne D τ l ≤ 4 * k * Del) ∧
  (∀ u (l : ℕ), 1 ≤ l → l ≤ D.R.k - 2 →
    (∀ τ, uOne D u τ (l + 1) = vOne D τ l - 1 / 2) ∨ (∀ τ, uOne D u τ (l + 1) = vOne D τ l - 1 / 2 - Del)) ∧
  (∀ u τ, 4 * k * Del ≤ uOne D u τ 1 - vOne D τ 1) ∧
  (∀ u τ, ¬ IsTop D τ → uOne D u τ 1 - vOne D τ 1 ≤ 8 * k * Del) ∧
  (∀ u τ, ¬ IsTop D τ → uOne D u τ D.R.k = vOne D τ (D.R.k - 1) - 1 / 2) ∧
  (∀ τ, IsTop D τ → 3 ≤ bOne D τ 1 - bTop D τ ∧ bOne D τ 1 / 2 ≤ bTop D τ) ∧
  (∀ u τ, InterlaceS (show D.R.k ≤ D.R.r by have := D.R.two_le_m; unfold Formalism.BasicNotions.Ranks.r; omega)
    (uS D u τ) (lamS D.R (D.hc τ))) ∧
  (∀ u u', u ≠ u' → ∀ τ, uS D u τ ≠ uS D u' τ) ∧
  (∀ u, SplitsE D (D.mem u).A.T ∧
    (D.mem u).A.T % (D.host.g 0 * D.host.g 1) ^ 2 = 1 % (D.host.g 0 * D.host.g 1) ^ 2) ∧
  (∀ u, 0 < D.duS u) ∧
  SplitsE D (D.host.g 0) ∧ SplitsE D (D.host.g 1) ∧
  NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 ∧
  (∀ u, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1)
section At
variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

def VanishingGramTermsBound : Prop :=
  Summable ((Y.tO u u).degSet.indicator (fun t => ‖(Y.tO u u).op t‖)) ∧
    ‖(Y.tO u u).part (Y.tO u u).degSet‖ ^ 2 ≤ duC X Y u * epsK D

def CollAt : Prop := (Y.tO u u).pairAbs ((Y.tO u u).big (Y.tO u u).nzSet) ≤ epsL D * (ddC X Y u u + duC X Y u)

def NscAt : Prop := (Y.tO u u).pairAbs ((Y.tO u u).nsc (Y.tO u u).genSet) ≤ epsL D * (ddC X Y u u + duC X Y u)
end At

def Free (Q : ∀ {D : D7} {X : HidaSetting D}, Full X → D.what₂.Word → Prop) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (L : ℝ) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (_ : SIso D.s (sOf hF)) (u : D.what₂.Word),
      Formalism.BasicNotions.Ties D → Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D → HypL D L C' Cl Cg cb Cu cT CT → DataNW D → ConcTie X Y →
      (Y.tO u u).AbsConv → Q Y u

def Led (Q : ∀ {D : D7} {X : HidaSetting D}, Full X → D.what₂.Word → Prop) : Prop :=
  ∀ Cg cb Cu cT CT : ℝ, 0 < cb → 0 < cT → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (_ : SIso D.s (sOf hF)) (u : D.what₂.Word),
      Formalism.BasicNotions.Ties D → Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → DataNW D → ConcTie X Y →
      (Y.tO u u).AbsConv → Q Y u

def Win (Q : ∀ {D : D7} {X : HidaSetting D}, Full X → D.what₂.Word → Prop) : Prop :=
  ∀ Cg cb Cu cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (_ : SIso D.s (sOf hF)) (u : D.what₂.Word),
      Formalism.BasicNotions.Ties D → Formalism.MainNotions.LocalBesselAndTopKernel.FamilyMidVolume D → Formalism.MainNotions.S.Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ConcTie X Y →
      (Y.tO u u).AbsConv → Q Y u

def VanishingGramBound : Prop := Free VanishingGramTermsBound

def CollBound : Prop := Free CollAt

def NscBound : Prop := Free NscAt

def VanishingGramTermsBoundParams : Prop := Led VanishingGramTermsBound

def CollLed : Prop := Led CollAt

def NscLed : Prop := Led NscAt

def VanishingGramTermsBoundWindow : Prop := Win VanishingGramTermsBound

def CollWin : Prop := Win CollAt

def NscWin : Prop := Win NscAt

theorem hypL_of {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (h : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT) :
    HypL D large₂.sc.L C' Cl Cg cb Cu cT CT :=
  ⟨Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos, h.2⟩

end GlobalTheory.Core.Deg
