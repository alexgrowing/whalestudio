import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure

noncomputable section
open MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Amp
namespace GlobalTheory.TypeAsm

def TailAt (D : D7) (large₂ : SizeData₂ D) (CH : ℝ) (C₁ : ℕ) : Prop :=
  ∀ (τ : D.what₂.Tau) (u : D.what₂.Word) (W : LocW D.R.k D.R.rS), GoodW D τ u u 1 W →
    ∀ A : LocS W, GoodS D (lamD D τ) A →
      TailBd W.z W.νS A.Φ (C₁ * D.R.k * D.R.rS) (large₂.sc.b ^ (CH * (D.R.m : ℝ))) ∧
      TailBd W.z' W.νS' A.Φ' (C₁ * D.R.k * D.R.rS) (large₂.sc.b ^ (CH * (D.R.m : ℝ)))

def TailP : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, 0 < cb → 0 < cT → ∃ CH : ℝ, 0 ≤ CH ∧ ∀ C₁ : ℕ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D), Formalism.BasicNotions.Ties D → Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 →
      (∀ w : D.what₂.Word, 1 ≤ Tr D w * Formalism.MainNotions.S.Bridge.kaS D ^ (2 * D.R.rS)) → TailAt D large₂ CH C₁

def MomAllP : Prop :=
  ∀ Ch : ℝ, 0 ≤ Ch → ∃ Cs Cq Cr C₂ : ℝ, 0 < Cq ∧ 0 < Cr ∧ 0 ≤ C₂ ∧ ∀ D : D7, Formalism.MainNotions.OnePlaceEstimates.SubmultiplicativeLocalNorm D Ch Cs Cq Cr C₂
end GlobalTheory.TypeAsm
