import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize

namespace GlobalTheory.SumCount

section

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (C b : ℝ)

def DataNum : Prop := (Nat.card ch.G.Datum : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b)

def CosNum : Prop := ∀ Φ, ((ch.S.supp A.μ0 Φ).ncard : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b)

def PureNum : Prop := ∀ Φ, ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ τ,
  IsCosetExpansion ch.S.toGridChoice A.μ0 Φ β (expDepth ch.S.toGridChoice A.μ0 Φ β) τ →
    (τ.support.card : ℝ) ≤ Real.exp (D.R.m * aOne ch.G C b)

end

def DataK : Prop := BigC fun _ ch C b => DataNum ch C b

def CosK : Prop := BigC fun _ ch C b => CosNum ch C b

def PureK : Prop := BigC fun _ ch C b => PureNum ch C b

open IsDedekindDomain NumberField Matrix in

theorem _root_.GlobalTheory.SumCount.infCountK_of (h1 : _root_.GlobalTheory.SumCount.DataK)
    (h2 : _root_.GlobalTheory.SumCount.CosK) (h3 : _root_.GlobalTheory.SumCount.PureK) :
    _root_.GlobalTheory.SumSize.InfCountK := by
  unfold _root_.GlobalTheory.SumSize.InfCountK
  obtain ⟨s₁, h1⟩ := h1
  obtain ⟨s₂, h2⟩ := h2
  obtain ⟨s₃, h3⟩ := h3
  refine ⟨max s₁ (max s₂ s₃), fun CF hCF ↦ ?_⟩
  obtain ⟨C1, h1⟩ := h1 CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, h2⟩ := h2 CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨C3, h3⟩ := h3 CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max C1 (max C2 C3), fun ε C hC ↦ ?_⟩
  obtain ⟨x1, h1⟩ := h1 ε C (le_trans (le_max_left _ _) hC)
  obtain ⟨x2, h2⟩ := h2 ε C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC)
  obtain ⟨x3, h3⟩ := h3 ε C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC)
  refine ⟨max x1 (max x2 x3), fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hR ch hch hs hf ↦ ?_⟩
  have a1 := h1 D large₂ he (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hR ch hch hs hf
  have a2 := h2 D large₂ he (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx)
    Γ Pl0 T A Ks R F hR ch hch hs hf
  have a3 := h3 D large₂ he (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx)
    Γ Pl0 T A Ks R F hR ch hch hs hf
  exact ⟨a1, fun Φ ↦ ⟨a2 Φ, a3 Φ⟩⟩

end GlobalTheory.SumCount

end
