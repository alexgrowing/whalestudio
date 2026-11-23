import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationBigCellRelationFourier
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilRepresentation_bigCell_relation_fourier : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ κ : ℂ, κ ≠ 0 ∧ ∀ p ∈ sieg c ν, InCell c (weyl c ν * p * weyl c ν) → ∃ p₁ ∈ sieg c ν, ∃ p₂ ∈ sieg c ν, weyl c ν * p * weyl c ν = p₁ * weyl c ν * p₂ ∧ ∀ φ ∈ SB (Matrix α ν E), κ • fou c ψ Q μ (parFun c ψ χ Q (mat c p) (κ • fou c ψ Q μ φ)) = parFun c ψ χ Q (mat c p₁) (κ • fou c ψ Q μ (parFun c ψ χ Q (mat c p₂) φ)) := by
  first | exact @GlobalTheory.KSp.weyl_cell_relation | exact GlobalTheory.KSp.weyl_cell_relation | (intros; apply GlobalTheory.KSp.weyl_cell_relation <;> assumption)
