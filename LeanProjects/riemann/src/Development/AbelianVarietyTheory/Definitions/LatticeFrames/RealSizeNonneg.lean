import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ENNReal

namespace GlobalTheory.Unf

variable {D : D7}

def realSize (θ : InfFam D) {m n : ℕ} (x : Mx D m n) : ℝ := ∑ τ, ∑ i, ∑ j, ‖compAt θ τ x i j‖

def InBox {m n : ℕ} (K : Set (Mx D m n)) (x : Mx D m n) : Prop := ∃ k ∈ K, (x - k).map (finPart D) = 0

open Classical in

def maj (θ : InfFam D) {m n : ℕ} (K : Set (Mx D m n)) (N : ℕ) (x : Mx D m n) : ℝ :=
  if InBox K x then ((1 + realSize θ x) ^ N)⁻¹ else 0

def supSob (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (d : ℕ) (f : WO S T → ℂ) : ℝ≥0∞ :=
  GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) (fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) d f

structure IsSobForm (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (ℓ : (WO S T → ℂ) → ℂ) : Prop where
  add : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ℓ (f + g) = ℓ f + ℓ g
  smul : ∀ (c : ℂ) f, IsThetaFunO ψ S T f → ℓ (c • f) = c * ℓ f
  bound : ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ (d : ℕ) (C : NNReal),
    ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ‖ℓ f‖ₑ ≤ C * supSob ψ θ d f

theorem realSize_nonneg (θ : InfFam D) {m n : ℕ} (x : Mx D m n) : 0 ≤ realSize θ x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem maj_nonneg (θ : InfFam D) {m n : ℕ} (K : Set (Mx D m n)) (N : ℕ) (x : Mx D m n) : 0 ≤ maj θ K N x := by
  unfold maj
  split_ifs
  · have := realSize_nonneg θ x; positivity
  · exact le_rfl

theorem isSobForm_eval (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) : IsSobForm ψ θ S T fun f => f 0 where
  add _ _ _ _ := rfl
  smul _ _ _ := rfl
  bound _ _ := ⟨0, 1, fun f _ => by
    rw [ENNReal.coe_one, one_mul]
    exact le_trans (le_iSup (fun w => ‖f w‖ₑ) 0)
      (GlobalTheory.Size.le_wordSum (A := GlobalTheory.Size.heisDer ψ θ) (p := fun φ : WO S T → ℂ => ⨆ w, ‖φ w‖ₑ) (l := []) le_rfl f)⟩

end GlobalTheory.Unf

end
