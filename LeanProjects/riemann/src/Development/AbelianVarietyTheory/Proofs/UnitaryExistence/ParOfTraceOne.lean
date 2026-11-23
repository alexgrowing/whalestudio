import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.TorusAtExists
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SymmetricMeasureL2NormEqResolutionL2
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsGeneratorsLattice

noncomputable section

namespace GlobalTheory.TorusFrameRigid

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E]

def hfR (ι : Type) [Fintype ι] : EuclideanSpace ℂ ι →ₗ[ℝ] EuclideanSpace ℂ ι →ₗ[ℝ] ℂ :=
  LinearMap.mk₂ ℝ Hf
    (fun u v w => by simp [Hf, add_mul, Finset.sum_add_distrib])
    (fun c u v => by simp [Hf, Finset.mul_sum, mul_assoc])
    (fun u v w => by simp [Hf, mul_add, Finset.sum_add_distrib])
    (fun c u v => by simp [Hf, Finset.mul_sum, mul_left_comm])

def actR (dim : (E →+* ℂ) → ℕ) (α : 𝓞 E) : Vsp dim →ₗ[ℝ] Vsp dim where
  toFun := act α
  map_add' := GlobalTheory.TupleSumPos.act_add_vec α
  map_smul' c v := by ext i; simp [act, mul_left_comm]

structure Match (Y Y' : PT E) (ψ : Vsp Y.dim ≃ₗ[ℝ] Vsp Y'.dim) : Prop where
  lat : ∀ y, y ∈ Y.L ↔ ψ y ∈ Y'.L
  act : ∀ α y, ψ (act α y) = act α (ψ y)
  herm : (∀ u v, Hf (ψ u) (ψ v) = Hf u v) ∨ ∀ u v, Hf (ψ u) (ψ v) = conj (Hf u v)

variable {Y Y' : PT E} {ψ : Vsp Y.dim ≃ₗ[ℝ] Vsp Y'.dim}

variable [IsCMField E] {r : ℕ} {X : Data E r} {x : Frame X.Ψ r}

open GlobalTheory.SemicharIndep

def EpsBy (Y : PT E) (w : 𝓞 E) : Prop := ∀ y ∈ Y.L, (Y.eps y : ℝ) = Real.cos (Real.pi * (Hf y (act w y)).im)

omit [IsCMField E] in
theorem Match.eps (h : Match Y Y' ψ) {w : 𝓞 E} (he : EpsBy Y w) (he' : EpsBy Y' w) :
    ∀ y ∈ Y.L, Y'.eps (ψ y) = Y.eps y := fun y hy => by
  have : (Y'.eps (ψ y) : ℝ) = Y.eps y := by
    rw [he y hy, he' _ ((h.lat y).1 hy), ← h.act]
    rcases h.herm with h1 | h1 <;> simp [h1]
  exact_mod_cast this

end GlobalTheory.TorusFrameRigid
