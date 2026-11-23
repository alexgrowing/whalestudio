import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.RiemHaarOfChartDens

noncomputable section

namespace PI.IwaMeasEx.Gauge.ZetaZeros

open MeasureTheory Topology Filter Set Metric
open scoped ENNReal NNReal Pointwise
open Formalism.MainNotions.S PI.IwaMeasEx.Gauge

variable {n : ℕ} {ε : Fin n → Bool}

def expSet1 (K : Subgroup (Formalism.REAL.UJ ε)) (T : Set (lieSp K)) : Set (Formalism.REAL.UJ ε) :=
  {g | ∃ x ∈ T, uMat g = NormedSpace.exp (toMat (x : MatR n))}

def ChartDens1 : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (K : Subgroup (Formalism.REAL.UJ ε)) (hc : IsClosed (K : Set (Formalism.REAL.UJ ε))),
    ∃ δ : ℝ, 0 < δ ∧ ∃ (j : lieSp K → ℝ≥0∞) (c : ℝ≥0∞), c ≠ 0 ∧ c ≠ ⊤ ∧
      Tendsto j (𝓝 0) (𝓝 c) ∧
      ∀ T : Set (lieSp K), MeasurableSet T → T ⊆ ball 0 δ → haarH K hc (expSet1 K T) = ∫⁻ x in T, j x

theorem mem_conjInv (H : Subgroup (Formalism.REAL.UJ ε)) (y g : Formalism.REAL.UJ ε) :
    g ∈ conjInv H y ↔ y * g * y⁻¹ ∈ H := by
  unfold conjInv
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    have e : y * (MulAut.conj y⁻¹).toMonoidHom h * y⁻¹ = h := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hh
  · intro hg
    refine ⟨y * g * y⁻¹, hg, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

def conjE (H : Subgroup (Formalism.REAL.UJ ε)) (y : Formalism.REAL.UJ ε) : H ≃ₜ* conjInv H y where
  toFun h := ⟨y⁻¹ * h * y, (mem_conjInv H y _).2 (by
    rw [show y * (y⁻¹ * (h : Formalism.REAL.UJ ε) * y) * y⁻¹ = h by group]
    exact h.2)⟩
  invFun k := ⟨y * k * y⁻¹, (mem_conjInv H y _).1 k.2⟩
  left_inv h := Subtype.ext (show y * (y⁻¹ * (h : Formalism.REAL.UJ ε) * y) * y⁻¹ = h by group)
  right_inv k := Subtype.ext (show y⁻¹ * (y * (k : Formalism.REAL.UJ ε) * y⁻¹) * y = k by group)
  map_mul' a b := Subtype.ext (show y⁻¹ * ((a : Formalism.REAL.UJ ε) * b) * y = (y⁻¹ * a * y) * (y⁻¹ * b * y) by group)
  continuous_toFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  continuous_invFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

end PI.IwaMeasEx.Gauge.ZetaZeros

end
