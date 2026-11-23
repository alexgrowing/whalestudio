import ReciprocityTheory.Chebotarev.EulerSum
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.UnitsEqOneOrNegOne
import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.LatITopBasis
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.IdealBasis
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.NormArea
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.Homothety

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

theorem exists_latI_basis (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime] (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (𝔞 : Ideal (𝓞 K))
    (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ a b : ℂ, 0 < ((starRingEnd ℂ) a * b).im ∧ latI φ 𝔞 1 = AddSubgroup.closure {a, b} ∧
      ((starRingEnd ℂ) a * b).im = (Ideal.absNorm 𝔞 : ℝ) * Real.sqrt d / 2 := by
  obtain ⟨a₀, b₀, h₀, hl₀, hc₀⟩ := latI_top_basis K d hd4 x hx hK φ
  obtain ⟨a, b, h, hl, hc⟩ := latI_basis K hK φ a₀ b₀ h₀ hl₀ 𝔞 h𝔞
  exact ⟨a, b, h, hl, by rw [hc, hc₀]; ring⟩

theorem discr_latI_ne_zero (K : Type) [Field K] [NumberField K] (d : ℕ) [Fact d.Prime] (hd4 : d % 4 = 3)
    (x : K) (hx : x ^ 2 = -(d : K)) (hK : Module.finrank ℚ K = 2) (φ : K →+* ℂ) (𝔞 : Ideal (𝓞 K)) (h𝔞 : 𝔞 ≠ ⊥) :
    discr (latI φ 𝔞 1) ≠ 0 := by
  obtain ⟨a, b, h, hl, -⟩ := exists_latI_basis K d hd4 x hx hK φ 𝔞 h𝔞
  rw [hl]; exact discr_closure_pair_ne_zero a b h

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
