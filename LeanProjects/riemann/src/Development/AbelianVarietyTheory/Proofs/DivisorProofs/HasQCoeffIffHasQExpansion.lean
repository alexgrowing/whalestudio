import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasQExpansionModularForm

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

namespace GlobalTheory.QFam

theorem hasQ_iff_hasQExpansion_mk (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) :
    HasQ N f a ↔ GlobalTheory.HasQExpansion (N : ℝ) f (PowerSeries.mk a) := by
  rw [hasQ_iff]
  simp only [GlobalTheory.HasQExpansion, Function.Periodic.qParam, PowerSeries.coeff_mk,
    Complex.ofReal_natCast]

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in

theorem _root_.GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion (N : ℕ) (f : ℍ → ℂ) (φ : PowerSeries ℂ) :
    _root_.GlobalTheory.QFam.HasQ N f (fun n => PowerSeries.coeff n φ) ↔
      _root_.GlobalTheory.HasQExpansion (N : ℝ) f φ := by
  rw [_root_.GlobalTheory.QFam.hasQ_iff]
  unfold _root_.GlobalTheory.HasQExpansion
  simp only [Function.Periodic.qParam, Complex.ofReal_natCast]

theorem hasQ_powerSeries_bridge :
    (∀ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ),
      HasQ N f a ↔ GlobalTheory.HasQExpansion (N : ℝ) f (PowerSeries.mk a)) ∧
    (∀ (N : ℕ) (f : ℍ → ℂ) (φ : PowerSeries ℂ),
      HasQ N f (fun n => PowerSeries.coeff n φ) ↔ GlobalTheory.HasQExpansion (N : ℝ) f φ) :=
  ⟨hasQ_iff_hasQExpansion_mk, hasQ_coeff_iff_hasQExpansion⟩

end GlobalTheory.QFam
