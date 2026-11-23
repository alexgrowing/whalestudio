import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasQExpansionModularForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQCoeffIffHasQExpansion

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators

namespace GlobalTheory.QFam

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in

theorem _root_.GlobalTheory.QFam.HasQ.mdifferentiable {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (hN : 0 < N)
    (h : _root_.GlobalTheory.QFam.HasQ N f a) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  have h' : _root_.GlobalTheory.QFam.HasQ N f (fun n => PowerSeries.coeff n (PowerSeries.mk a)) := by
    simpa only [PowerSeries.coeff_mk] using h
  exact ((_root_.GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion N f _).1 h').mdifferentiable (by exact_mod_cast hN)

theorem HasQ.isBoundedAtImInfty {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (hN : 0 < N) (h : HasQ N f a) :
    UpperHalfPlane.IsBoundedAtImInfty f :=
  (hasQ_powerSeries_bridge.1 N f a |>.1 h).isBoundedAtImInfty (Nat.cast_pos.mpr hN)

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in

theorem _root_.GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty :
    ∀ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < N → _root_.GlobalTheory.QFam.HasQ N f a →
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ UpperHalfPlane.IsBoundedAtImInfty f := by
  intro N f a hN h
  have h' : _root_.GlobalTheory.QFam.HasQ N f (fun n => PowerSeries.coeff n (PowerSeries.mk a)) := by
    simpa only [PowerSeries.coeff_mk] using h
  have hq := (_root_.GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion N f _).1 h'
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  exact ⟨hq.mdifferentiable hpos, hq.isBoundedAtImInfty hpos⟩

end GlobalTheory.QFam
