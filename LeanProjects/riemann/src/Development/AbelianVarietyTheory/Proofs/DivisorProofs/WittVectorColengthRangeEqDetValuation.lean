import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthQuotRangeEqAddValDet
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.ColenDet

theorem map_eq_unit_mul_pow {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    (ψ : ℤ_[p] →+* WittVector p k) {x : ℤ_[p]} (hx : x ≠ 0) :
    ψ x = ψ (PadicInt.unitCoeff hx : ℤ_[p]) * (p : WittVector p k) ^ x.valuation := by
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [map_mul, map_pow, map_natCast]

theorem addVal_map {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    (ψ : ℤ_[p] →+* WittVector p k) {x : ℤ_[p]} (hx : x ≠ 0) :
    IsDiscreteValuationRing.addVal (WittVector p k) (ψ x) = (x.valuation : ℕ∞) := by
  rw [map_eq_unit_mul_pow ψ hx, AddValuation.map_mul, AddValuation.map_pow,
    IsDiscreteValuationRing.addVal_uniformizer (WittVector.irreducible p),
    (IsDiscreteValuationRing.addVal_eq_zero_iff).mpr ((PadicInt.unitCoeff hx).isUnit.map ψ)]
  simp

theorem colength_det : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : Type) [AddCommGroup N] [Module (WittVector p k) N] [Module.Free (WittVector p k) N] [Module.Finite (WittVector p k) N] (ψ : ℤ_[p] →+* (WittVector p k)) (u : N →ₗ[(WittVector p k)] N) (d : ℤ_[p]), LinearMap.det u = ψ d → (∀ e : ℕ, Module.length (WittVector p k) (N ⧸ LinearMap.range u) = e → ‖d‖ = (p : ℝ) ^ (-(e : ℤ))) ∧ (¬ Function.Injective u → d = 0) ∧ Function.Injective ψ := by
  intro p _ k _ _ _ N _ _ _ _ ψ u d hdet
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have h1 := addVal_map ψ h0
    rw [hx, AddValuation.map_zero] at h1
    exact ENat.top_ne_coe _ h1
  have hlen := GlobalTheory.length_quot_range_eq_addVal_det u
  refine ⟨fun e he => ?_, fun hu => ?_, hψ⟩
  · rw [hlen, hdet] at he
    have hd : d ≠ 0 := by
      rintro rfl
      rw [map_zero, AddValuation.map_zero] at he
      exact ENat.top_ne_coe _ he
    rw [addVal_map ψ hd] at he
    have he' : d.valuation = e := by exact_mod_cast he
    rw [PadicInt.norm_eq_zpow_neg_valuation hd, he']
  · have h0 : LinearMap.det u = 0 := by
      by_contra h
      apply hu
      rwa [LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot] at h
    exact hψ (by rw [← hdet, h0, map_zero])

end GlobalTheory.Dieu.ColenDet
