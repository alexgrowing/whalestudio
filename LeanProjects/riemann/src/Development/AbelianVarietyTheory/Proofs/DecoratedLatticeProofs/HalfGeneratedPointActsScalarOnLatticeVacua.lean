import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfGenScalar

theorem addChar_ne_zero {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := by
  intro h
  have h1 : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem exists_scalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (z : WO S T),
    z ∈ AddSubgroup.closure {u | u ∈ Λ ∧ ∃ e, IsSplitIdem D e ∧ IsHalf e u} →
    ∃ c : ℂ, ∀ f, IsLatVac (heisO ψ S T) Λ f → heisO ψ S T z f = c • f := by
  intro D ψ S T Λ z hz
  induction hz using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨huΛ, e, he, hh⟩ := hu
    exact ⟨1, fun f hf => by rw [one_smul]; exact hf.2 e he u huΛ hh⟩
  | zero => exact ⟨1, fun f _ => by rw [one_smul]; exact GlobalTheory.SplitScalar.heisO_zero ψ S T f⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨cx, hcx⟩ := ihx
    obtain ⟨cy, hcy⟩ := ihy
    refine ⟨(ψ (symplOH S T x y))⁻¹ * (cx * cy), fun f hf => ?_⟩
    have h1 := GlobalTheory.SplitScalar.heisO_heisO ψ S T x y f
    rw [hcy f hf, GlobalTheory.SplitScalar.heisO_smul, hcx f hf, smul_smul] at h1
    have hne := addChar_ne_zero ψ (symplOH S T x y)
    rw [mul_smul, mul_comm cx cy, h1, smul_smul, inv_mul_cancel₀ hne, one_smul]
  | neg x _ ihx =>
    obtain ⟨cx, hcx⟩ := ihx
    by_cases h0 : cx = 0
    · refine ⟨0, fun f hf => ?_⟩
      have h1 := GlobalTheory.SplitScalar.heisO_heisO ψ S T (-x) x f
      rw [hcx f hf, h0, zero_smul, neg_add_cancel, GlobalTheory.SplitScalar.heisO_zero] at h1
      have hf0 : f = 0 := by
        have h2 : heisO ψ S T (-x) (0 : WO S T → ℂ) = 0 := by
          simpa using GlobalTheory.SplitScalar.heisO_smul ψ S T (-x) 0 (0 : WO S T → ℂ)
        rw [h2] at h1
        exact (smul_eq_zero.1 h1.symm).resolve_left (addChar_ne_zero ψ _)
      subst hf0
      rw [zero_smul]
      simpa using GlobalTheory.SplitScalar.heisO_smul ψ S T (-x) 0 (0 : WO S T → ℂ)
    · refine ⟨ψ (symplOH S T (-x) x) / cx, fun f hf => ?_⟩
      have h1 := GlobalTheory.SplitScalar.heisO_heisO ψ S T (-x) x f
      rw [hcx f hf, GlobalTheory.SplitScalar.heisO_smul, neg_add_cancel, GlobalTheory.SplitScalar.heisO_zero] at h1
      rw [div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ h0, one_smul]

end GlobalTheory.HalfGenScalar

end
