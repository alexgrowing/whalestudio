import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementJ
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColR
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

theorem pair_value_eq {D : D7} {p : ℕ} [Fact p.Prime] {ι : ℂ ≃+* ℂ_[p]} {th : ℂ_[p]} (hth : th ≠ 0)
    {z₁ z₂ : Bool × HH D} {s₁ s₂ : D.host.E} (h₁ : ‖rho D ι z₁ s₁‖ = 1) (h₂ : ‖rho D ι z₂ s₂‖ = 1)
    (hc : ‖rho D ι z₁ (D.host.conj s₂) - rho D ι z₂ s₂‖ ≤ ‖th‖) {N : ℕ} {a b : Fin N} {X : D.host.E}
    (hX : X = s₁ * D.host.conj s₂ * (if a = b then 1 else 0)) :
    ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ (rho D ι z₁ s₁)⁻¹ * rho D ι z₁ X * (rho D ι z₂ s₂)⁻¹ =
      (if a = b then 1 else 0) + th * e := by
  have n₁ : rho D ι z₁ s₁ ≠ 0 := fun h => by simp [h] at h₁
  have n₂ : rho D ι z₂ s₂ ≠ 0 := fun h => by simp [h] at h₂
  by_cases hab : a = b
  · refine ⟨(rho D ι z₁ (D.host.conj s₂) - rho D ι z₂ s₂) / (rho D ι z₂ s₂ * th), ?_, ?_⟩
    · rw [norm_div, norm_mul, h₂, one_mul]
      exact div_le_one_of_le₀ hc (norm_nonneg _)
    · subst hX
      simp only [hab, if_true, mul_one, map_mul]
      field_simp
      ring
  · refine ⟨0, by simp, ?_⟩
    subst hX
    simp [hab]

theorem sum_pc_pc {D : D7} {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {N : ℕ}
    (σ : Bool × HH D → 𝓞 D.host.E) (z₁ z₂ : Bool × HH D) (a₁ a₂ : Fin N)
    (F : (Bool × HH D) × Fin N → (Bool × HH D) × Fin N → ℂ_[p]) :
    ∑ l, ∑ l₂, pc D ι σ z₁ l a₁ * F l l₂ * pc D ι σ z₂ l₂ a₂ =
      (rho D ι z₁ (σ z₁ : D.host.E))⁻¹ * F (z₁, a₁) (z₂, a₂) * (rho D ι z₂ (σ z₂ : D.host.E))⁻¹ := by
  rw [Finset.sum_eq_single (z₁, a₁), Finset.sum_eq_single (z₂, a₂)]
  · simp [pc]
  · intro b _ hb; simp [pc, hb]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb; simp [pc, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem dual_local_bases_pair : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (th : ℂ_[p]), th ≠ 0 → (∀ (t : HH D) (y : 𝓞 D.host.E), ‖GlobalTheory.DFrame.rho D ι (false, t) (D.host.conj (y : D.host.E)) - GlobalTheory.DFrame.rho D ι (true, t) (y : D.host.E)‖ ≤ ‖th‖) → ∀ {N : ℕ} (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (σ : Bool × HH D → 𝓞 D.host.E), (∀ z, ‖GlobalTheory.DFrame.rho D ι z (σ z : D.host.E)‖ = 1) → (∀ t, ((P (tauPl D (true, t))).map D.host.conj).transpose * P (tauPl D (false, t)) = 1) → (∀ (t : HH D) (a₁ a₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ l, ∑ l₂, GlobalTheory.DFrame.pc D ι σ (false, t) l a₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ j, GlobalTheory.DFrame.rowL D P σ l j * D.host.conj (GlobalTheory.DFrame.rowL D P σ l₂ j)) * GlobalTheory.DFrame.pc D ι σ (true, t) l₂ a₂ = (if a₁ = a₂ then 1 else 0) + th * e) ∧ (∀ (t : HH D) (b₁ b₂ : Fin N), ∃ e : ℂ_[p], ‖e‖ ≤ 1 ∧ ∑ r₁, ∑ r₂, GlobalTheory.DFrame.pc D ι σ (false, t) r₁ b₁ * GlobalTheory.DFrame.rho D ι (false, t) (∑ i, GlobalTheory.DFrame.colR D P σ r₁ i * D.host.conj (GlobalTheory.DFrame.colR D P σ r₂ i)) * GlobalTheory.DFrame.pc D ι σ (true, t) r₂ b₂ = (if b₁ = b₂ then 1 else 0) + th * e) := by
  intro D p _ ι th hth h2 N P σ hσ hP
  have key : ∀ t : HH D, (P (tauPl D (false, t)))⁻¹ = ((P (tauPl D (true, t))).map D.host.conj).transpose ∧
      (P (tauPl D (true, t)))⁻¹ * P (tauPl D (true, t)) = 1 := by
    intro t
    have h := hP t
    refine ⟨Matrix.inv_eq_left_inv h, ?_⟩
    apply Matrix.nonsing_inv_mul
    have hd := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hd
    have hd' : (P (tauPl D (true, t))).det ≠ 0 := by
      intro h0
      have : ((P (tauPl D (true, t))).map D.host.conj).det = D.host.conj (P (tauPl D (true, t))).det := by
        simpa using (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) (P (tauPl D (true, t)))).symm
      rw [this, h0] at hd
      simp at hd
    exact isUnit_iff_ne_zero.mpr hd'
  refine ⟨fun t a₁ a₂ => ?_, fun t b₁ b₂ => ?_⟩
  · rw [sum_pc_pc ι σ (false, t) (true, t) a₁ a₂
      (fun l l₂ => rho D ι (false, t) (∑ j, rowL D P σ l j * D.host.conj (rowL D P σ l₂ j)))]
    refine pair_value_eq hth (hσ _) (hσ _) (h2 t (σ (true, t))) ?_
    obtain ⟨k₁, k₂⟩ := key t
    have e := congrFun (congrFun k₂ a₂) a₁
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    have e' := congrArg D.host.conj e
    simp only [rowL, k₁, map_mul, map_sum, Matrix.transpose_apply, Matrix.map_apply] at e' ⊢
    have e'' : D.host.conj (if a₂ = a₁ then 1 else 0) = if a₁ = a₂ then 1 else 0 := by
      by_cases h : a₁ = a₂
      · simp [h]
      · simp [h, Ne.symm h]
    rw [← e'', ← e', Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  · rw [sum_pc_pc ι σ (false, t) (true, t) b₁ b₂
      (fun l l₂ => rho D ι (false, t) (∑ i, colR D P σ l i * D.host.conj (colR D P σ l₂ i)))]
    refine pair_value_eq hth (hσ _) (hσ _) (h2 t (σ (true, t))) ?_
    have e := congrFun (congrFun (hP t) b₂) b₁
    rw [Matrix.mul_apply, Matrix.one_apply] at e
    simp only [Matrix.transpose_apply, Matrix.map_apply] at e
    simp only [colR, map_mul]
    have e'' : (if b₂ = b₁ then (1 : D.host.E) else 0) = if b₁ = b₂ then 1 else 0 := by
      by_cases h : b₁ = b₂
      · simp [h]
      · simp [h, Ne.symm h]
    rw [← e'', ← e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

end GlobalTheory.DFrame
