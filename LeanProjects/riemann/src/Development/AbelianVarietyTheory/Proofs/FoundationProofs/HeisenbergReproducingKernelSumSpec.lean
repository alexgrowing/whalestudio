import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableExpNegHermStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta.KerSum

theorem exists_bound {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (H : Sesq V) : ∃ M : ℝ, 0 ≤ M ∧ ∀ u v, ‖H u v‖ ≤ M * ‖u‖ * ‖v‖ := by
  let B : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ (fun u v => H u v)
    (fun a b c => by simp)
    (fun c a b => by
      rw [← Complex.coe_smul, map_smul, LinearMap.smul_apply, Complex.coe_smul])
    (fun a b c => by simp)
    (fun c a b => by
      rw [← Complex.coe_smul, LinearMap.map_smulₛₗ, Complex.conj_ofReal, Complex.coe_smul])
  let B' : V →L[ℝ] V →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℂ) ≃ₗ[ℝ] (V →L[ℝ] ℂ)).toLinearMap ∘ₗ B)
  exact ⟨‖B'‖, norm_nonneg _, fun u v => B'.le_opNorm₂ u v⟩

theorem norm_kerTerm_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (H : Sesq V) {M R : ℝ} (hM : 0 ≤ M) (hB : ∀ u v, ‖H u v‖ ≤ M * ‖u‖ * ‖v‖) (x w z : V)
    (hw : ‖w‖ ≤ R) :
    ‖kerTerm H x w z‖ ≤ Real.exp (π * (M * R * ‖z‖)) *
      Real.exp (-(π / 2) * (H x x).re + (π * (M * ‖z‖ + M * R)) * ‖x‖) := by
  rw [kerTerm, Complex.norm_exp, ← Real.exp_add, Real.exp_le_exp]
  have h1 : (H w z).re ≤ M * R * ‖z‖ :=
    ((Complex.re_le_norm _).trans (hB w z)).trans (by gcongr)
  have h2 : (H x z).re ≤ M * ‖x‖ * ‖z‖ := (Complex.re_le_norm _).trans (hB x z)
  have h3 : -(H w x).re ≤ M * R * ‖x‖ :=
    (((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans (hB w x)).trans (by gcongr)
  have e : ((π : ℂ) * H (w + x) z - (π : ℂ) * H w x - (π : ℂ) * H x x / 2).re
      = π * ((H w z).re + (H x z).re + -(H w x).re) - π / 2 * (H x x).re := by
    simp; ring
  rw [e]
  have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add h1 h2) h3) Real.pi_pos.le
  linarith

theorem differentiable_kerTerm {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (H : Sesq V) (x z : V) :
    Differentiable ℂ (fun w => kerTerm H x w z) := by
  have h : ∀ v, Differentiable ℂ (fun w => H w v) := fun v =>
    (LinearMap.toContinuousLinearMap (H.flip v)).differentiable
  have e : (fun w => kerTerm H x w z) = fun w =>
      cexp ((π : ℂ) * (H w z + H x z) - (π : ℂ) * H w x - (π : ℂ) * H x x / 2) := by
    funext w; simp [kerTerm]
  rw [e]
  exact (((((h z).add_const _).const_mul _).sub ((h x).const_mul _)).sub_const _).cexp

theorem kerTerm_shift {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V)
    (hH : ∀ z w, H z w = conj (H w z)) (x y w z : V) :
    kerTerm H x (w + y) z * cexp (-(π : ℂ) * H w y - (π : ℂ) * H y y / 2)
      = cexp (-((π : ℂ) * I) * ((H y x).im : ℂ)) * kerTerm H (y + x) w z := by
  have h : I * ((H y x).im : ℂ) = (H y x - H x y) / 2 := by
    rw [hH x y, Complex.sub_conj]; push_cast; ring
  rw [kerTerm, kerTerm, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [map_add, LinearMap.add_apply]
  linear_combination (π : ℂ) * h

theorem kerSum_spec : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [DiscreteTopology Λ] (α : V → ℂ), IsSemichar H Λ α → (∀ w z, Summable (fun x : Λ => α x * kerTerm H x w z)) ∧ (∀ z, Differentiable ℂ (kerSum H Λ α z)) ∧ ∀ z, ∀ y ∈ Λ, ∀ w, α y * Heisenberg₂ H y (kerSum H Λ α z) w = kerSum H Λ α z w := by
  intro V _ _ _ H hH Λ _ α hα
  obtain ⟨M, hM, hB⟩ := exists_bound H
  have hn : ∀ x : Λ, ‖α x‖ = 1 := fun x => by
    rcases hα.1 x x.2 with h | h <;> simp [h]
  have key : ∀ (z : V) (R : ℝ), ∃ u : Λ → ℝ, Summable u ∧
      ∀ (x : Λ) (w : V), ‖w‖ ≤ R → ‖α x * kerTerm H x w z‖ ≤ u x := fun z R =>
    ⟨_, (GlobalTheory.T.summable_exp_neg_herm_add_norm V H hH Λ (π * (M * ‖z‖ + M * R))).mul_left (Real.exp (π * (M * R * ‖z‖))),
      fun x w hw => by
        rw [norm_mul, hn, one_mul]
        exact norm_kerTerm_le H hM hB x w z hw⟩
  refine ⟨fun w z => ?_, fun z => ?_, fun z y hy w => ?_⟩
  · obtain ⟨u, hu, h⟩ := key z ‖w‖
    exact Summable.of_norm_bounded hu fun x => h x w le_rfl
  · refine differentiableOn_univ.1 (GlobalTheory.SCV.differentiableOn_tsum_of_locally_normal isOpen_univ
      (F := fun (x : Λ) w => α x * kerTerm H x w z)
      (fun x => ((differentiable_kerTerm H x z).const_mul _).differentiableOn) fun w _ => ?_)
    obtain ⟨u, hu, h⟩ := key z (‖w‖ + 1)
    refine ⟨Metric.ball w 1, Metric.ball_mem_nhds w one_pos, u, hu, fun x v hv => h x v ?_⟩
    have := norm_le_norm_add_norm_sub' v w
    rw [mem_ball_iff_norm] at hv
    linarith
  · simp only [Heisenberg₂, kerSum]
    rw [← tsum_mul_right, ← tsum_mul_left,
      ← (Equiv.addLeft (⟨y, hy⟩ : Λ)).tsum_eq (fun x : Λ => α x * kerTerm H x w z)]
    refine tsum_congr fun x => ?_
    simp only [Equiv.coe_addLeft, AddSubgroup.coe_add]
    rw [hα.2.2 y hy x x.2, mul_assoc (α x), kerTerm_shift H hH.1]
    ring

end GlobalTheory.UnitaryTheta.KerSum
