import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host

namespace PositivityTheory.jumpWindows

namespace AveragingProjection

section Avg

variable {G : Type} [AddCommGroup G] [TopologicalSpace G]

theorem avg_add (Γ : AddSubgroup G) {Φ Ψ : G → ℂ} (hΦ : Continuous Φ) (hΨ : Continuous Ψ) {B : ℝ}
    (bΦ : ∀ x, ‖Φ x‖ ≤ B) (bΨ : ∀ x, ‖Ψ x‖ ≤ B) :
    avg Γ (fun x => Φ x + Ψ x) = avg Γ Φ + avg Γ Ψ := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  simp only [avg]
  split_ifs with h
  · have _ : IsFiniteMeasure (h.choose.1.restrict h.choose.2) :=
      isFiniteMeasure_restrict.2 (by rw [h.choose_spec.2.2]; exact ENNReal.one_ne_top)
    exact integral_add (Integrable.of_bound hΦ.aestronglyMeasurable B (ae_of_all _ bΦ))
      (Integrable.of_bound hΨ.aestronglyMeasurable B (ae_of_all _ bΨ))
  · simp

theorem avg_zero (Γ : AddSubgroup G) : avg Γ (fun _ => (0 : ℂ)) = 0 := by
  simpa using avg_const_mul Γ 0 (fun _ => (0 : ℂ))

theorem norm_avg_sub_le (Γ : AddSubgroup G) {Φ Ψ : G → ℂ} (hΦ : Continuous Φ) (hΨ : Continuous Ψ) {B : ℝ}
    (bΦ : ∀ x, ‖Φ x‖ ≤ B) (bΨ : ∀ x, ‖Ψ x‖ ≤ B) {C : ℝ} (hC : 0 ≤ C) (hd : ∀ x, ‖Φ x - Ψ x‖ ≤ C) :
    ‖avg Γ Φ - avg Γ Ψ‖ ≤ C := by
  let _ : MeasurableSpace G := borel G
  have _ : BorelSpace G := ⟨rfl⟩
  simp only [avg]
  split_ifs with h
  · have e1 : h.choose.1 h.choose.2 = 1 := h.choose_spec.2.2
    have _ : IsFiniteMeasure (h.choose.1.restrict h.choose.2) :=
      isFiniteMeasure_restrict.2 (by rw [e1]; exact ENNReal.one_ne_top)
    rw [← integral_sub (Integrable.of_bound hΦ.aestronglyMeasurable B (ae_of_all _ bΦ))
      (Integrable.of_bound hΨ.aestronglyMeasurable B (ae_of_all _ bΨ))]
    calc _ ≤ C * h.choose.1.real h.choose.2 :=
          norm_setIntegral_le_of_norm_le_const (by rw [e1]; exact ENNReal.one_lt_top) fun x _ => hd x
      _ = C := by simp [Measure.real, e1]
  · simpa using hC

theorem continuous_avg {X : Type} [TopologicalSpace X] (Γ : AddSubgroup G) {u : G → X} (hu : Continuous u) :
    Continuous fun φ : X →ᵇ ℂ => avg Γ (fun x => φ (u x)) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun φ ψ => ?_).continuous
  rw [dist_eq_norm, NNReal.coe_one, one_mul]
  exact norm_avg_sub_le Γ (φ.continuous.comp hu) (ψ.continuous.comp hu) (B := max ‖φ‖ ‖ψ‖)
    (fun x => (φ.norm_coe_le_norm _).trans (le_max_left _ _))
    (fun x => (ψ.norm_coe_le_norm _).trans (le_max_right _ _)) dist_nonneg
    (fun x => by rw [← dist_eq_norm]; exact BoundedContinuousFunction.dist_coe_le_dist (f := φ) (g := ψ) (u x))

end Avg

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

def P (ψ : AddChar (Ad E) ℂ) (φ : XB E a) : Prop :=
  Good ψ (a - 1) φ ∧ ∀ γ g, φ (ratGL E a γ * g) = φ g

theorem P_zero : P ψ (0 : XB E a) := by
  refine ⟨⟨(0 : XB E a).continuous, fun γ _ g => rfl, fun k _ y g => by simp, fun r _ _ g => ?_⟩, fun γ g => rfl⟩
  simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply]
  exact avg_zero _

theorem P_add {φ φ' : XB E a} (h : P ψ φ) (h' : P ψ φ') : P ψ (φ + φ') := by
  refine ⟨⟨(φ + φ').continuous, fun γ hγ g => ?_, fun k hk y g => ?_, fun r hr hr' g => ?_⟩, fun γ g => ?_⟩
  · simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, h.1.left γ hγ g, h'.1.left γ hγ g]
  · simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, h.1.law k hk y g, h'.1.law k hk y g, mul_add]
  · simp only [BoundedContinuousFunction.coe_add, Pi.add_apply]
    rw [avg_add _ (Φ := fun x => φ (blkU x * g)) (Ψ := fun x => φ' (blkU x * g)) (φ.continuous.comp ((continuous_posU _).mul continuous_const))
      (φ'.continuous.comp ((continuous_posU _).mul continuous_const)) (B := max ‖φ‖ ‖φ'‖)
      (fun x => (φ.norm_coe_le_norm _).trans (le_max_left _ _))
      (fun x => (φ'.norm_coe_le_norm _).trans (le_max_right _ _)),
      h.1.van r hr hr' g, h'.1.van r hr hr' g, add_zero]
  · simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, h.2 γ g, h'.2 γ g]

theorem P_smul (c : ℂ) {φ : XB E a} (h : P ψ φ) : P ψ (c • φ) := by
  refine ⟨⟨(c • φ).continuous, fun γ hγ g => ?_, fun k hk y g => ?_, fun r hr hr' g => ?_⟩, fun γ g => ?_⟩
  · simp only [BoundedContinuousFunction.coe_smul, h.1.left γ hγ g]
  · simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul, h.1.law k hk y g]
    ring
  · simp only [BoundedContinuousFunction.coe_smul, smul_eq_mul]
    rw [avg_const_mul, h.1.van r hr hr' g, mul_zero]
  · simp only [BoundedContinuousFunction.coe_smul, h.2 γ g]

theorem P_rt (k : GA E a) {φ : XB E a} (h : P ψ φ) : P ψ (Rt E a k φ) := by
  refine ⟨⟨(Rt E a k φ).continuous, fun γ hγ g => ?_, fun j hj y g => ?_, fun r hr hr' g => ?_⟩, fun γ g => ?_⟩
  · simp only [Rt_apply, mul_assoc]; exact h.1.left γ hγ (g * k)
  · simp only [Rt_apply, mul_assoc]; exact h.1.law j hj y (g * k)
  · simp only [Rt_apply, mul_assoc]; exact h.1.van r hr hr' (g * k)
  · simp only [Rt_apply, mul_assoc]; exact h.2 γ (g * k)

theorem isClosed_P : IsClosed {φ : XB E a | P ψ φ} := by
  have key : {φ : XB E a | P ψ φ} =
      (⋂ (γ : GL (Fin a) E), ⋂ (g : GA E a), {φ : XB E a | φ (ratGL E a γ * g) = φ g}) ∩
      ((⋂ (k : ℕ), ⋂ (_ : a - 1 < k), ⋂ (y : UnipotentBlockColumnIndex a k k → Ad E), ⋂ (g : GA E a),
          {φ : XB E a | φ (blkU y * g) = ψ (dot (eLast a k) y) * φ g}) ∩
        (⋂ (r : ℕ), ⋂ (_ : 0 < r), ⋂ (_ : r ≤ a - 1), ⋂ (g : GA E a),
          {φ : XB E a | avg (ratV E (UnipotentBlockColumnIndex a r (a - 1))) (fun x => φ (blkU x * g)) = 0})) := by
    ext φ
    simp only [P, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hG, hl⟩
      exact ⟨hl, hG.law, hG.van⟩
    · rintro ⟨hl, hlaw, hvan⟩
      exact ⟨⟨φ.continuous, fun γ _ g => hl γ g, hlaw, hvan⟩, hl⟩
  rw [key]
  refine (isClosed_iInter fun γ => isClosed_iInter fun g => ?_).inter
    ((isClosed_iInter fun k => isClosed_iInter fun _ => isClosed_iInter fun y => isClosed_iInter fun g => ?_).inter
      (isClosed_iInter fun r => isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun g => ?_))
  · exact isClosed_eq (continuous_eval_const _) (continuous_eval_const _)
  · exact isClosed_eq (continuous_eval_const _) (continuous_const.mul (continuous_eval_const _))
  · exact isClosed_eq (continuous_avg _ ((continuous_posU _).mul continuous_const)) continuous_const

end AveragingProjection

open AveragingProjection in
theorem averaging_projection_linear : G2a := by
  intro E _ _ _ a ψ _
  refine ⟨{ carrier := {φ | P ψ φ}, add_mem' := P_add, zero_mem' := P_zero, smul_mem' := P_smul },
    isClosed_P, fun g φ h => P_rt g h, fun φ => Iff.rfl⟩

end PositivityTheory.jumpWindows

end
