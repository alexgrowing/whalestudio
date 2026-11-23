import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianHaarMeasure.SmoothLevZero

open Matrix Finset MeasureTheory
open scoped ContDiff

noncomputable section

namespace PI.QnHermHaar

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Gen

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {i : Fin (r + 1)} {μ : Measure (Mt k r)}

theorem repOn_of_eq {hI' : IntOn μ (ιo k r) (testSub k r i)} {T : A hI'} {Φ Ψ : (Mx k r → ℂ) → Mx k r → ℂ}
    (h : RepOn hI' T Φ) (e : ∀ f, Φ f = Ψ f) : RepOn hI' T Ψ := by
  have hΦΨ : Φ = Ψ := funext e
  subst hΦΨ
  exact h

private theorem eq_of_repOn_of_agree_on_test (H : Hyp k r z z' i μ) {S T : A (hI H)}
    {Φ Ψ : (Mx k r → ℂ) → Mx k r → ℂ} (hS : RepOn (hI H) S Φ) (hT : RepOn (hI H) T Ψ)
    (e : ∀ f, TestF k r i f → ∀ g ∈ Glev k r i, Φ f g = Ψ f g) : S = T :=
  A_ext (hI H) fun f hf => by
    rw [(hS f hf).2, (hT f hf).2]
    exact mk'_eq_of_eqOn (hI H) (Glev k r i) (hG H) (hS f hf).1 (hT f hf).1 (e f hf)

private theorem repOn_ite' (H : Hyp k r z z' i μ) (p : Prop) [Decidable p] {T : A (hI H)}
    {Φ : (Mx k r → ℂ) → Mx k r → ℂ} (hT : RepOn (hI H) T Φ) :
    RepOn (hI H) (if p then T else 0) (fun f g => if p then Φ f g else 0) := by
  by_cases hp : p
  · simp only [if_pos hp]
    exact hT
  · simp only [if_neg hp]
    have h0 := repOn_sub _ hT hT
    rw [sub_self] at h0
    exact repOn_of_eq h0 fun f => funext fun g => by simp

theorem glRel_A (H : Hyp k r z z' i μ) : GlRel (EA H) := by
  intro a b c d
  refine eq_of_repOn_of_agree_on_test H (repOn_sub _ (repOn_mul _ (repE H a b) (repE H c d)) (repOn_mul _ (repE H c d) (repE H a b)))
    (repOn_sub _ (repOn_ite' H (b = c) (repE H a d)) (repOn_ite' H (d = a) (repE H c b))) fun f hf g hg => ?_
  exact H.Gl ℂ k r i Set.univ a b c d f isOpen_univ hf.1 g ⟨hg, Set.mem_univ _⟩

theorem starE_A (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) :
    star (EA H a b) = ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EA H c d := by
  have hL : RepOn (hI H) (star (EA H a b)) (EOp' k r i a b) := by
    show RepOn (hI H) (star (toA (hI H) (hG H) (adjOp_E H a b))) _
    rw [star_toA]
    exact repOn_toA _ _ _
  have hR : RepOn (hI H) (∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EA H c d)
      (fun f => ∑ c, ∑ d, (Hm k r i c b * Hm k r i a d) • EOp k r i c d f) :=
    repOn_sum _ _ fun c _ => repOn_sum _ _ fun d _ => repOn_smul _ _ (repE H c d)
  refine eq_of_repOn_of_agree_on_test H hL hR fun f _ g _ => ?_
  simp only [EOp'_eq]

theorem yComm (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) : YA H a * YA H b = YA H b * YA H a := by
  refine eq_of_repOn_of_agree_on_test H (repOn_mul _ (repY H a) (repY H b)) (repOn_mul _ (repY H b) (repY H a)) fun f _ g _ => ?_
  simp only [MOp]
  ring

theorem ybComm (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) : YbA H a * YbA H b = YbA H b * YbA H a := by
  refine eq_of_repOn_of_agree_on_test H (repOn_mul _ (repYb H a) (repYb H b)) (repOn_mul _ (repYb H b) (repYb H a)) fun f _ g _ => ?_
  simp only [MOp]
  ring

theorem yybComm (H : Hyp k r z z' i μ) (a b : Fin (mdim k r i)) : YA H a * YbA H b = YbA H b * YA H a := by
  refine eq_of_repOn_of_agree_on_test H (repOn_mul _ (repY H a) (repYb H b)) (repOn_mul _ (repYb H b) (repY H a)) fun f _ g _ => ?_
  simp only [MOp]
  ring

theorem eyComm (H : Hyp k r z z' i μ) (a b c : Fin (mdim k r i)) :
    EA H a b * YA H c - YA H c * EA H a b = if a = c then -YA H b else 0 := by
  refine eq_of_repOn_of_agree_on_test H (repOn_sub _ (repOn_mul _ (repE H a b) (repY H c)) (repOn_mul _ (repY H c) (repE H a b)))
    (repOn_ite' H (a = c) (repOn_neg _ (repY H b))) fun f hf g hg => ?_
  have hy := (H.YL ℂ k r z i Set.univ a b c f isOpen_univ hf.1 g ⟨hg, Set.mem_univ _⟩).1
  show EH k r (posL k r i a) (posL k r i b) (fun x => yv k r z i x c • f x) g -
      yv k r z i g c * EH k r (posL k r i a) (posL k r i b) f g =
      if a = c then -(yv k r z i g b * f g) else 0
  rw [hy]
  split_ifs <;> simp only [smul_eq_mul] <;> ring

theorem eybComm (H : Hyp k r z z' i μ) (a b c : Fin (mdim k r i)) :
    EA H a b * YbA H c - YbA H c * EA H a b = if b = c then YbA H a else 0 := by
  refine eq_of_repOn_of_agree_on_test H (repOn_sub _ (repOn_mul _ (repE H a b) (repYb H c)) (repOn_mul _ (repYb H c) (repE H a b)))
    (repOn_ite' H (b = c) (repYb H a)) fun f hf g hg => ?_
  have hy := (H.YL ℂ k r z i Set.univ a b c f isOpen_univ hf.1 g ⟨hg, Set.mem_univ _⟩).2
  show EH k r (posL k r i a) (posL k r i b) (fun x => ybv k r z i x c • f x) g -
      ybv k r z i g c * EH k r (posL k r i a) (posL k r i b) f g =
      if b = c then ybv k r z i g a * f g else 0
  rw [hy]
  split_ifs <;> simp only [smul_eq_mul] <;> ring

theorem ybStar (H : Hyp k r z z' i μ) (c : Fin (mdim k r i)) :
    YbA H c = ∑ l, Hm k r i l c • star (YA H l) := by
  have hs : ∀ l, RepOn (hI H) (star (YA H l)) (MOp' (fun g => yv k r z i g l)) := fun l => by
    show RepOn (hI H) (star (toA (hI H) (hG H) (adjOp_M _ (yTest H l)))) _
    rw [star_toA]
    exact repOn_toA _ _ _
  refine eq_of_repOn_of_agree_on_test H (repYb H c) (repOn_sum _ _ fun l _ => repOn_smul _ _ (hs l)) fun f _ g hg => ?_
  simp only [MOp, MOp', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [H.Yb k r z i H.hz g hg c, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

end PI.QnHermHaar
