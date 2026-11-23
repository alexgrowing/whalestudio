import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantMetricIsometry.ColChoiceFintype

noncomputable section

open Matrix Classical

namespace PI.IsoInvMetricW

open PI.IsoInvMetric

theorem oe_eq_of_range_sub {h N : ℕ} (I J : Fin h ↪o Fin N) (hs : ∀ i, ∃ k, J k = I i) :
    I = J := by
  classical
  have h1 : Finset.univ.image I ⊆ Finset.univ.image J := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨i, rfl⟩ := hx
    exact hs i
  have h2 : Finset.univ.image I = Finset.univ.image J :=
    Finset.eq_of_subset_of_card_le h1 (by
      rw [Finset.card_image_of_injective _ J.injective,
        Finset.card_image_of_injective _ I.injective])
  apply OrderEmbedding.range_inj.mp
  have := congrArg (fun s : Finset (Fin N) => (s : Set (Fin N))) h2
  simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using this

theorem metric_diagonal : EDiag := by
  intro Lt _ _ N nu d I J
  unfold E
  split_ifs with hIJ
  · subst hIJ
    refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
    have : (Matrix.of fun i k : Fin ((nu s).colLen c) =>
        Matrix.diagonal (d s) (I s c i) (I s c k)) = Matrix.diagonal (fun i => d s (I s c i)) := by
      ext i k
      simp [Matrix.diagonal_apply, (I s c).injective.eq_iff]
    rw [this, Matrix.det_diagonal]
  · have : ∃ s c, I s c ≠ J s c := by
      by_contra hne
      push_neg at hne
      exact hIJ (funext fun s => funext fun c => hne s c)
    obtain ⟨s, c, hsc⟩ := this
    have : ∃ i, ∀ k, J s c k ≠ I s c i := by
      by_contra hne
      push_neg at hne
      exact hsc (oe_eq_of_range_sub _ _ hne)
    obtain ⟨i, hi⟩ := this
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro k
    simp [Matrix.diagonal_apply_ne _ (hi k).symm]

def J0 {Lt : Type} {N : ℕ} (nu : Lt → YoungDiagram) (hle : ∀ z, (nu z).colLen 0 ≤ N) :
    ColChoice N nu :=
  fun s c => Fin.castLEOrderEmb (le_trans ((nu s).colLen_anti 0 c (Nat.zero_le _)) (hle s))

theorem unitVector_val_eq {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} (nu : Lt → YoungDiagram)
    (hle : ∀ z, (nu z).colLen 0 ≤ N) (J : ColChoice N nu) :
    u0 N nu J = if J = J0 nu hle then 1 else 0 := by
  have e : u0 N nu J = E nu (fun _ => Matrix.diagonal (fun _ => (1 : ℂ))) J (J0 nu hle) := by
    unfold u0 hvC minY E
    refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
    congr 1
    ext i k
    have hk : (k : ℕ) < N := lt_of_lt_of_le k.2
      (le_trans ((nu s).colLen_anti 0 c (Nat.zero_le _)) (hle s))
    simp only [Matrix.of_apply, colsOf, hk, dite_true, Matrix.diagonal_one, J0]
    rfl
  rw [e, metric_diagonal]
  split_ifs <;> simp

theorem norm1' : Norm1 := by
  intro Lt _ _ N nu hle
  unfold l2
  rw [finsum_eq_sum_of_fintype]
  simp [unitVector_val_eq nu hle, apply_ite (fun x : ℂ => ‖x‖ ^ 2)]

end PI.IsoInvMetricW
