import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Transfer

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismTransfer

open PositivityTheory.KB.SplitAffineSpectral

variable {Y : Type}

theorem dc_cons {m : ℕ} (G : (Fin (m + 2) → Y) → ℝ) (a : Y) (t : Fin (m + 2) → Y) :
    dc G (Fin.cons a t) = G t - dc (fun z => G (Fin.cons a z)) t := by
  unfold dc
  rw [Fin.sum_univ_succ]
  have h0 : (fun j => (Fin.cons a t : Fin (m + 3) → Y) ((0 : Fin (m + 3)).succAbove j)) = t := by
    funext j; simp [Fin.succAbove_zero]
  have hs : ∀ i : Fin (m + 2), (fun j => (Fin.cons a t : Fin (m + 3) → Y) (i.succ.succAbove j)) =
      Fin.cons a (fun j => t (i.succAbove j)) := by
    intro i; funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [Fin.succ_succAbove_zero]
    · simp [Fin.succ_succAbove_succ]
  rw [h0]
  simp only [hs, Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem dc_sub {m : ℕ} (G H : (Fin (m + 1) → Y) → ℝ) (x : Fin (m + 2) → Y) :
    dc (fun z => G z - H z) x = dc G x - dc H x := by
  unfold dc
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem dc1 (G : (Fin 1 → Y) → ℝ) (y : Fin 2 → Y) :
    dc G y = G (fun _ => y 1) - G (fun _ => y 0) := by
  unfold dc
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
  have h0 : (fun j : Fin 1 => y ((0 : Fin 2).succAbove j)) = fun _ => y 1 := by
    funext j; rw [Fin.fin_one_eq_zero j]; rfl
  have h1 : (fun j : Fin 1 => y ((Fin.succ 0 : Fin 2).succAbove j)) = fun _ => y 0 := by
    funext j; rw [Fin.fin_one_eq_zero j]; rfl
  rw [h0, h1]; simp; ring

def prism (φ : Y → Y) : (m : ℕ) → ((Fin (m + 2) → Y) → ℝ) → (Fin (m + 1) → Y) → ℝ
  | 0, F, x => F (Fin.cons (x 0) (φ ∘ x))
  | m + 1, F, x => F (Fin.cons (x 0) (φ ∘ x)) - prism φ m (fun z => F (Fin.cons (x 0) z)) (Fin.tail x)

theorem prism_sub (φ : Y → Y) : ∀ (m : ℕ) (F G : (Fin (m + 2) → Y) → ℝ) (x : Fin (m + 1) → Y),
    prism φ m (fun z => F z - G z) x = prism φ m F x - prism φ m G x
  | 0, F, G, x => rfl
  | m + 1, F, G, x => by
    simp only [prism]
    rw [prism_sub φ m]
    ring

theorem prism_zero (φ : Y → Y) : ∀ (m : ℕ) (x : Fin (m + 1) → Y),
    prism φ m (fun _ => (0 : ℝ)) x = 0
  | 0, x => rfl
  | m + 1, x => by
    simp only [prism]
    rw [prism_zero φ m]
    ring

theorem prism_base (φ : Y → Y) (F : (Fin 2 → Y) → ℝ) (x : Fin 2 → Y) :
    dc (prism φ 0 F) x + prism φ 1 (dc F) x = F (φ ∘ x) - F x := by
  obtain ⟨a, b, rfl⟩ : ∃ a b, x = Fin.cons a (fun _ : Fin 1 => b) := ⟨x 0, x 1, by
    funext j; refine Fin.cases rfl (fun k => ?_) j; rw [Fin.fin_one_eq_zero k]; rfl⟩
  simp only [prism, Fin.cons_zero, Fin.tail_cons]
  simp only [Fin.comp_cons]
  simp only [dc_cons, dc1]
  simp only [Fin.cons_zero, Fin.cons_one, Fin.tail_cons, Function.comp_def]
  ring

theorem prism_htpy (φ : Y → Y) : ∀ (m : ℕ) (F : (Fin (m + 2) → Y) → ℝ) (x : Fin (m + 2) → Y),
    dc (prism φ m F) x + prism φ (m + 1) (dc F) x = F (φ ∘ x) - F x
  | 0, F, x => prism_base φ F x
  | m + 1, F, x => by
    obtain ⟨a, t, rfl⟩ : ∃ a t, x = Fin.cons a t := ⟨x 0, Fin.tail x, (Fin.cons_self_tail x).symm⟩
    have ih := prism_htpy φ m (fun z => F (Fin.cons a z)) t
    rw [dc_cons]
    have hK : (fun z => prism φ (m + 1) F (Fin.cons a z)) =
        fun z => F (Fin.cons a (Fin.cons (φ a) (φ ∘ z))) - prism φ m (fun w => F (Fin.cons a w)) z := by
      funext z; simp only [prism, Fin.cons_zero, Fin.tail_cons, Fin.comp_cons]
    rw [hK, dc_sub]
    have h2 : prism φ (m + 2) (dc F) (Fin.cons a t) =
        dc F (Fin.cons a (φ ∘ Fin.cons a t)) - prism φ (m + 1) (fun z => dc F (Fin.cons a z)) t := by
      simp only [prism, Fin.cons_zero, Fin.tail_cons]
    rw [h2]
    have h3 : (fun z => dc F (Fin.cons a z)) = fun z => F z - dc (fun w => F (Fin.cons a w)) z := by
      funext z; exact dc_cons F a z
    rw [h3, prism_sub, Fin.comp_cons, dc_cons, dc_cons]
    have h4 : dc (fun z => F (Fin.cons a (Fin.cons (φ a) (φ ∘ z)))) t =
        dc (fun w => F (Fin.cons a (Fin.cons (φ a) w))) (φ ∘ t) := rfl
    rw [h4]
    linarith [ih]

theorem prism_smul {P : Type} [Group P] (φ : P → P) (k : P) (hφ : ∀ y, φ (k * y) = k * φ y) :
    ∀ (m : ℕ) (F : (Fin (m + 2) → P) → ℝ) (x : Fin (m + 1) → P),
      prism φ m F (fun i => k * x i) = prism φ m (fun z => F (fun i => k * z i)) x
  | 0, F, x => by
    simp only [prism]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [hφ]
  | m + 1, F, x => by
    simp only [prism]
    have e1 : (Fin.cons (k * x 0) (φ ∘ fun i => k * x i) : Fin (m + 3) → P) =
        fun i => k * (Fin.cons (x 0) (φ ∘ x) : Fin (m + 3) → P) i := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [hφ]
    rw [e1]
    congr 1
    have e2 : (Fin.tail fun i => k * x i) = fun i => k * Fin.tail x i := rfl
    rw [e2, prism_smul φ k hφ m]
    congr 1
    funext z
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp

end PositivityTheory.KB.SplitAffineSpectral.PrismTransfer

end
