import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepLin
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv GlobalTheory.StepLeft Classical

noncomputable section
namespace GlobalTheory.StepLeft

section Shape
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in

theorem basePt_eq_zero_of_stepVar (y : Matrix n n' k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) : basePt c y r s = 0 := by
  rcases r with r | r <;> rcases s with s | s <;> simp only [Free, Kept, or_false, false_or] at h <;>
    simp only [basePt, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, of_apply]
  rw [if_neg (by omega)]

omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] in

theorem stepVar_fixed_of_ordL_lt (y : Matrix n n' k) {r t : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hv : ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s))) (hlt : GlobalTheory.DiagVol.ordL c r < GlobalTheory.DiagVol.ordL c t) :
    ¬ (Free (c / 2 + 1) (t, s) ∨ Kept (t, s)) ∧ basePt c y t s = 0 := by
  rcases r with r | r <;> rcases t with t | t <;> rcases s with s | s <;>
    simp only [Free, Kept, GlobalTheory.DiagVol.ordL, Sum.elim_inl, Sum.elim_inr, basePt, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, of_apply, not_or,
      Nat.even_iff, Nat.odd_iff, not_and, true_and, and_true, not_false_eq_true, not_true_eq_false] at hv hlt ⊢
  all_goals first | omega | (refine ⟨⟨by omega, by omega⟩, ?_⟩; rw [if_neg (by omega)]) | (refine ⟨by omega, ?_⟩; rw [if_neg (by omega)]) | skip

end Shape

section Shape2
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

omit [Fintype n'] [DecidableEq n'] in

theorem unipSub_mul_fixed {u : GL (n ⊕ Fin c) k} (hu : u ∈ GlobalTheory.DiagVol.unipSub (GlobalTheory.DiagVol.ordL c))
    (y : Matrix n n' k) (M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (hM : ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → M r s = basePt c y r s) :
    ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → (u.val * M) r s = basePt c y r s := by
  intro r s hv
  have hu' : ∀ r t, GlobalTheory.DiagVol.ordL c t ≤ GlobalTheory.DiagVol.ordL c r →
      u.val r t = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r t := hu
  rw [Matrix.mul_apply, Finset.sum_eq_single r]
  · rw [hu' r r le_rfl, Matrix.one_apply_eq, one_mul, hM r s hv]
  · intro t _ htr
    by_cases h : GlobalTheory.DiagVol.ordL c t ≤ GlobalTheory.DiagVol.ordL c r
    · rw [hu' r t h, Matrix.one_apply_ne (Ne.symm htr), zero_mul]
    · obtain ⟨h1, h2⟩ := stepVar_fixed_of_ordL_lt y hv (not_le.1 h)
      rw [hM t s h1, h2, mul_zero]
  · simp

omit [Fintype n'] [DecidableEq n'] in

theorem embX_mul_fixed (κ : GL n k) (y : Matrix n n' k) (M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (hM : ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → M r s = basePt c y r s) :
    ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) →
      ((embX c κ).val * M) r s = basePt c (κ.val * y) r s := by
  intro r s hv
  have hE : (embX c κ).val = (fromBlocks κ.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) := rfl
  rw [hE, Matrix.mul_apply, Fintype.sum_sum_type]
  rcases r with a | l
  · simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
    have hb : ∀ b, M (Sum.inl b) s = basePt c y (Sum.inl b) s := fun b =>
      hM _ _ (by rcases s with s | s <;> simpa only [Free, Kept] using hv)
    simp only [hb]
    rcases s with s | s <;> simp [basePt, Matrix.mul_apply]
  · simp only [fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single l (fun j _ hj => by rw [Matrix.one_apply_ne (Ne.symm hj), zero_mul]) (by simp),
      Matrix.one_apply_eq, one_mul, hM _ _ hv]
    rcases s with s | s <;> simp [basePt]

end Shape2

theorem inv_mul_stepPt_shape : ∀ {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (v : GL (n ⊕ Fin c) k), v ∈ symN k n c → ∀ (κ : GL n k) (x₀ : Matrix n n' k) (e : StepVar n c n' → k), ((v * embX c κ)⁻¹).val * stepPt x₀ e = stepPt ((κ⁻¹).val * x₀) (fun a => (((v * embX c κ)⁻¹).val * stepPt x₀ e : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) a.1.1 a.1.2) := by
  intro k _ n n' _ _ _ _ c v hv κ x₀ e
  have hg : ((v * embX c κ)⁻¹).val = (embX c κ⁻¹).val * (v⁻¹).val := by
    rw [_root_.mul_inv_rev, map_inv, Units.val_mul]
  have hu : v⁻¹ ∈ GlobalTheory.DiagVol.unipSub (GlobalTheory.DiagVol.ordL c) := GlobalTheory.DiagVol.symN_le_unipSub (inv_mem hv)
  have hM : ∀ r s, ¬ (Free (c / 2 + 1) (r, s) ∨ Kept (r, s)) → stepPt x₀ e r s = basePt c x₀ r s :=
    fun r s h => by rw [stepPt, Matrix.add_apply, of_apply, dif_neg h, add_zero]
  have hA := embX_mul_fixed κ⁻¹ x₀ _ (unipSub_mul_fixed hu x₀ _ hM)
  have hR : ∀ (y : Matrix n n' k) (e' : StepVar n c n' → k) r s, stepPt y e' r s =
      basePt c y r s + (if h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s) then e' ⟨(r, s), h⟩ else 0) :=
    fun _ _ _ _ => rfl
  ext r s
  by_cases h : Free (c / 2 + 1) (r, s) ∨ Kept (r, s)
  · conv_rhs => rw [hR, dif_pos h, basePt_eq_zero_of_stepVar _ h, zero_add]
  · conv_rhs => rw [hR, dif_neg h, add_zero]
    rw [hg, Matrix.mul_assoc, hA r s h]

end GlobalTheory.StepLeft
