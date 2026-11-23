import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

namespace GlobalTheory

theorem finSigmaFinEquiv_val_eq_range {s : ℕ} (t : Fin s → ℕ) (x : (a : Fin s) × Fin (t a)) :
    ((finSigmaFinEquiv x : Fin (∑ a, t a)) : ℕ) =
      (∑ i ∈ Finset.range x.1, (fun i : ℕ => if h : i < s then t ⟨i, h⟩ else 0) i) + x.2 := by
  rw [finSigmaFinEquiv_apply]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : (i : ℕ) < s := lt_of_lt_of_le i.2 x.1.2.le
  simp only [hi, dif_pos]
  rfl

theorem finSigmaFinEquiv_lt_of_lex_lt {s : ℕ} (t : Fin s → ℕ) (x y : (a : Fin s) × Fin (t a))
    (hxy : toLex x < toLex y) :
    (finSigmaFinEquiv x : Fin (∑ a, t a)) < finSigmaFinEquiv y := by
  rw [Fin.lt_def, finSigmaFinEquiv_val_eq_range, finSigmaFinEquiv_val_eq_range]
  set t' : ℕ → ℕ := fun i => if h : i < s then t ⟨i, h⟩ else 0 with ht'
  rcases Sigma.Lex.lt_def.mp hxy with h | ⟨h, h2⟩
  · have h' : (x.1 : ℕ) < y.1 := h
    have hsub : Finset.range (x.1 + 1) ⊆ Finset.range y.1 :=
      Finset.range_subset_range.mpr h'
    have hle : (Finset.range (x.1 + 1)).sum t' ≤ (Finset.range y.1).sum t' :=
      Finset.sum_le_sum_of_subset hsub
    replace hle := (Finset.sum_range_succ t' x.1).symm.trans_le hle
    have hx : t' x.1 = t x.1 := by simp [ht', x.1.2]
    have h3 : (x.2 : ℕ) < t x.1 := x.2.2
    have h4 : (∑ i ∈ Finset.range x.1, t' i) = (Finset.range x.1).sum t' := rfl
    omega
  · obtain ⟨a, i⟩ := x
    obtain ⟨b, j⟩ := y
    change a = b at h
    subst h
    change i < j at h2
    have : (i : ℕ) < j := h2
    simp only
    omega

theorem finSigmaFinEquiv_symm_strictMono_lex :
    ∀ (s : ℕ) (t : Fin s → ℕ), StrictMono fun c : Fin (∑ a, t a) =>
      (toLex (finSigmaFinEquiv.symm c) : Σₗ a, Fin (t a)) := by
  intro s t c d hcd
  by_contra hn
  rw [not_lt] at hn
  rcases hn.lt_or_eq with h | h
  · have := finSigmaFinEquiv_lt_of_lex_lt t _ _ h
    simp only [Equiv.apply_symm_apply] at this
    exact absurd hcd (not_lt.mpr this.le)
  · have h' : finSigmaFinEquiv.symm d = finSigmaFinEquiv.symm c := toLex.injective h
    have := finSigmaFinEquiv.symm.injective h'
    exact absurd hcd (by rw [this]; exact lt_irrefl _)

end GlobalTheory
