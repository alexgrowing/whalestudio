import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.HilbertNinetyNorms.OrdLEqNegLog

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Bc.ArchbcB.B.M4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem TO_diagT (w : Pl E) (a : ℕ) (g : GLw a w) (hg : g ∈ TO a w) :
    ∃ d : Fin a → (w.adicCompletion E)ˣ, (∀ i, Valued.v (d i : w.adicCompletion E) = 1) ∧
      g = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin a) d := by
  obtain ⟨h0, h1⟩ := hg
  have hne : ∀ i, g.val i i ≠ 0 := fun i h => by
    have := h1 i; rw [h, map_zero] at this; exact zero_ne_one this
  refine ⟨fun i => Units.mk0 _ (hne i), fun i => h1 i, Units.ext ?_⟩
  rw [GlobalTheory.SmGL.val_diagT]
  ext i j
  by_cases hij : i = j
  · subst hij; simp
  · rw [diagonal_apply_ne _ hij, h0 i j hij]

theorem ordL_of_v_one {w : Pl E} {x : w.adicCompletion E} (hx : Valued.v x = 1) : ordL x = 0 := by
  rw [ordL_eq_neg_log', hx, ← WithZero.exp_zero, WithZero.log_exp, neg_zero]

def nEnt (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) {a : ℕ} (y : Fin a → ℤ) (d : Fin a → (w.adicCompletion E)ˣ)
    (i : Fin a) : (w.adicCompletion E)ˣ :=
  ϖ ^ y i * d i * (cjU w (ϖ ^ y i.rev * d i.rev))⁻¹

theorem nrm_tdiag (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (a : ℕ) (y : Fin a → ℤ)
    (d : Fin a → (w.adicCompletion E)ˣ) :
    nrmL a w (tdiag ϖ y * GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin a) d) =
      GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin a) (nEnt w ϖ y d) := by
  rw [nrmL_eq w hw, show tdiag ϖ y = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin a) (fun i => ϖ ^ y i) from rfl,
    ← map_mul, thL_diagT w hw, ← map_mul]
  rfl

theorem ordL_nEnt (hU : Unr E) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ) {a : ℕ} (y : Fin a → ℤ)
    (d : Fin a → (w.adicCompletion E)ˣ) (hd : ∀ i, Valued.v (d i : w.adicCompletion E) = 1) (i : Fin a) :
    ordL (nEnt w ϖ y d i : w.adicCompletion E) = nv y i := by
  have hP : ∀ j, ordL (((ϖ ^ y j : (w.adicCompletion E)ˣ)) : w.adicCompletion E) = y j := fun j => by
    rw [ordL_zpow_units, hϖ.1, mul_one]
  simp only [nEnt, Units.val_mul, Units.val_inv_eq_inv_val, cjU_val]
  rw [ordL_mul'' (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))
      (inv_ne_zero ((_root_.map_ne_zero _).2 (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)))),
    ordL_mul'' (Units.ne_zero _) (Units.ne_zero _),
    ordL_inv'' ((_root_.map_ne_zero _).2 (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))), ordL_cj hU,
    ordL_mul'' (Units.ne_zero _) (Units.ne_zero _), hP, hP, ordL_of_v_one (hd i), ordL_of_v_one (hd i.rev), nv]
  ring

theorem unq_diag (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifAt ϖ)
    (a : ℕ) (y : Fin a → ℤ) (hy : StrictAnti y) (τ τ' : GLw a w) (hτ : τ ∈ TO a w) (hτ' : τ' ∈ TO a w)
    (h : (nrmL a w (tdiag ϖ y * τ)).val.charpoly = (nrmL a w (tdiag ϖ y * τ')).val.charpoly) :
    ∃ g : GLw a w, g ∈ TO a w ∧ g⁻¹ * (tdiag ϖ y * τ) * thL a w g = tdiag ϖ y * τ' := by
  obtain ⟨d, hd, rfl⟩ := TO_diagT w a τ hτ
  obtain ⟨d', hd', rfl⟩ := TO_diagT w a τ' hτ'
  rw [nrm_tdiag w hw, nrm_tdiag w hw, GlobalTheory.SmGL.val_diagT, GlobalTheory.SmGL.val_diagT, charpoly_diagonal,
    charpoly_diagonal] at h
  have hcϖ : cjU w ϖ = ϖ := Units.ext hϖ.2
  have hee : ∀ i, nEnt w ϖ y d i = nEnt w ϖ y d' i := by
    intro i
    have hr : (∏ j, (X - C ((nEnt w ϖ y d' j : (w.adicCompletion E)ˣ) : w.adicCompletion E))).eval
        ((nEnt w ϖ y d i : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 0 := by
      rw [← h, eval_prod]; exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    rw [eval_prod, Finset.prod_eq_zero_iff] at hr
    obtain ⟨j, -, hj⟩ := hr
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hj
    have hvij : nv y i = nv y j := by
      rw [← ordL_nEnt hU w ϖ hϖ y d hd i, hj, ordL_nEnt hU w ϖ hϖ y d' hd' j]
    have hij := (nv_strictAnti hy).injective hvij
    subst hij
    exact Units.ext hj
  have hsplit : ∀ (e : Fin a → (w.adicCompletion E)ˣ) i, nEnt w ϖ y e i =
      (ϖ ^ y i * (cjU w (ϖ ^ y i.rev))⁻¹) * (e i * (cjU w (e i.rev))⁻¹) := fun e i => by
    simp only [nEnt, map_mul, mul_inv]; rw [mul_mul_mul_comm]
  set r : Fin a → (w.adicCompletion E)ˣ := fun i => d i * (d' i)⁻¹ with hrdef
  have hrr : ∀ i, r i = cjU w (r i.rev) := by
    intro i
    have h1 := hee i
    rw [hsplit, hsplit] at h1
    have h2 := mul_left_cancel h1
    simp only [hrdef, map_mul, map_inv]
    apply Units.ext
    have h3 := congrArg Units.val h2
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, cjU_val] at h3 ⊢
    field_simp at h3 ⊢
    linear_combination h3
  have hrv : ∀ i, Valued.v (r i : w.adicCompletion E) = 1 := fun i => by
    simp [hrdef, Units.val_mul, Units.val_inv_eq_inv_val, map_inv₀, hd, hd']
  have hmid : ∀ i, i.rev = i → ∃ Z : (w.adicCompletion E)ˣ, Valued.v (Z : w.adicCompletion E) = 1 ∧
      Z * cjU w Z = r i := fun i hi => by
    have hfix : cj w (r i : w.adicCompletion E) = r i := by
      have := congrArg Units.val (hrr i); rw [hi] at this; exact this.symm
    obtain ⟨z, hz, hz'⟩ := (hilbert90_norm_one_units_of_unr_of_not_split hU w hw).1 _ (hrv i) hfix
    have hz0 : z ≠ 0 := by intro h; rw [h, map_zero] at hz; exact zero_ne_one hz
    exact ⟨Units.mk0 z hz0, hz, Units.ext (by simpa using hz')⟩
  let hh : Fin a → (w.adicCompletion E)ˣ := fun i =>
    if h : i < i.rev then r i else if h' : i.rev = i then Classical.choose (hmid i h') else 1
  have hhv : ∀ i, Valued.v (hh i : w.adicCompletion E) = 1 := fun i => by
    simp only [hh]
    split_ifs with h h'
    · exact hrv i
    · exact (Classical.choose_spec (hmid i h')).1
    · simp
  have hk : ∀ i, hh i * cjU w (hh i.rev) = r i := by
    intro i
    rcases lt_trichotomy i i.rev with h | h | h
    · have e1 : hh i = r i := by simp only [hh, dif_pos h]
      have e2 : hh i.rev = 1 := by
        have hn : ¬ i.rev < i.rev.rev := by rw [Fin.rev_rev]; exact not_lt.2 h.le
        have hn' : ¬ i.rev.rev = i.rev := by rw [Fin.rev_rev]; exact h.ne
        simp only [hh, dif_neg hn, dif_neg hn']
      rw [e1, e2, map_one, mul_one]
    · have hi : i.rev = i := h.symm
      have hn : ¬ i < i.rev := by rw [hi]; exact lt_irrefl i
      have e1 : hh i = Classical.choose (hmid i hi) := by simp only [hh, dif_neg hn, dif_pos hi]
      rw [hi, e1]
      exact (Classical.choose_spec (hmid i hi)).2
    · have hn : ¬ i < i.rev := not_lt.2 h.le
      have hn' : ¬ i.rev = i := h.ne
      have e1 : hh i = 1 := by simp only [hh, dif_neg hn, dif_neg hn']
      have hp : i.rev < i.rev.rev := by rw [Fin.rev_rev]; exact h
      have e2 : hh i.rev = r i.rev := by simp only [hh, dif_pos hp]
      rw [e1, e2, one_mul, hrr i]
  refine ⟨GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin a) hh, ⟨fun i j hij => ?_, fun i => ?_⟩, ?_⟩
  · rw [GlobalTheory.SmGL.val_diagT, diagonal_apply_ne _ hij]
  · rw [GlobalTheory.SmGL.val_diagT, diagonal_apply_eq]; exact hhv i
  rw [thL_diagT w hw, show tdiag ϖ y = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin a) (fun i => ϖ ^ y i) from rfl,
    ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  funext i
  have hki := congrArg Units.val (hk i)
  apply Units.ext
  simp only [Pi.mul_apply, Pi.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, cjU_val, hrdef] at hki ⊢
  field_simp at hki ⊢
  linear_combination -hki

end PositivityTheory.Rg.Bc.ArchbcB.B.M4
