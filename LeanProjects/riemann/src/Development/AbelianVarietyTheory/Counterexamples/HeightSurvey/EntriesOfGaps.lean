import Mathlib
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ThetaMemLattice

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RunWeightTest

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons

theorem gapZ_nonneg {p : ℕ} {l : Fin p → ℕ} (hl : Antitone l) (i : Fin p) : 0 ≤ WeightAlgebra.gapZ l i := by
  unfold WeightAlgebra.gapZ
  split_ifs with h
  · have : l ⟨i.1 + 1, h⟩ ≤ l i := hl (by simp [Fin.le_def])
    omega
  · positivity

variable {D : D7} {j : ℕ}

theorem isL_lWt (ka : WeightFamilies.Wt D j) (T nW : ℕ) (hW : Even nW)
    (h : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 →
      ((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r ≤ ka.aP τ i) :
    WeightAlgebra.IsL D ka (lWt D ka T nW hW) T nW := by
  have hp : (0 : ℤ) ≤ (WeightAlgebra.Tp D j T : ℕ) := by positivity
  refine ⟨rfl, fun τ i => ?_, fun τ i => ?_⟩
  · show WeightAlgebra.gapZ (ofGaps (lGapP D ka T nW τ)) i = _
    rw [gapZ_ofGaps]; unfold lGapP
    split_ifs with hi
    · exact Int.toNat_of_nonneg (Int.fdiv_nonneg (by have := gapZ_nonneg (ka.aPlus_antitone τ) i; omega) hp)
    · exact Int.toNat_of_nonneg (Int.fdiv_nonneg (by have := h τ i (by have := i.2; omega); omega) hp)
  · show WeightAlgebra.gapZ (ofGaps (lGapM D ka T τ)) i = _
    rw [gapZ_ofGaps]; unfold lGapM
    split_ifs with hi
    · exact Int.toNat_of_nonneg (Int.fdiv_nonneg (by have := gapZ_nonneg (ka.aM_anti τ) i; omega) hp)
    · exact Int.toNat_of_nonneg (Int.fdiv_nonneg (by positivity) hp)

set_option autoImplicit false in
variable {D : _root_.Formalism.BasicNotions.D7} {j : ℕ} in
private lemma ofGaps_eq_sub_mul {p : ℕ} (a b g : Fin p → ℕ) (T : ℕ)
    (hg : ∀ k : Fin p, (g k : ℤ) = if (k : ℕ) + 1 < p then _root_.Formalism.MainNotions.WeightAlgebra.gapZ a k - T * _root_.Formalism.MainNotions.WeightAlgebra.gapZ b k
      else (a k : ℤ) - T * b k) (i : Fin p) :
    (_root_.Formalism.MainNotions.DIV.Cons.ofGaps g i : ℤ) = a i - T * b i := by
  suffices h : ∀ n, ∀ i : Fin p, p - (i : ℕ) = n → (_root_.Formalism.MainNotions.DIV.Cons.ofGaps g i : ℤ) = a i - T * b i from
    h _ i rfl
  intro n
  induction n with
  | zero => intro i hi; have := i.isLt; omega
  | succ n ih =>
    intro i hi
    by_cases h : (i : ℕ) + 1 < p
    · rw [_root_.Formalism.MainNotions.DIV.Cons.ofGaps_succ g i h]
      push_cast
      rw [ih ⟨(i : ℕ) + 1, h⟩ (by simp only; omega), hg i, if_pos h]
      unfold _root_.Formalism.MainNotions.WeightAlgebra.gapZ
      rw [dif_pos h, dif_pos h]
      ring
    · rw [_root_.Formalism.MainNotions.DIV.Cons.ofGaps_last g i h, hg i, if_neg h]

set_option autoImplicit false in
variable {D : _root_.Formalism.BasicNotions.D7} {j : ℕ} in
private lemma mul_toNat_fdiv_add_two_le_of_add_two_le {T K : ℕ} (hK : T + 2 ≤ K) {d : ℤ} (hd : 0 ≤ d) :
    (T : ℤ) * ((d + 2).fdiv K).toNat ≤ d := by
  have hKpos : (0 : ℤ) < K := by omega
  rw [Int.fdiv_eq_ediv_of_nonneg _ hKpos.le]
  have hq : 0 ≤ (d + 2) / (K : ℤ) := Int.ediv_nonneg (by omega) hKpos.le
  rw [Int.toNat_of_nonneg hq]
  have hle := Int.ediv_mul_le (d + 2) hKpos.ne'
  have hK' : (T : ℤ) + 2 ≤ K := by exact_mod_cast hK
  rcases (show (d + 2) / (K : ℤ) = 0 ∨ 1 ≤ (d + 2) / (K : ℤ) by omega) with h0 | h1
  · rw [h0]; simp [hd]
  · nlinarith

set_option autoImplicit false in
variable {D : _root_.Formalism.BasicNotions.D7} {j : ℕ} in
private lemma gapZ_nonneg_of_antitone' {p : ℕ} (a : Fin p → ℕ) (ha : Antitone a) (k : Fin p) :
    0 ≤ _root_.Formalism.MainNotions.WeightAlgebra.gapZ a k := by
  unfold _root_.Formalism.MainNotions.WeightAlgebra.gapZ
  split_ifs with h
  · have hk : k ≤ ⟨(k : ℕ) + 1, h⟩ := by rw [Fin.le_iff_val_le_val]; simp
    have := ha hk
    omega
  · positivity

set_option autoImplicit false in
variable {D : _root_.Formalism.BasicNotions.D7} {j : ℕ} in
private lemma mul_toNat_fdiv_le_of_le_of_nonneg {T K : ℕ} (hK : T + 2 ≤ K) {y a : ℤ} (hy : y ≤ a)
    (ha : 0 ≤ a) : (T : ℤ) * (y.fdiv K).toNat ≤ a := by
  have hKpos : (0 : ℤ) < K := by omega
  rw [Int.fdiv_eq_ediv_of_nonneg _ hKpos.le]
  by_cases hq : 0 ≤ y / (K : ℤ)
  · rw [Int.toNat_of_nonneg hq]
    have hle := Int.ediv_mul_le y hKpos.ne'
    have hK' : (T : ℤ) + 2 ≤ K := by exact_mod_cast hK
    nlinarith
  · rw [Int.toNat_of_nonpos (by omega)]
    simpa using ha

set_option autoImplicit false in
variable {D : _root_.Formalism.BasicNotions.D7} {j : ℕ} in

theorem _root_.GlobalTheory.RunWeightTest.isF'_fWt (ka : _root_.Formalism.MainNotions.WeightFamilies.Wt D j) (T nW nP : ℕ) (hW : Even nW)
    (hP : Even nP) :
    _root_.Formalism.MainNotions.WeightAlgebra.IsF' ka (_root_.Formalism.MainNotions.DIV.Cons.lWt D ka T nW hW) (_root_.Formalism.MainNotions.DIV.Cons.fWt D ka (_root_.Formalism.MainNotions.DIV.Cons.lWt D ka T nW hW) T nP hP) T nP := by
  have hK : T + 2 ≤ _root_.Formalism.MainNotions.WeightAlgebra.Tp D j T := by unfold _root_.Formalism.MainNotions.WeightAlgebra.Tp; omega
  unfold _root_.Formalism.MainNotions.WeightAlgebra.IsF'
  refine ⟨rfl, fun τ i => ?_, fun τ i => ?_⟩
  · have hl : (_root_.Formalism.MainNotions.DIV.Cons.lWt D ka T nW hW).aP τ = _root_.Formalism.MainNotions.DIV.Cons.ofGaps (_root_.Formalism.MainNotions.DIV.Cons.lGapP D ka T nW τ) := rfl
    show (_root_.Formalism.MainNotions.DIV.Cons.ofGaps (_root_.Formalism.MainNotions.DIV.Cons.fGapP D ka (_root_.Formalism.MainNotions.DIV.Cons.lWt D ka T nW hW) T τ) i : ℤ) = _
    refine ofGaps_eq_sub_mul _ _ _ T (fun k => ?_) i
    unfold _root_.Formalism.MainNotions.DIV.Cons.fGapP
    split_ifs with h
    · refine Int.toNat_of_nonneg ?_
      rw [hl, _root_.Formalism.MainNotions.DIV.Cons.gapZ_ofGaps]
      unfold _root_.Formalism.MainNotions.DIV.Cons.lGapP
      rw [if_pos h]
      have := mul_toNat_fdiv_add_two_le_of_add_two_le hK (gapZ_nonneg_of_antitone' _ (ka.aPlus_antitone τ) k)
      linarith
    · refine Int.toNat_of_nonneg ?_
      rw [hl, _root_.Formalism.MainNotions.DIV.Cons.ofGaps_last _ k h]
      unfold _root_.Formalism.MainNotions.DIV.Cons.lGapP
      rw [if_neg h]
      refine sub_nonneg.mpr (mul_toNat_fdiv_le_of_le_of_nonneg hK ?_ (by positivity))
      refine (sub_le_self _ ?_).trans (sub_le_self _ ?_) <;> positivity
  · have hl : (_root_.Formalism.MainNotions.DIV.Cons.lWt D ka T nW hW).aM τ = _root_.Formalism.MainNotions.DIV.Cons.ofGaps (_root_.Formalism.MainNotions.DIV.Cons.lGapM D ka T τ) := rfl
    show (_root_.Formalism.MainNotions.DIV.Cons.ofGaps (_root_.Formalism.MainNotions.DIV.Cons.fGapM D ka (_root_.Formalism.MainNotions.DIV.Cons.lWt D ka T nW hW) T τ) i : ℤ) = _
    refine ofGaps_eq_sub_mul _ _ _ T (fun k => ?_) i
    unfold _root_.Formalism.MainNotions.DIV.Cons.fGapM
    split_ifs with h
    · refine Int.toNat_of_nonneg ?_
      rw [hl, _root_.Formalism.MainNotions.DIV.Cons.gapZ_ofGaps]
      unfold _root_.Formalism.MainNotions.DIV.Cons.lGapM
      rw [if_pos h]
      have := mul_toNat_fdiv_add_two_le_of_add_two_le hK (gapZ_nonneg_of_antitone' _ (ka.aM_anti τ) k)
      linarith
    · refine Int.toNat_of_nonneg ?_
      rw [hl, _root_.Formalism.MainNotions.DIV.Cons.ofGaps_last _ k h]
      unfold _root_.Formalism.MainNotions.DIV.Cons.lGapM
      rw [if_neg h]
      have := mul_toNat_fdiv_le_of_le_of_nonneg hK le_rfl (show (0 : ℤ) ≤ ka.aM τ k by positivity)
      linarith

variable {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem main (Tp : ParamsT D L P) (hK : DV.KapDef D) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    WeightAlgebra.IsL D (kaR Tp hK j) (lR Tp hK j) Tp.TO Tp.nWn ∧
      WeightAlgebra.IsF' (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO Tp.nP ∧
      kaR Tp hK j = WeightAlgebra.wadd (fR Tp hK j) (WeightAlgebra.wsmul Tp.TO (lR Tp hK j)) := by
  have hF : WeightAlgebra.IsF' (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO Tp.nP := isF'_fWt _ _ _ _ _ _
  refine ⟨isL_lWt _ _ _ _ fun τ i hi => ?_, hF, ?_⟩
  · have ha := GlobalTheory.DepthBoundTest.two_sq_le_last Tp hK ⟨h1, h2⟩ τ i hi
    have hd : WeightFamilies.dimY D j = Tp.Dp := by rw [GlobalTheory.DepthBoundTest.dimY_eq_flag ⟨h1, h2⟩, Tp.Dp_eq]
    have hc : (((WeightFamilies.dimY D j : ℕ) : ℤ) + 2) * Tp.nWn + 2 * D.R.r ≤ Tp.TO := by
      rw [hd]; exact_mod_cast Tp.TO_nW
    have : (0 : ℤ) ≤ Tp.TO := by positivity
    nlinarith
  · have hn : (kaR Tp hK j).n = Tp.nP + Tp.TO * Tp.nWn := by
      rw [← Tp.split]; exact kaWt_n D hK _ j
    have hP : (kaR Tp hK j).aP = fun τ i => (fR Tp hK j).aP τ i + Tp.TO * (lR Tp hK j).aP τ i := by
      funext τ i; have := hF.2.1 τ i; zify; linarith
    have hM : (kaR Tp hK j).aM = fun τ i => (fR Tp hK j).aM τ i + Tp.TO * (lR Tp hK j).aM τ i := by
      funext τ i; have := hF.2.2 τ i; zify; linarith
    have ext : ∀ w w' : WeightFamilies.Wt D j, w.aP = w'.aP → w.aM = w'.aM → w.n = w'.n → w = w' := by
      rintro ⟨⟩ ⟨⟩ h h' h''
      simp only at h h' h''
      subst h h' h''
      rfl
    exact ext _ _ hP hM hn

end GlobalTheory.RunWeightTest
