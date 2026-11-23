import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WinSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSumPowMulFactorialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardCrossingSetEqGrassmannianDimStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormLowPolyEqNegSumCrossingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormLambdaEqTwoSumCrossingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumCoeffWindowCrossingFiberPointStatement

open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm GlobalTheory.FlagCurve Formalism.DegreeFormula

noncomputable section

namespace GlobalTheory.FlagCurve

theorem mono_apply {σ : Type} [DecidableEq σ] (R : Finset σ) (s : σ) : mono R s = if s ∈ R then 1 else 0 := by
  unfold mono
  rw [Finset.sum_apply']
  simp [Finsupp.single_apply]

theorem coeff_mono_X_mul {σ : Type} [DecidableEq σ] (R : Finset σ) (p : σ) (hp : p ∈ R)
    (ω : MvPolynomial σ ℝ) : coeff (mono R) (X p * ω) = coeff (mono (R.erase p)) ω := by
  have : mono R = mono (R.erase p) + Finsupp.single p 1 := by
    unfold mono; rw [Finset.sum_erase_add _ _ hp]
  rw [this, add_comm, coeff_X_mul]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem disjoint_win_cr (N j : ℕ) : Disjoint (winSet ι N j) (crSet ι N j) := by
  unfold winSet crSet
  rw [Finset.disjoint_filter]
  intro s _ h1 h2
  omega

theorem volExp_eq (N j : ℕ) :
    (volExp : (ι × Fin N × Fin N) →₀ ℕ) = mono (winSet ι N j ∪ crSet ι N j) := by
  ext s
  rw [mono_apply]
  simp only [volExp, Finsupp.coe_equivFunOnFinite_symm, winSet, crSet, Finset.mem_union,
    Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : s.2.1 < s.2.2
  · rw [if_pos h, if_pos]
    have : (s.2.1 : ℕ) < s.2.2 := h
    omega
  · rw [if_neg h, if_neg]
    tauto

theorem blkForm_eq (N j : ℕ) (τ : ι) :
    (blkForm j τ : FormPol ι N) = ∑ s ∈ (winSet ι N j).filter (fun s => s.1 = τ), X s := by
  rw [Finset.sum_filter]
  unfold winSet blkForm
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · rw [Fintype.sum_prod_type]
    simp
  · intro τ' _ hτ'
    simp [hτ']
  · simp

end GlobalTheory.FlagCurve

namespace GlobalTheory.FlagCurve
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem toForm_lamA_eq (N j : ℕ) :
    (toForm (lamA ι N j) : FormPol ι N) = 2 * ∑ s ∈ crSet ι N j, X s := GlobalTheory.T.form_lambda_eq_two_sum_crossing ι N j
theorem toForm_pLow_eq (N j : ℕ) (τ : ι) :
    (toForm (pLow j τ 1 : Pol ι N)) = -∑ s ∈ (crSet ι N j).filter (fun s => s.1 = τ), X s :=
  GlobalTheory.T.form_low_poly_eq_neg_sum_crossing ι N j τ
theorem coeff_mono_sum_pow_mul {σ : Type} [DecidableEq σ] (C R : Finset σ) (k : ℕ)
    (ω : MvPolynomial σ ℝ) : coeff (mono R) ((∑ s ∈ C, X s) ^ k * ω) =
      (k.factorial : ℝ) * ∑ U ∈ (R ∩ C).powersetCard k, coeff (mono (R \ U)) ω := GlobalTheory.T.coeff_sum_pow_mul_factorial C R k ω
theorem card_crSet (N j : ℕ) (hj : j ≤ N) : (crSet ι N j).card = dimGr ι N j := GlobalTheory.T.card_crossing_set_eq_grassmannian_dim ι N j hj
theorem core_sum (N j : ℕ) (h1 : 1 ≤ j) (h2 : j < N) :
    ∑ p ∈ winSet ι N j, ∑ q ∈ crSet ι N j,
      coeff (mono (insert q ((winSet ι N j).erase p))) (toForm (fibPt ι N j)) =
      (Fintype.card ι : ℝ) * (2 * (j : ℝ) - N) * coeff (mono (winSet ι N j)) (toForm (fibPt ι N j)) :=
  GlobalTheory.T.sum_coeff_window_crossing_fiber_point ι N j h1 h2
end GlobalTheory.FlagCurve

namespace GlobalTheory.FlagCurve
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sum_powersetCard_pred {σ : Type} [DecidableEq σ] (S : Finset σ) (hS : S.Nonempty) (g : Finset σ → ℝ) :
    ∑ U ∈ S.powersetCard (S.card - 1), g U = ∑ q ∈ S, g (S.erase q) := by
  symm
  refine Finset.sum_bij (fun q _ => S.erase q) ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.erase_subset _ _, Finset.card_erase_of_mem hq⟩
  · intro q1 h1 q2 h2 h
    exact (Finset.erase_inj S h1).mp h
  · intro U hU
    rw [Finset.mem_powersetCard] at hU
    have hc : (S \ U).card = 1 := by
      rw [Finset.card_sdiff_of_subset hU.1, hU.2]
      have := hS.card_pos
      omega
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hc
    have hqS : q ∈ S := (Finset.mem_sdiff.mp (hq ▸ Finset.mem_singleton_self q)).1
    refine ⟨q, hqS, ?_⟩
    ext x
    simp only [Finset.mem_erase]
    constructor
    · rintro ⟨hx, hxS⟩
      by_contra hxU
      have : x ∈ S \ U := Finset.mem_sdiff.mpr ⟨hxS, hxU⟩
      rw [hq, Finset.mem_singleton] at this
      exact hx this
    · intro hxU
      refine ⟨?_, hU.1 hxU⟩
      rintro rfl
      have : x ∈ S \ U := hq ▸ Finset.mem_singleton_self x
      exact (Finset.mem_sdiff.mp this).2 hxU
  · intro q hq; rfl
end GlobalTheory.FlagCurve

namespace GlobalTheory.FlagCurve

theorem erase_sdiff_erase {σ : Type} [DecidableEq σ] {W Cr : Finset σ} (hd : Disjoint W Cr) {p q : σ}
    (hp : p ∈ W) (hq : q ∈ Cr) : (W ∪ Cr).erase p \ Cr.erase q = insert q (W.erase p) := by
  have hpC : p ∉ Cr := Finset.disjoint_left.mp hd hp
  have hqW : q ∉ W := fun h => Finset.disjoint_left.mp hd h hq
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union, Finset.mem_insert]
  by_cases hxq : x = q
  · subst hxq; simp [hqW, hq]; rintro rfl; exact hpC hq
  · by_cases hxW : x ∈ W
    · have : x ∉ Cr := Finset.disjoint_left.mp hd hxW
      simp [hxq, hxW, this]
    · simp [hxq, hxW]

theorem erase_inter_of_mem_left {σ : Type} [DecidableEq σ] {W Cr : Finset σ} (hd : Disjoint W Cr) {p : σ}
    (hp : p ∈ W) : (W ∪ Cr).erase p ∩ Cr = Cr := by
  have hpC : p ∉ Cr := Finset.disjoint_left.mp hd hp
  ext x
  simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_union]
  constructor
  · exact fun h => h.2
  · intro hx; exact ⟨⟨fun h => hpC (h ▸ hx), Or.inr hx⟩, hx⟩

theorem erase_inter_of_mem_right {σ : Type} [DecidableEq σ] (W Cr : Finset σ) {q : σ} :
    (W ∪ Cr).erase q ∩ Cr = Cr.erase q := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_union]
  tauto

theorem erase_sdiff_erase_self {σ : Type} [DecidableEq σ] {W Cr : Finset σ} (hd : Disjoint W Cr) {q : σ}
    (hq : q ∈ Cr) : (W ∪ Cr).erase q \ Cr.erase q = W := by
  have hqW : q ∉ W := fun h => Finset.disjoint_left.mp hd h hq
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union]
  by_cases hxq : x = q
  · subst hxq; simp [hqW]
  · by_cases hxW : x ∈ W
    · have : x ∉ Cr := Finset.disjoint_left.mp hd hxW
      simp [hxq, hxW, this]
    · simp [hxq, hxW]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem toForm_curveCl (N j : ℕ) :
    (toForm (curveCl ι N j) : FormPol ι N) =
      C (2 ^ (dimGr ι N j - 1)) * ((∑ s ∈ crSet ι N j, X s) ^ (dimGr ι N j - 1) * toForm (fibPt ι N j)) := by
  have : (toForm (curveCl ι N j) : FormPol ι N) =
      toForm (lamA ι N j) ^ (dimGr ι N j - 1) * toForm (fibPt ι N j) := by
    simp only [curveCl, toForm, map_mul, map_pow]
  rw [this, toForm_lamA_eq, mul_pow, mul_assoc]
  congr 1
  rw [map_pow, map_ofNat]

theorem coeff_curveCl_win (N j : ℕ) (hj : j ≤ N) (hne : (crSet ι N j).Nonempty) {p : ι × Fin N × Fin N}
    (hp : p ∈ winSet ι N j) :
    coeff (mono ((winSet ι N j ∪ crSet ι N j).erase p)) (toForm (curveCl ι N j) : FormPol ι N) =
      2 ^ (dimGr ι N j - 1) * ((dimGr ι N j - 1).factorial : ℝ) *
        ∑ q ∈ crSet ι N j, coeff (mono (insert q ((winSet ι N j).erase p))) (toForm (fibPt ι N j)) := by
  rw [toForm_curveCl, coeff_C_mul, coeff_mono_sum_pow_mul,
    erase_inter_of_mem_left (disjoint_win_cr N j) hp, ← card_crSet N j hj, sum_powersetCard_pred _ hne,
    mul_assoc]
  congr 2
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [erase_sdiff_erase (disjoint_win_cr N j) hp hq]

theorem coeff_curveCl_cr (N j : ℕ) (hj : j ≤ N) {q : ι × Fin N × Fin N} (hq : q ∈ crSet ι N j) :
    coeff (mono ((winSet ι N j ∪ crSet ι N j).erase q)) (toForm (curveCl ι N j) : FormPol ι N) =
      2 ^ (dimGr ι N j - 1) * ((dimGr ι N j - 1).factorial : ℝ) *
        coeff (mono (winSet ι N j)) (toForm (fibPt ι N j)) := by
  rw [toForm_curveCl, coeff_C_mul, coeff_mono_sum_pow_mul, erase_inter_of_mem_right,
    ← card_crSet N j hj, ← Finset.card_erase_of_mem hq, Finset.powersetCard_self, Finset.sum_singleton,
    erase_sdiff_erase_self (disjoint_win_cr N j) hq, mul_assoc]

theorem blk_curve_main (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ) (h1 : 1 ≤ j) (h2 : j < N) :
    ∑ τ : ι, formDeg (blkForm j τ * toForm (curveCl ι N j)) =
      (1 / (j : ℝ) - 1 / ((N : ℝ) - j)) *
        ∑ τ : ι, formDeg (toForm (pLow j τ 1 * curveCl ι N j) : FormPol ι N) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hd : (crSet ι N j).card = dimGr ι N j := card_crSet N j h2.le
  have hCr : (crSet ι N j).Nonempty := by
    rw [← Finset.card_pos, hd]
    unfold dimGr
    have : 0 < Fintype.card ι := Fintype.card_pos
    have : 0 < N - j := Nat.sub_pos_of_lt h2
    positivity
  set K : ℝ := 2 ^ (dimGr ι N j - 1) * ((dimGr ι N j - 1).factorial : ℝ) with hK
  set c : ℝ := coeff (mono (winSet ι N j)) (toForm (fibPt ι N j) : FormPol ι N) with hc
  have hL : ∑ τ : ι, formDeg (blkForm j τ * toForm (curveCl ι N j)) =
      K * ((Fintype.card ι : ℝ) * (2 * (j : ℝ) - N) * c) / (superFact N : ℝ) ^ Fintype.card ι := by
    simp only [formDeg, volExp_eq N j (ι := ι)]
    rw [← Finset.sum_div]
    congr 1
    have step : ∀ τ : ι, coeff (mono (winSet ι N j ∪ crSet ι N j)) (blkForm j τ * toForm (curveCl ι N j)) =
        ∑ p ∈ (winSet ι N j).filter (fun s => s.1 = τ),
          coeff (mono ((winSet ι N j ∪ crSet ι N j).erase p)) (toForm (curveCl ι N j) : FormPol ι N) := by
      intro τ
      rw [blkForm_eq, Finset.sum_mul, coeff_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      exact coeff_mono_X_mul _ _ (Finset.mem_union_left _ (Finset.mem_filter.mp hp).1) _
    simp only [step]
    rw [Finset.sum_fiberwise (winSet ι N j) (fun s => s.1)
      (fun p => coeff (mono ((winSet ι N j ∪ crSet ι N j).erase p)) (toForm (curveCl ι N j) : FormPol ι N))]
    rw [Finset.sum_congr rfl fun p hp => coeff_curveCl_win N j h2.le hCr hp, ← Finset.mul_sum,
      core_sum N j h1 h2]
  have hR : ∑ τ : ι, formDeg (toForm (pLow j τ 1 * curveCl ι N j) : FormPol ι N) =
      -((dimGr ι N j : ℝ) * K * c) / (superFact N : ℝ) ^ Fintype.card ι := by
    simp only [formDeg, volExp_eq N j (ι := ι)]
    rw [← Finset.sum_div]
    congr 1
    have step : ∀ τ : ι, coeff (mono (winSet ι N j ∪ crSet ι N j))
        (toForm (pLow j τ 1 * curveCl ι N j) : FormPol ι N) =
        -∑ q ∈ (crSet ι N j).filter (fun s => s.1 = τ),
          coeff (mono ((winSet ι N j ∪ crSet ι N j).erase q)) (toForm (curveCl ι N j) : FormPol ι N) := by
      intro τ
      rw [show (toForm (pLow j τ 1 * curveCl ι N j) : FormPol ι N) =
          toForm (pLow j τ 1 : Pol ι N) * toForm (curveCl ι N j) from map_mul _ _ _]
      rw [toForm_pLow_eq, neg_mul, coeff_neg, Finset.sum_mul, coeff_sum]
      congr 1
      refine Finset.sum_congr rfl fun p hp => ?_
      exact coeff_mono_X_mul _ _ (Finset.mem_union_right _ (Finset.mem_filter.mp hp).1) _
    simp only [step]
    rw [Finset.sum_neg_distrib, Finset.sum_fiberwise (crSet ι N j) (fun s => s.1)
      (fun p => coeff (mono ((winSet ι N j ∪ crSet ι N j).erase p)) (toForm (curveCl ι N j) : FormPol ι N))]
    rw [Finset.sum_congr rfl fun q hq => coeff_curveCl_cr N j h2.le hq, Finset.sum_const, hd, nsmul_eq_mul, hK, hc]
    ring
  rw [hL, hR]
  have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hNj : (N : ℝ) - j ≠ 0 := by
    have : (j : ℝ) < N := by exact_mod_cast h2
    linarith
  have hdR : (dimGr ι N j : ℝ) = (Fintype.card ι : ℝ) * ((j : ℝ) * ((N : ℝ) - j)) := by
    unfold dimGr; push_cast [Nat.cast_sub h2.le]; ring
  rw [hdR]
  have hsf : ((superFact N : ℝ) ^ Fintype.card ι) ≠ 0 := by
    apply pow_ne_zero
    unfold superFact
    exact_mod_cast (Finset.prod_pos fun k _ => Nat.factorial_pos k).ne'
  field_simp
  ring

end GlobalTheory.FlagCurve
