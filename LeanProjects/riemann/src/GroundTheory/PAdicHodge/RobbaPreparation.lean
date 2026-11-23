import Mathlib
import GroundTheory.PAdicHodge.RobbaSeries
import GroundTheory.PAdicHodge.HighIndexSingleZeroOne
import GroundTheory.PAdicHodge.RobbaBounded
import GroundTheory.PAdicHodge.RobbaNewton
import GroundTheory.PAdicHodge.RobbaClosed
import GroundTheory.PAdicHodge.RobbaDivision
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace Laurent

variable {a : ℤ → K} {ρ : ℝ}

theorem dominant_zero_of_gaussNorm_sub_one_lt (hρ : 0 < ρ) {u : ℤ → K} (hu : ConvergesAt u ρ)
    (h1 : gaussNorm (u - Pi.single 0 1) ρ < 1) :
    u ≠ 0 ∧ lowIndex u ρ = 0 ∧ highIndex u ρ = 0 := by
  have hv : ConvergesAt (u - Pi.single 0 1) ρ := hu.sub hρ (convergesAt_single 0 1 ρ)
  have hw : ∀ m : ℤ, ‖(u - (Pi.single 0 (1 : K) : ℤ → K)) m‖ * ρ ^ m < 1 := fun m =>
    (hv.le_gaussNorm m).trans_lt h1
  have hu0 : ‖u 0‖ = 1 := by
    have := hw 0
    simp only [Pi.sub_apply, Pi.single_eq_same, zpow_zero, mul_one] at this
    have e : u 0 = 1 + (u 0 - 1) := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact this.ne'),
      norm_one, max_eq_left this.le]
  have hne : u ≠ 0 := fun h => by rw [h] at hu0; simp at hu0
  have hweight : ∀ m, m ≠ 0 → ‖u m‖ * ρ ^ m < ‖u 0‖ * ρ ^ (0 : ℤ) := by
    intro m hm
    have := hw m
    simp only [Pi.sub_apply, Pi.single_eq_of_ne hm, sub_zero] at this
    rw [hu0, zpow_zero, mul_one]; exact this
  have hg : gaussNorm u ρ = 1 := by
    refine le_antisymm (gaussNorm_le fun m => ?_) ?_
    · by_cases hm : m = 0
      · subst hm; rw [hu0, zpow_zero, mul_one]
      · have := hweight m hm; rw [hu0, zpow_zero, mul_one] at this; exact this.le
    · have := hu.le_gaussNorm 0; rwa [hu0, zpow_zero, mul_one] at this
  have hdom : domSet u ρ = {0} := by
    ext m
    simp only [domSet, Set.mem_setOf_eq, hg, Set.mem_singleton_iff]
    constructor
    · intro h; by_contra hm; have := hweight m hm; rw [hu0, zpow_zero, mul_one] at this; linarith
    · rintro rfl; rw [hu0, zpow_zero, mul_one]
  exact ⟨hne, by rw [lowIndex, hdom, csInf_singleton], by rw [highIndex, hdom, csSup_singleton]⟩

theorem dominant_of_perturb {P₀ P : ℤ → K} {N : ℤ} {F : ℝ} (hρ : 0 < ρ)
    (hN : ‖P₀ N‖ * ρ ^ N = F) (hF : 0 < F) (hdom : ∀ i, ‖P₀ i‖ * ρ ^ i ≤ F)
    (hδ : ∀ i, ‖(P - P₀) i‖ * ρ ^ i < F) :
    ‖P N‖ * ρ ^ N = F ∧ ∀ i, ‖P i‖ * ρ ^ i ≤ F := by
  have hρN : 0 < ρ ^ N := zpow_pos hρ N
  constructor
  · have e : P N = P₀ N + (P - P₀) N := by simp
    have h1 : ‖(P - P₀) N‖ < ‖P₀ N‖ := by
      rw [← mul_lt_mul_iff_of_pos_right hρN, hN]; exact hδ N
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne', max_eq_left h1.le, hN]
  · intro i
    have e : P i = P₀ i + (P - P₀) i := by simp
    rw [e]
    calc ‖P₀ i + (P - P₀) i‖ * ρ ^ i ≤ max ‖P₀ i‖ ‖(P - P₀) i‖ * ρ ^ i :=
          mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (by positivity)
      _ = max (‖P₀ i‖ * ρ ^ i) (‖(P - P₀) i‖ * ρ ^ i) := max_mul_of_nonneg _ _ (by positivity)
      _ ≤ F := max_le (hdom i) (hδ i).le

end Laurent

namespace Laurent

section Preparation

variable {τ₁ τ₂ : ℝ} {L H : ℤ}

def DivHyp (τ₁ τ₂ : ℝ) (L H : ℤ) (P h : ℤ → K) : Prop :=
  0 < τ₁ ∧ τ₁ ≤ τ₂ ∧ L ≤ H ∧ (∀ n, n < L ∨ H < n → P n = 0) ∧ P L ≠ 0 ∧ P H ≠ 0 ∧
    (∀ i, ‖P i‖ * τ₁ ^ i ≤ ‖P L‖ * τ₁ ^ L) ∧ (∀ i, ‖P i‖ * τ₂ ^ i ≤ ‖P H‖ * τ₂ ^ H) ∧
    ConvergesAt h τ₁ ∧ ConvergesAt h τ₂

def DivSpec (τ₁ τ₂ : ℝ) (L H : ℤ) (P h : ℤ → K) (qr : (ℤ → K) × (ℤ → K)) : Prop :=
  ConvergesAt qr.1 τ₁ ∧ ConvergesAt qr.1 τ₂ ∧ (∀ n, n < L ∨ H < n → qr.2 n = 0) ∧
    h = cmul qr.1 P + qr.2 ∧
    gaussNorm qr.1 τ₁ ≤ max (gaussNorm h τ₁ / gaussNorm P τ₁) (gaussNorm h τ₂ / gaussNorm P τ₂) ∧
    gaussNorm qr.1 τ₂ ≤ max (gaussNorm h τ₁ / gaussNorm P τ₁) (gaussNorm h τ₂ / gaussNorm P τ₂) ∧
    gaussNorm qr.2 τ₁ ≤ max (gaussNorm h τ₁ / gaussNorm P τ₁) (gaussNorm h τ₂ / gaussNorm P τ₂) *
      gaussNorm P τ₁ ∧
    gaussNorm qr.2 τ₂ ≤ max (gaussNorm h τ₁ / gaussNorm P τ₁) (gaussNorm h τ₂ / gaussNorm P τ₂) *
      gaussNorm P τ₂

theorem exists_divSpec (τ₁ τ₂ : ℝ) (L H : ℤ) (P h : ℤ → K) :
    ∃ qr : (ℤ → K) × (ℤ → K), DivHyp τ₁ τ₂ L H P h → DivSpec τ₁ τ₂ L H P h qr := by
  by_cases hh : DivHyp τ₁ τ₂ L H P h
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hh
    obtain ⟨q, r, hq⟩ := weierstrass_division h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact ⟨(q, r), fun _ => hq⟩
  · exact ⟨(0, 0), fun h => absurd h hh⟩

def wdiv (τ₁ τ₂ : ℝ) (L H : ℤ) (P h : ℤ → K) : (ℤ → K) × (ℤ → K) :=
  Classical.choose (exists_divSpec τ₁ τ₂ L H P h)

theorem wdiv_spec {P h : ℤ → K} (hh : DivHyp τ₁ τ₂ L H P h) :
    DivSpec τ₁ τ₂ L H P h (wdiv τ₁ τ₂ L H P h) :=
  Classical.choose_spec (exists_divSpec τ₁ τ₂ L H P h) hh

def prepSeq (τ₁ τ₂ : ℝ) (L H : ℤ) (f : ℤ → K) : ℕ → (ℤ → K) × (ℤ → K)
  | 0 => (trunc f (Set.Icc L H), Pi.single 0 1)
  | k + 1 =>
    ((prepSeq τ₁ τ₂ L H f k).1 + (wdiv τ₁ τ₂ L H (prepSeq τ₁ τ₂ L H f k).1
        (f - cmul (prepSeq τ₁ τ₂ L H f k).1 (prepSeq τ₁ τ₂ L H f k).2)).2,
      (prepSeq τ₁ τ₂ L H f k).2 + (wdiv τ₁ τ₂ L H (prepSeq τ₁ τ₂ L H f k).1
        (f - cmul (prepSeq τ₁ τ₂ L H f k).1 (prepSeq τ₁ τ₂ L H f k).2)).1)

end Preparation

end Laurent

namespace Laurent

section PrepInvariant

variable {τ₁ τ₂ : ℝ} {L H : ℤ} {f : ℤ → K} {F₁ F₂ lam : ℝ}

def PrepInv (τ₁ τ₂ : ℝ) (L H : ℤ) (f : ℤ → K) (F₁ F₂ lam : ℝ) (k : ℕ) : Prop :=
  (∀ n, n < L ∨ H < n → (prepSeq τ₁ τ₂ L H f k).1 n = 0) ∧
  gaussNorm ((prepSeq τ₁ τ₂ L H f k).1 - trunc f (Set.Icc L H)) τ₁ ≤ lam * F₁ ∧
  gaussNorm ((prepSeq τ₁ τ₂ L H f k).1 - trunc f (Set.Icc L H)) τ₂ ≤ lam * F₂ ∧
  ConvergesAt (prepSeq τ₁ τ₂ L H f k).2 τ₁ ∧ ConvergesAt (prepSeq τ₁ τ₂ L H f k).2 τ₂ ∧
  gaussNorm ((prepSeq τ₁ τ₂ L H f k).2 - Pi.single 0 1) τ₁ ≤ lam ∧
  gaussNorm ((prepSeq τ₁ τ₂ L H f k).2 - Pi.single 0 1) τ₂ ≤ lam ∧
  gaussNorm (f - cmul (prepSeq τ₁ τ₂ L H f k).1 (prepSeq τ₁ τ₂ L H f k).2) τ₁ ≤
    lam ^ (k + 1) * F₁ ∧
  gaussNorm (f - cmul (prepSeq τ₁ τ₂ L H f k).1 (prepSeq τ₁ τ₂ L H f k).2) τ₂ ≤
    lam ^ (k + 1) * F₂

variable (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂) (hLH : L ≤ H) (h₁ : ConvergesAt f τ₁)
  (h₂ : ConvergesAt f τ₂) (hF₁ : 0 < F₁) (hF₂ : 0 < F₂)
  (hL : ‖f L‖ * τ₁ ^ L = F₁) (hL' : ∀ i, ‖f i‖ * τ₁ ^ i ≤ F₁)
  (hH : ‖f H‖ * τ₂ ^ H = F₂) (hH' : ∀ i, ‖f i‖ * τ₂ ^ i ≤ F₂)
  (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
  (he₁ : gaussNorm (f - trunc f (Set.Icc L H)) τ₁ ≤ lam * F₁)
  (he₂ : gaussNorm (f - trunc f (Set.Icc L H)) τ₂ ≤ lam * F₂)
include hτ₁ hτ hLH h₁ h₂ hF₁ hF₂ hL hL' hH hH' hlam0 hlam1 he₁ he₂

theorem prepInv_zero : PrepInv τ₁ τ₂ L H f F₁ F₂ lam 0 := by
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ
  refine ⟨fun n hn => ?_, ?_, ?_, convergesAt_single 0 1 τ₁, convergesAt_single 0 1 τ₂, ?_, ?_,
    ?_, ?_⟩
  · have : n ∉ Set.Icc L H := fun hm => by simp only [Set.mem_Icc] at hm; omega
    simp [prepSeq, trunc, Set.indicator_of_notMem this]
  · simp only [prepSeq, sub_self, gaussNorm_zero]; positivity
  · simp only [prepSeq, sub_self, gaussNorm_zero]; positivity
  · simp only [prepSeq, sub_self, gaussNorm_zero]; exact hlam0
  · simp only [prepSeq, sub_self, gaussNorm_zero]; exact hlam0
  · simp only [prepSeq, cmul_single_zero_one, zero_add, pow_one]; exact he₁
  · simp only [prepSeq, cmul_single_zero_one, zero_add, pow_one]; exact he₂

set_option maxHeartbeats 1000000 in

theorem prepInv_succ {k : ℕ} (hk : PrepInv τ₁ τ₂ L H f F₁ F₂ lam k) :
    PrepInv τ₁ τ₂ L H f F₁ F₂ lam (k + 1) ∧
    gaussNorm ((prepSeq τ₁ τ₂ L H f (k + 1)).1 - (prepSeq τ₁ τ₂ L H f k).1) τ₁ ≤
      lam ^ (k + 1) * F₁ ∧
    gaussNorm ((prepSeq τ₁ τ₂ L H f (k + 1)).1 - (prepSeq τ₁ τ₂ L H f k).1) τ₂ ≤
      lam ^ (k + 1) * F₂ ∧
    gaussNorm ((prepSeq τ₁ τ₂ L H f (k + 1)).2 - (prepSeq τ₁ τ₂ L H f k).2) τ₁ ≤ lam ^ (k + 1) ∧
    gaussNorm ((prepSeq τ₁ τ₂ L H f (k + 1)).2 - (prepSeq τ₁ τ₂ L H f k).2) τ₂ ≤ lam ^ (k + 1) := by
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ
  obtain ⟨hs, hb1, hb2, hu1, hu2, hv1, hv2, hd1, hd2⟩ := hk
  set P := (prepSeq τ₁ τ₂ L H f k).1 with hPdef
  set u := (prepSeq τ₁ τ₂ L H f k).2 with hudef
  set P₀ := trunc f (Set.Icc L H)
  set e := f - cmul P u with hedef
  have hP₀s : ∀ n, n < L ∨ H < n → P₀ n = 0 := fun n hn => by
    have : n ∉ Set.Icc L H := fun hm => by simp only [Set.mem_Icc] at hm; omega
    simp [P₀, trunc, Set.indicator_of_notMem this]
  have hδs : ∀ n, n < L ∨ H < n → (P - P₀) n = 0 := fun n hn => by
    simp [hs n hn, hP₀s n hn]
  have hP₀L : P₀ L = f L := by simp [P₀, trunc, Set.indicator_of_mem (show L ∈ Set.Icc L H from ⟨le_rfl, hLH⟩)]
  have hP₀H : P₀ H = f H := by simp [P₀, trunc, Set.indicator_of_mem (show H ∈ Set.Icc L H from ⟨hLH, le_rfl⟩)]

  have hdom1 := dominant_of_perturb (P₀ := P₀) (P := P) (N := L) hτ₁ (by rw [hP₀L]; exact hL) hF₁
    (fun i => ((mul_le_mul_of_nonneg_right (norm_trunc_le _ i) (by positivity))).trans (hL' i))
    (fun i => ((convergesAt_of_support hδs τ₁).le_gaussNorm i).trans_lt
      (hb1.trans_lt (by nlinarith)))
  have hdom2 := dominant_of_perturb (P₀ := P₀) (P := P) (N := H) hτ₂ (by rw [hP₀H]; exact hH) hF₂
    (fun i => ((mul_le_mul_of_nonneg_right (norm_trunc_le _ i) (by positivity))).trans (hH' i))
    (fun i => ((convergesAt_of_support hδs τ₂).le_gaussNorm i).trans_lt
      (hb2.trans_lt (by nlinarith)))
  have hPL : P L ≠ 0 := fun h0 => by
    have := hdom1.1; rw [h0, norm_zero, zero_mul] at this; linarith
  have hPH : P H ≠ 0 := fun h0 => by
    have := hdom2.1; rw [h0, norm_zero, zero_mul] at this; linarith
  have hin : ∀ i, ‖P i‖ * τ₁ ^ i ≤ ‖P L‖ * τ₁ ^ L := fun i => by rw [hdom1.1]; exact hdom1.2 i
  have hout : ∀ i, ‖P i‖ * τ₂ ^ i ≤ ‖P H‖ * τ₂ ^ H := fun i => by rw [hdom2.1]; exact hdom2.2 i
  have hG1 : gaussNorm P τ₁ = F₁ := by rw [gaussNorm_eq_of_dominant hs hin, hdom1.1]
  have hG2 : gaussNorm P τ₂ = F₂ := by rw [gaussNorm_eq_of_dominant hs hout, hdom2.1]
  have hPc : ∀ ρ, ConvergesAt P ρ := convergesAt_of_support hs
  have he1 : ConvergesAt e τ₁ := h₁.sub hτ₁ ((hPc τ₁).cmul hτ₁ hu1)
  have he2 : ConvergesAt e τ₂ := h₂.sub hτ₂ ((hPc τ₂).cmul hτ₂ hu2)
  have hhyp : DivHyp τ₁ τ₂ L H P e := ⟨hτ₁, hτ, hLH, hs, hPL, hPH, hin, hout, he1, he2⟩
  obtain ⟨hq1, hq2, hrs, hediv, hqb1, hqb2, hrb1, hrb2⟩ := wdiv_spec hhyp
  set q := (wdiv τ₁ τ₂ L H P e).1
  set r := (wdiv τ₁ τ₂ L H P e).2
  rw [hG1, hG2] at hqb1 hqb2 hrb1 hrb2
  set M := max (gaussNorm e τ₁ / F₁) (gaussNorm e τ₂ / F₂) with hM
  have hM0 : 0 ≤ M := le_max_of_le_left (div_nonneg (gaussNorm_nonneg hτ₁) hF₁.le)
  have hMk : M ≤ lam ^ (k + 1) := max_le ((div_le_iff₀ hF₁).2 hd1) ((div_le_iff₀ hF₂).2 hd2)
  have hpow : lam ^ (k + 1) ≤ lam := pow_le_of_le_one hlam0 hlam1.le (by omega)
  have hMlam : M ≤ lam := hMk.trans hpow
  have hrc : ∀ ρ, ConvergesAt r ρ := convergesAt_of_support hrs
  have hnext : prepSeq τ₁ τ₂ L H f (k + 1) = (P + r, u + q) := rfl

  have hδ1 := convergesAt_single 0 (1 : K) τ₁
  have herr : f - cmul (P + r) (u + q) = -(cmul r ((u - Pi.single 0 1) + q)) := by
    have e1 : cmul (P + r) (u + q) = cmul P u + cmul P q + cmul r (u + q) := by
      rw [add_cmul hτ₁ (hPc τ₁) (hrc τ₁) (hu1.add hτ₁ hq1), cmul_add hτ₁ (hPc τ₁) hu1 hq1]
    have e2 : cmul r ((u - Pi.single 0 1) + q) = cmul r (u + q) - r := by
      rw [show (u - Pi.single 0 1) + q = (u + q) + -Pi.single 0 1 by abel,
        cmul_add hτ₁ (hrc τ₁) (hu1.add hτ₁ hq1) hδ1.neg, cmul_neg, cmul_single_zero_one]
      abel
    have e3 : e = cmul P q + r := by rw [hediv, cmul_comm]
    rw [e1, e2]
    have : f = e + cmul P u := by rw [hedef]; abel
    rw [this, e3]; abel
  have hw1 : ConvergesAt ((u - Pi.single 0 1) + q) τ₁ := (hu1.sub hτ₁ hδ1).add hτ₁ hq1
  have hw2 : ConvergesAt ((u - Pi.single 0 1) + q) τ₂ :=
    (hu2.sub hτ₂ (convergesAt_single 0 1 τ₂)).add hτ₂ hq2
  have hwb1 : gaussNorm ((u - Pi.single 0 1) + q) τ₁ ≤ lam :=
    (gaussNorm_add_le hτ₁ (hu1.sub hτ₁ hδ1) hq1).trans (max_le hv1 (hqb1.trans hMlam))
  have hwb2 : gaussNorm ((u - Pi.single 0 1) + q) τ₂ ≤ lam :=
    (gaussNorm_add_le hτ₂ (hu2.sub hτ₂ (convergesAt_single 0 1 τ₂)) hq2).trans
      (max_le hv2 (hqb2.trans hMlam))
  have hrb1' : gaussNorm r τ₁ ≤ lam ^ (k + 1) * F₁ := hrb1.trans (by nlinarith)
  have hrb2' : gaussNorm r τ₂ ≤ lam ^ (k + 1) * F₂ := hrb2.trans (by nlinarith)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro n hn; rw [hnext]; simp [hs n hn, hrs n hn]
  · rw [hnext, show P + r - P₀ = (P - P₀) + r by abel]
    exact (gaussNorm_add_le hτ₁ (convergesAt_of_support hδs τ₁) (hrc τ₁)).trans
      (max_le hb1 (hrb1'.trans (by nlinarith)))
  · rw [hnext, show P + r - P₀ = (P - P₀) + r by abel]
    exact (gaussNorm_add_le hτ₂ (convergesAt_of_support hδs τ₂) (hrc τ₂)).trans
      (max_le hb2 (hrb2'.trans (by nlinarith)))
  · rw [hnext]; exact hu1.add hτ₁ hq1
  · rw [hnext]; exact hu2.add hτ₂ hq2
  · rw [hnext, show u + q - Pi.single 0 1 = (u - Pi.single 0 1) + q by abel]; exact hwb1
  · rw [hnext, show u + q - Pi.single 0 1 = (u - Pi.single 0 1) + q by abel]; exact hwb2
  · rw [hnext]
    show gaussNorm (f - cmul (P + r) (u + q)) τ₁ ≤ lam ^ (k + 1 + 1) * F₁
    rw [herr, gaussNorm_neg]
    calc gaussNorm (cmul r ((u - Pi.single 0 1) + q)) τ₁
        ≤ gaussNorm r τ₁ * gaussNorm ((u - Pi.single 0 1) + q) τ₁ :=
          gaussNorm_cmul_le hτ₁ (hrc τ₁) hw1
      _ ≤ (lam ^ (k + 1) * F₁) * lam :=
          mul_le_mul hrb1' hwb1 (gaussNorm_nonneg hτ₁) (by positivity)
      _ = lam ^ (k + 1 + 1) * F₁ := by ring
  · rw [hnext]
    show gaussNorm (f - cmul (P + r) (u + q)) τ₂ ≤ lam ^ (k + 1 + 1) * F₂
    rw [herr, gaussNorm_neg]
    calc gaussNorm (cmul r ((u - Pi.single 0 1) + q)) τ₂
        ≤ gaussNorm r τ₂ * gaussNorm ((u - Pi.single 0 1) + q) τ₂ :=
          gaussNorm_cmul_le hτ₂ (hrc τ₂) hw2
      _ ≤ (lam ^ (k + 1) * F₂) * lam :=
          mul_le_mul hrb2' hwb2 (gaussNorm_nonneg hτ₂) (by positivity)
      _ = lam ^ (k + 1 + 1) * F₂ := by ring
  · rw [hnext, show P + r - P = r by abel]; exact hrb1'
  · rw [hnext, show P + r - P = r by abel]; exact hrb2'
  · rw [hnext, show u + q - u = q by abel]; exact hqb1.trans hMk
  · rw [hnext, show u + q - u = q by abel]; exact hqb2.trans hMk

theorem prepInv_all : ∀ k, PrepInv τ₁ τ₂ L H f F₁ F₂ lam k
  | 0 => prepInv_zero hτ₁ hτ hLH h₁ h₂ hF₁ hF₂ hL hL' hH hH' hlam0 hlam1 he₁ he₂
  | k + 1 => (prepInv_succ hτ₁ hτ hLH h₁ h₂ hF₁ hF₂ hL hL' hH hH' hlam0 hlam1 he₁ he₂
      (prepInv_all k)).1

end PrepInvariant

end Laurent

namespace Laurent

section PrepLimit

variable {τ₁ τ₂ : ℝ} {L H : ℤ} {f : ℤ → K} {F₁ F₂ lam : ℝ}

theorem tendsto_pow_succ_mul {lam F : ℝ} (h0 : 0 ≤ lam) (h1 : lam < 1) :
    Tendsto (fun k : ℕ => lam ^ (k + 1) * F) atTop (𝓝 0) := by
  have := ((tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).comp (tendsto_add_atTop_nat 1)).mul_const F
  simpa [Function.comp] using this

variable (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂) (hLH : L ≤ H) (h₁ : ConvergesAt f τ₁)
  (h₂ : ConvergesAt f τ₂) (hF₁ : 0 < F₁) (hF₂ : 0 < F₂)
  (hL : ‖f L‖ * τ₁ ^ L = F₁) (hL' : ∀ i, ‖f i‖ * τ₁ ^ i ≤ F₁)
  (hH : ‖f H‖ * τ₂ ^ H = F₂) (hH' : ∀ i, ‖f i‖ * τ₂ ^ i ≤ F₂)
  (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
  (he₁ : gaussNorm (f - trunc f (Set.Icc L H)) τ₁ ≤ lam * F₁)
  (he₂ : gaussNorm (f - trunc f (Set.Icc L H)) τ₂ ≤ lam * F₂)
include hτ₁ hτ hLH h₁ h₂ hF₁ hF₂ hL hL' hH hH' hlam0 hlam1 he₁ he₂

set_option maxHeartbeats 1000000 in
theorem prep_limit : ∃ P u : ℤ → K, (∀ n, n < L ∨ H < n → P n = 0) ∧ ConvergesAt u τ₁ ∧
    ConvergesAt u τ₂ ∧ gaussNorm (u - Pi.single 0 1) τ₁ < 1 ∧
    gaussNorm (u - Pi.single 0 1) τ₂ < 1 ∧ f = cmul P u := by
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ
  have inv := prepInv_all hτ₁ hτ hLH h₁ h₂ hF₁ hF₂ hL hL' hH hH' hlam0 hlam1 he₁ he₂
  have stp := fun k => (prepInv_succ hτ₁ hτ hLH h₁ h₂ hF₁ hF₂ hL hL' hH hH' hlam0 hlam1 he₁ he₂
    (inv k)).2
  set Pk : ℕ → ℤ → K := fun k => (prepSeq τ₁ τ₂ L H f k).1 with hPk
  set uk : ℕ → ℤ → K := fun k => (prepSeq τ₁ τ₂ L H f k).2 with huk
  have hPks : ∀ k n, n < L ∨ H < n → Pk k n = 0 := fun k => (inv k).1
  have hPc : ∀ k ρ, ConvergesAt (Pk k) ρ := fun k => convergesAt_of_support (hPks k)
  have hdPc : ∀ j ρ, ConvergesAt (Pk (j + 1) - Pk j) ρ := fun j ρ =>
    convergesAt_of_support (A := L) (B := H)
      (fun n (hn : n < L ∨ H < n) => by simp [hPks (j + 1) n hn, hPks j n hn]) ρ
  have hCP1 : UCauchy Pk τ₁ := UCauchy.of_gaussNorm hτ₁ (fun j => hdPc j τ₁)
    (squeeze_zero (fun _ => gaussNorm_nonneg hτ₁) (fun j => (stp j).1)
      (tendsto_pow_succ_mul hlam0 hlam1))
  have hu1 : ∀ k, ConvergesAt (uk k) τ₁ := fun k => (inv k).2.2.2.1
  have hu2 : ∀ k, ConvergesAt (uk k) τ₂ := fun k => (inv k).2.2.2.2.1
  have hCu1 : UCauchy uk τ₁ := UCauchy.of_gaussNorm hτ₁ (fun j => (hu1 (j + 1)).sub hτ₁ (hu1 j))
    (squeeze_zero (fun _ => gaussNorm_nonneg hτ₁) (fun j => by simpa using (stp j).2.2.1)
      (by simpa using tendsto_pow_succ_mul (F := 1) hlam0 hlam1))
  have hCu2 : UCauchy uk τ₂ := UCauchy.of_gaussNorm hτ₂ (fun j => (hu2 (j + 1)).sub hτ₂ (hu2 j))
    (squeeze_zero (fun _ => gaussNorm_nonneg hτ₂) (fun j => by simpa using (stp j).2.2.2)
      (by simpa using tendsto_pow_succ_mul (F := 1) hlam0 hlam1))
  set P := limSeq Pk
  set u := limSeq uk
  have hPs : ∀ n, n < L ∨ H < n → P n = 0 := fun n hn =>
    tendsto_nhds_unique (hCP1.tendsto hτ₁ n) (by simp only [hPks _ n hn]; exact tendsto_const_nhds)
  have hPcv : ∀ ρ, ConvergesAt P ρ := convergesAt_of_support hPs
  have hkP : ∀ k ρ, ConvergesAt (Pk k - P) ρ := fun k ρ =>
    convergesAt_of_support (A := L) (B := H)
      (fun n (hn : n < L ∨ H < n) => by simp [hPks k n hn, hPs n hn]) ρ
  have huc1 : ConvergesAt u τ₁ := hCu1.convergesAt hτ₁ hu1
  have huc2 : ConvergesAt u τ₂ := hCu2.convergesAt hτ₂ hu2
  have hδ : ∀ ρ, ConvergesAt (Pi.single 0 (1 : K)) ρ := convergesAt_single 0 1
  have hε0 : 0 < (1 - lam) / 2 := by linarith
  have hunit : ∀ ρ, 0 < ρ → UCauchy uk ρ → ConvergesAt u ρ → (∀ k, ConvergesAt (uk k) ρ) →
      (∀ k, gaussNorm (uk k - Pi.single 0 1) ρ ≤ lam) → gaussNorm (u - Pi.single 0 1) ρ < 1 := by
    intro ρ hρ hC hc hck hb
    obtain ⟨K₀, hK₀⟩ := hC.gaussNorm_sub_le hρ hε0
    have e : u - Pi.single 0 1 = (u - uk K₀) + (uk K₀ - Pi.single 0 1) := by abel
    rw [e]
    refine (gaussNorm_add_le hρ (hc.sub hρ (hck K₀)) ((hck K₀).sub hρ (hδ ρ))).trans_lt ?_
    exact max_lt ((hK₀ K₀ le_rfl).trans_lt (by linarith)) ((hb K₀).trans_lt hlam1)
  refine ⟨P, u, hPs, huc1, huc2, hunit τ₁ hτ₁ hCu1 huc1 hu1 (fun k => (inv k).2.2.2.2.2.1),
    hunit τ₂ hτ₂ hCu2 huc2 hu2 (fun k => (inv k).2.2.2.2.2.2.1), ?_⟩

  set D := f - cmul P u with hD
  have hDc : ConvergesAt D τ₁ := h₁.sub hτ₁ ((hPcv τ₁).cmul hτ₁ huc1)
  have hsmall : ∀ ε > 0, gaussNorm D τ₁ ≤ ε := by
    intro ε hε
    set C := gaussNorm P τ₁
    have hC0 : 0 ≤ C := gaussNorm_nonneg hτ₁
    obtain ⟨K1, hK1⟩ := hCP1.gaussNorm_sub_le hτ₁ hε
    obtain ⟨K2, hK2⟩ := hCu1.gaussNorm_sub_le hτ₁ (show 0 < ε / (C + 1) by positivity)
    obtain ⟨K3, hK3⟩ := eventually_atTop.1
      ((tendsto_pow_succ_mul (F := F₁) hlam0 hlam1).eventually (ge_mem_nhds hε))
    set k := max K1 (max K2 K3)
    have hk1 : gaussNorm (P - Pk k) τ₁ ≤ ε := hK1 k (le_max_left _ _)
    have hk2 : gaussNorm (u - uk k) τ₁ ≤ ε / (C + 1) := hK2 k (le_max_of_le_right (le_max_left _ _))
    have hk3 : gaussNorm (f - cmul (Pk k) (uk k)) τ₁ ≤ ε :=
      ((inv k).2.2.2.2.2.2.2.1).trans (hK3 k (le_max_of_le_right (le_max_right _ _)))
    have hukb : gaussNorm (uk k) τ₁ ≤ 1 := by
      have e : uk k = (uk k - Pi.single 0 1) + Pi.single 0 1 := by abel
      rw [e]
      refine (gaussNorm_add_le hτ₁ ((hu1 k).sub hτ₁ (hδ τ₁)) (hδ τ₁)).trans (max_le ?_ ?_)
      · exact ((inv k).2.2.2.2.2.1).trans hlam1.le
      · rw [gaussNorm_single_zero_one hτ₁]
    have hexp : D = (f - cmul (Pk k) (uk k)) + (cmul (Pk k - P) (uk k) + cmul P (uk k - u)) := by
      have e1 : cmul (Pk k) (uk k) = cmul P (uk k) + cmul (Pk k - P) (uk k) := by
        rw [← add_cmul hτ₁ (hPcv τ₁) (hkP k τ₁) (hu1 k)]; congr 1; abel
      have e2 : cmul P (uk k) = cmul P u + cmul P (uk k - u) := by
        rw [← cmul_add hτ₁ (hPcv τ₁) huc1 ((hu1 k).sub hτ₁ huc1)]; congr 1; abel
      rw [hD, e1, e2]; abel
    rw [hexp]
    have hc1 : ConvergesAt (cmul (Pk k - P) (uk k)) τ₁ :=
      (hkP k τ₁).cmul hτ₁ (hu1 k)
    have hc2 : ConvergesAt (cmul P (uk k - u)) τ₁ := (hPcv τ₁).cmul hτ₁ ((hu1 k).sub hτ₁ huc1)
    refine (gaussNorm_add_le hτ₁ (h₁.sub hτ₁ ((hPc k τ₁).cmul hτ₁ (hu1 k))) (hc1.add hτ₁ hc2)).trans
      (max_le hk3 ((gaussNorm_add_le hτ₁ hc1 hc2).trans (max_le ?_ ?_)))
    · refine (gaussNorm_cmul_le hτ₁ (hkP k τ₁) (hu1 k)).trans ?_
      rw [gaussNorm_sub_comm]
      calc gaussNorm (P - Pk k) τ₁ * gaussNorm (uk k) τ₁ ≤ ε * 1 :=
            mul_le_mul hk1 hukb (gaussNorm_nonneg hτ₁) hε.le
        _ = ε := mul_one ε
    · refine (gaussNorm_cmul_le hτ₁ (hPcv τ₁) ((hu1 k).sub hτ₁ huc1)).trans ?_
      rw [gaussNorm_sub_comm]
      calc C * gaussNorm (u - uk k) τ₁ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hk2 hC0
        _ ≤ ε := by rw [mul_div_assoc']; rw [div_le_iff₀ (by positivity)]; nlinarith
  have hD0 : gaussNorm D τ₁ = 0 := by
    refine le_antisymm ?_ (gaussNorm_nonneg hτ₁)
    by_contra hpos
    push_neg at hpos
    have := hsmall (gaussNorm D τ₁ / 2) (by positivity)
    linarith
  have := (gaussNorm_eq_zero_iff hτ₁ hDc).1 hD0
  exact (sub_eq_zero.1 this)

end PrepLimit

theorem gaussNorm_sub_trunc_lt {ρ : ℝ} {f : ℤ → K} {L H : ℤ} (hρ : 0 < ρ) (h : ConvergesAt f ρ)
    (hf : f ≠ 0) (hout : ∀ n, n ∉ Set.Icc L H → ‖f n‖ * ρ ^ n < gaussNorm f ρ) :
    gaussNorm (f - trunc f (Set.Icc L H)) ρ < gaussNorm f ρ := by
  have hF := gaussNorm_pos hρ h hf
  have hc : ConvergesAt (f - trunc f (Set.Icc L H)) ρ := h.sub hρ (h.trunc hρ _)
  by_cases h0 : f - trunc f (Set.Icc L H) = 0
  · rw [h0, gaussNorm_zero]; exact hF
  obtain ⟨n, hn⟩ := hc.exists_eq_gaussNorm hρ h0
  rw [← hn]
  by_cases hm : n ∈ Set.Icc L H
  · simp [trunc, Set.indicator_of_mem hm] ; exact hF
  · simp only [Pi.sub_apply, trunc, Set.indicator_of_notMem hm, sub_zero]; exact hout n hm

theorem weierstrass_preparation {τ₁ τ₂ : ℝ} {f : ℤ → K} (hτ₁ : 0 < τ₁) (hτ : τ₁ ≤ τ₂)
    (h₁ : ConvergesAt f τ₁) (h₂ : ConvergesAt f τ₂) (hf : f ≠ 0) :
    ∃ P u : ℤ → K, (∀ n, n < lowIndex f τ₁ ∨ highIndex f τ₂ < n → P n = 0) ∧
      ConvergesAt u τ₁ ∧ ConvergesAt u τ₂ ∧ gaussNorm (u - Pi.single 0 1) τ₁ < 1 ∧
      gaussNorm (u - Pi.single 0 1) τ₂ < 1 ∧ f = cmul P u := by
  have hτ₂ : 0 < τ₂ := hτ₁.trans_le hτ
  set L := lowIndex f τ₁
  set H := highIndex f τ₂
  have hLH : L ≤ H :=
    (lowIndex_le_highIndex hτ₁ h₁ hf).trans (highIndex_mono hτ₁ hτ h₁ h₂ hf)
  have hF₁ := gaussNorm_pos hτ₁ h₁ hf
  have hF₂ := gaussNorm_pos hτ₂ h₂ hf
  have hlt₁ : gaussNorm (f - trunc f (Set.Icc L H)) τ₁ < gaussNorm f τ₁ :=
    gaussNorm_sub_trunc_lt hτ₁ h₁ hf fun n hn => by
      simp only [Set.mem_Icc, not_and_or, not_le] at hn
      rcases hn with hn | hn
      · exact weight_lt_of_lt_lowIndex hτ₁ h₁ hf hn
      · exact weight_lt_of_highIndex_lt hτ₁ h₁ hf
          (lt_of_le_of_lt (highIndex_mono hτ₁ hτ h₁ h₂ hf) hn)
  have hlt₂ : gaussNorm (f - trunc f (Set.Icc L H)) τ₂ < gaussNorm f τ₂ :=
    gaussNorm_sub_trunc_lt hτ₂ h₂ hf fun n hn => by
      simp only [Set.mem_Icc, not_and_or, not_le] at hn
      rcases hn with hn | hn
      · exact weight_lt_of_lt_lowIndex hτ₂ h₂ hf
          (lt_of_lt_of_le hn (lowIndex_mono hτ₁ hτ h₁ h₂ hf))
      · exact weight_lt_of_highIndex_lt hτ₂ h₂ hf hn
  set lam := max (gaussNorm (f - trunc f (Set.Icc L H)) τ₁ / gaussNorm f τ₁)
    (gaussNorm (f - trunc f (Set.Icc L H)) τ₂ / gaussNorm f τ₂)
  have hlam0 : 0 ≤ lam := le_max_of_le_left (div_nonneg (gaussNorm_nonneg hτ₁) hF₁.le)
  have hlam1 : lam < 1 := max_lt ((div_lt_one hF₁).2 hlt₁) ((div_lt_one hF₂).2 hlt₂)
  exact prep_limit hτ₁ hτ hLH h₁ h₂ hF₁ hF₂ (lowIndex_mem hτ₁ h₁ hf) (h₁.le_gaussNorm)
    (highIndex_mem hτ₂ h₂ hf) (h₂.le_gaussNorm) hlam0 hlam1
    ((div_le_iff₀ hF₁).1 (le_max_left _ _)) ((div_le_iff₀ hF₂).1 (le_max_right _ _))

end Laurent

end GroundTheory.PAdicHodge
