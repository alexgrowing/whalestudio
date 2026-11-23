import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightGapsBlockAndBar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftGaps

theorem antitone_of_step {N : ℕ} {f : Fin N → ℤ} (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b ≤ f a) : Antitone f := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  simp only [Fin.mk_le_mk] at hab
  induction b with
  | zero =>
    obtain rfl : a = 0 := by omega
    exact le_rfl
  | succ n ih =>
    rcases Nat.lt_or_ge a (n + 1) with h' | h'
    · exact (h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl).trans (ih (by omega) (by omega))
    · obtain rfl : a = n + 1 := by omega
      exact le_rfl

theorem isQuot_u₁ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (P : WtPar Dw) (kc : ℕ) (hk : P.a + 1 = kc) : IsQuot Dw kc P.T P.c₀ P.u P.u₁ := by
  intro τ
  refine ⟨fun a (ha : (a : ℕ) + 1 = kc) => (P.anchored τ (by omega)).1, fun a b hb => ?_⟩
  have hb' : (a : ℕ) + 1 < Dw.p + Dw.q := hb ▸ b.2
  show P.u₁ τ a - P.u₁ τ b = (P.u τ a - P.u τ b + if (b : ℕ) = Dw.p then -P.c₀ - (2 * ((Dw.p + Dw.q : ℕ) : ℤ) - 2) else 2) /
    ((P.T : ℤ) + CompHt.dimFlag Dw + 1)
  rw [← CompHS.gap_eq (P.u₁ τ) hb, P.gap_u₁ τ hb', P.gap_uMinus_sub_kap τ hb', CompHS.gap_eq (P.u τ) hb, hb,
    WtPar.T₁, dimFlag_eq]

section Pt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem nCol_le (PP A M : ℝ) (hw : WtNum p i PP) (hh : HostNum D L PP A M) :
    GlobalTheory.RefSum.nCol (dat p i) ≤ 2 * D.R.r * (D.R.f * D.R.r) + 8 * (D.R.f * D.R.r) + 8 := by
  obtain ⟨-, -, s3⟩ := hw.sig
  have hcard : Fintype.card (Lt1 (dat p i)) = D.R.f * D.R.r := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [GlobalTheory.RefSum.sum_mult, hh.deg, s3]
    simp
  have hmult : ∀ τ, (dat p i).mult τ ≤ D.R.r := fun τ => by
    rw [← s3]; unfold Datum.mult; split_ifs <;> omega
  have hsum : ∑ f : Lt1 (dat p i), 2 * GlobalTheory.FactorDepth.rk f ≤ Fintype.card (Lt1 (dat p i)) * (2 * D.R.r) := by
    rw [← smul_eq_mul, ← Finset.card_univ]
    refine Finset.sum_le_card_nsmul _ _ _ fun f _ => ?_
    have := GlobalTheory.FactorDepth.rk_le f
    have := hmult f.1
    omega
  rw [hcard] at hsum
  unfold GlobalTheory.RefSum.nCol
  have h8 : 8 * ((∑ f : Lt1 (dat p i), 2 * GlobalTheory.FactorDepth.rk f) / 8) ≤ ∑ f : Lt1 (dat p i), 2 * GlobalTheory.FactorDepth.rk f :=
    Nat.mul_div_le _ _
  rw [hcard]
  have : D.R.f * D.R.r * (2 * D.R.r) = 2 * D.R.r * (D.R.f * D.R.r) := by ring
  omega

theorem cols_le_len (PP A M : ℝ) (hw : WtNum p i PP) (hh : HostNum D L PP A M) :
    (GlobalTheory.RefSum.nCol (dat p i) + 1) * (CompHt.dimFlag (dat p i) + 3) ≤ lenT p i PP := by
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hr6 : 6 ≤ D.R.r := by omega
  have hf8 := hh.f8
  have hn := nCol_le p i PP A M hw hh
  have hZ : (40 : ℝ) ≤ zBase L := by
    unfold zBase
    have a1 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf8
    have a2 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr6
    have a3 : (48 : ℝ) ≤ D.R.f * D.R.r := by nlinarith
    have a4 : (10 : ℝ) ≤ L.sc.L := hh.big.2.1
    nlinarith
  have hPP : (40 : ℝ) ≤ PP := hZ.trans ((le_self_pow₀ (by linarith) (by norm_num)).trans hh.ppLow)
  have hD : ((CompHt.dimFlag (dat p i) : ℕ) : ℝ) = (D.R.f : ℝ) * ((D.R.r : ℝ) * ((D.R.r : ℝ) - 1) / 2) := by
    rw [hw.dim]; push_cast [Nat.cast_choose_two]; ring
  set Dd : ℝ := ((CompHt.dimFlag (dat p i) : ℕ) : ℝ) with hDd
  have F8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hf8
  have R6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr6
  have FR : (48 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
  have hDd1 : (1 : ℝ) ≤ Dd := by rw [hD]; nlinarith
  have hn' : (GlobalTheory.RefSum.nCol (dat p i) : ℝ) + 1 ≤ 17 * Dd := by
    have : (GlobalTheory.RefSum.nCol (dat p i) : ℝ) ≤ 2 * D.R.r * (D.R.f * D.R.r) + 8 * (D.R.f * D.R.r) + 8 := by
      exact_mod_cast hn
    rw [hD]
    have h13 : (45 : ℝ) ≤ 13 * D.R.r - 33 := by linarith
    have : (48 : ℝ) * 45 ≤ ((D.R.f : ℝ) * D.R.r) * (13 * D.R.r - 33) := mul_le_mul FR h13 (by norm_num) (by linarith)
    nlinarith
  have hm0 : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
  have hkm : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hT : 1600 * Dd ^ 2 ≤ (lenT p i PP : ℝ) := by
    have h1 : 1600 * Dd ^ 2 ≤ PP ^ 2 * Dd ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
      rw [le_div_iff₀ hm0]
      have c5 : (1600 : ℝ) ≤ PP ^ 2 := by nlinarith
      have c6 : (0 : ℝ) ≤ Dd ^ 2 := by positivity
      calc 1600 * Dd ^ 2 * D.R.m ≤ PP ^ 2 * Dd ^ 2 * D.R.m :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right c5 c6) hm0.le
        _ ≤ PP ^ 2 * Dd ^ 2 * D.R.k := mul_le_mul_of_nonneg_left hkm (by positivity)
    exact h1.trans (Nat.le_ceil _)
  have hmain : ((GlobalTheory.RefSum.nCol (dat p i) : ℝ) + 1) * (Dd + 3) ≤ (lenT p i PP : ℝ) := by
    have e1 : Dd + 3 ≤ 4 * Dd := by linarith
    have : ((GlobalTheory.RefSum.nCol (dat p i) : ℝ) + 1) * (Dd + 3) ≤ (17 * Dd) * (4 * Dd) :=
      mul_le_mul hn' e1 (by linarith) (by linarith)
    nlinarith
  rw [hDd] at hmain
  exact_mod_cast hmain

theorem gapsAt (PP A M : ℝ) (hi : (i : ℕ) + 1 < D.R.m) (hw : WtNum p i PP) (hh : HostNum D L PP A M) :
    1 ≤ (dat p i).p ∧ ∀ la ∈ ({(⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁,
      (⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))),
      (∀ τ, Antitone (la τ)) ∧ ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = (dat p i).p →
        (b : ℕ) = (dat p i).p → (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 ≤ la τ a - la τ b := by
  obtain ⟨s1, s2, s3⟩ := hw.sig
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have ep : (dat p i).p = D.R.k + i := by rw [s1]; unfold Ranks.sigW; omega
  have eq : (dat p i).q = D.R.m - ((i : ℕ) + 1) := by rw [s2]; rfl
  have hcl := cols_le_len p i PP A M hw hh
  set P : WtPar (dat p i) := ⟨uW p i, cZero D ((i : ℕ) + 1), D.R.k - 2, lenT p i PP⟩ with hP
  have hPa : P.a + 1 = D.R.k - 1 := by show D.R.k - 2 + 1 = D.R.k - 1; omega
  have hquo : Quo p i PP P.u₁ := isQuot_u₁ (dat p i) P (D.R.k - 1) hPa
  obtain ⟨h0, S, eta, -, -, -, hT2, -, hH⟩ := hw.hyp hi
  have hW := hH P.u₁
  have hdiv := (quo_iff p i PP h0 S eta P.u₁).1 hquo
  have G := GlobalTheory.MeanTop.divided_gaps _ _ _ hW hdiv
  have hT1 := hW.h1
  simp only [wtsAt] at G hT1

  have gin : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → 0 ≤ P.u₁ τ a - P.u₁ τ b := by
    intro τ a b hb
    obtain ⟨g1, g2, -⟩ := G τ a b hb
    by_cases hbp : (b : ℕ) = (dat p i).p
    · have g := (g2 hbp).1
      have hT0 : (0 : ℤ) < 2 * (lenT p i PP : ℤ) := by omega
      by_contra hc
      push_neg at hc
      have := mul_neg_of_pos_of_neg hT0 hc
      nlinarith
    · have g := g1 hbp
      have : (0 : ℤ) ≤ (lenT p i PP : ℤ) + CompHt.dimFlag (dat p i) + 2 + 2 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by
        positivity
      omega
  have gbar : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 → (b : ℕ) = (dat p i).p →
      (lenT p i PP : ℤ) ≤ P.u₁ τ a - P.u₁ τ b := by
    intro τ a b hb hbp
    obtain ⟨-, g2, -⟩ := G τ a b hb
    have g := (g2 hbp).2
    have hT0 : (0 : ℤ) < 4 * (lenT p i PP : ℤ) := by omega
    have hle : (lenT p i PP : ℤ) ≤ P.u₁ τ a - P.u₁ τ b - 3 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by
      by_contra hc
      push_neg at hc
      have := mul_lt_mul_of_pos_left hc hT0
      nlinarith
    have : (0 : ℤ) ≤ (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by positivity
    linarith

  have gub : ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 →
      P.ub τ a - P.ub τ b = (P.u₁ τ a - P.u₁ τ b) / ((dimFlag (dat p i) : ℤ) + 3) := by
    intro τ a b hb
    have hb' : (a : ℕ) + 1 < (dat p i).p + (dat p i).q := hb ▸ b.2
    rw [← CompHS.gap_eq (P.ub τ) hb, P.gap_ub τ hb', CompHS.gap_eq (P.u₁ τ) hb]
  have hcl' : ((GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1) * ((dimFlag (dat p i) : ℤ) + 3) ≤ (lenT p i PP : ℤ) := by
    rw [← dimFlag_eq]; exact_mod_cast hcl
  have hD0 : (0 : ℤ) < (dimFlag (dat p i) : ℤ) + 3 := by positivity
  have hD1 : (1 : ℤ) ≤ (dimFlag (dat p i) : ℤ) + 3 := by omega
  have hnT : (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 ≤ (lenT p i PP : ℤ) := by
    have : (0 : ℤ) ≤ (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 := by positivity
    nlinarith
  refine ⟨by omega, fun la hla => ?_⟩
  rcases hla with rfl | hla
  · refine ⟨fun τ => antitone_of_step fun a b hb => by have := gin τ a b hb; omega, fun τ a b ha hb => ?_⟩
    exact hnT.trans (gbar τ a b (by omega) hb)
  · rw [Set.mem_singleton_iff] at hla
    subst hla
    refine ⟨fun τ => antitone_of_step fun a b hb => ?_, fun τ a b ha hb => ?_⟩
    · have e := gub τ a b hb
      have := Int.ediv_nonneg (gin τ a b hb) hD0.le
      omega
    · rw [gub τ a b (by omega)]
      exact Int.le_ediv_of_mul_le hD0 (hcl'.trans (gbar τ a b (by omega) hb))

end Pt

theorem lift_gaps : Size → Covers fun Fm x _ ι p i Y PP _ => 1 ≤ (dat p i).p ∧ ∀ la ∈ ({(⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁, (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).ub} : Set (AllWt.Weight (dat p i))), (∀ τ, Antitone (la τ)) ∧ ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (a : ℕ) + 1 = (dat p i).p → (b : ℕ) = (dat p i).p → (GlobalTheory.RefSum.nCol (dat p i) : ℤ) + 1 ≤ la τ a - la τ b := by
  intro _
  have hw : WtN := WtShape.wtN
  have hh : HostN 1 := Sizes.hostN 1
  unfold WtN Lifts at hw
  unfold HostN Lifts at hh
  unfold Covers Lifts
  refine Formalism.MainNotions.Closed.imp (Formalism.MainNotions.Closed.and hw hh) ?_
  intro eps Fm CH _ h
  obtain ⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩ := h
  refine ⟨0, le_rfl, max x1 x2, fun x hx hle ι p hp i hi Y _ => ?_⟩
  exact gapsAt p i _ _ _ hi (h1 x hx ((le_max_left _ _).trans hle) ι p hp i)
    (h2 x hx ((le_max_right _ _).trans hle) ι p hp i)

end GlobalTheory.LiftGaps
