import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRealThetaParameterPairThetaPartnerSignedParameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.ParPairArrows

open GlobalTheory.SignedHC Finset

section
variable (G : GridData)

theorem a_le_of_le {l l' : ℕ} (h : l ≤ l') : G.a l' ≤ G.a l := by
  have e := G.a_sub_a l l'
  have h' : (l : ℚ) ≤ l' := by exact_mod_cast h
  have : (0 : ℚ) ≤ ((l' : ℚ) - l) * G.ga := mul_nonneg (by linarith) (by positivity)
  linarith

theorem a_add_le {l l' : ℕ} (h : l + 1 ≤ l') : G.a l' + G.ga ≤ G.a l := by
  have e := G.a_sub_a l l'
  have h' : (l : ℚ) + 1 ≤ l' := by exact_mod_cast h
  have : (0 : ℚ) ≤ ((l' : ℚ) - l - 1) * G.ga := mul_nonneg (by linarith) (by positivity)
  nlinarith

theorem low_bound (hN : G.NearMid) (hs : 1 ≤ G.s) {j : ℕ} (hj : j ≤ G.m) {x : ℚ}
    (hx : x ∈ G.cloudHalf ∨ ∃ l, G.m - j + 1 ≤ l ∧ l ≤ G.m ∧ x ∈ G.blockC' l) :
    x ≤ G.a (G.m - j) - G.ga / 2 + G.s / 2 := by
  have hg : (0 : ℚ) ≤ G.ga := by positivity
  have hs0 : (0 : ℚ) ≤ G.s := by positivity
  rcases hx with hx | ⟨l, h1, h2, hx⟩
  · obtain ⟨i, hi2, hik, rfl⟩ := GridData.mem_cloudHalf.1 hx
    have hv : G.v i ≤ G.v 2 := by
      rcases eq_or_lt_of_le hi2 with h | h
      · rw [h]
      · exact (G.v_anti 2 i le_rfl h hik).le
    have hvq : (G.v i : ℚ) ≤ G.v 2 := by exact_mod_cast hv
    have ha := G.a_m
    have hmono := a_le_of_le G (Nat.sub_le G.m j)
    simp only [GridData.vHalf]
    linarith
  · have hb := abs_sub_le_of_mem_block (c := (G.cen l : ℚ)) (t := G.s - 1) hx
    have hcast : ((G.s - 1 : ℕ) : ℚ) = G.s - 1 := by rw [Nat.cast_sub hs]; simp
    rw [hcast] at hb
    have hn := hN l (mem_Icc.2 ⟨by omega, h2⟩)
    rw [G.mid_eq (by omega)] at hn
    have hmono := a_add_le G (show G.m - j + 1 ≤ l from h1)
    rw [abs_le] at hb hn
    linarith [hb.2, hn.2]

theorem cen_bounds (hN : G.NearMid) {i : ℕ} (hi : i < G.m) :
    G.a (G.m - i) + G.ga / 2 - 1 ≤ (G.cen (G.m - i) : ℚ) ∧ (G.cen (G.m - i) : ℚ) ≤ G.a (G.m - i) + G.ga / 2 + 1 := by
  have h := hN (G.m - i) (mem_Icc.2 ⟨by omega, by omega⟩)
  rw [G.mid_eq (by omega), abs_le] at h
  constructor <;> linarith [h.1, h.2]

end

theorem sign_step {m i l : ℕ} (h : l < m - i) :
    (!decide (m - i ≤ l ∨ Even (m - i - l))) = decide (m - (i + 1) ≤ l ∨ Even (m - (i + 1) - l)) := by
  obtain ⟨d, hd⟩ : ∃ d, m - i - l = d + 1 := ⟨m - i - l - 1, by omega⟩
  have h2 : m - (i + 1) - l = d := by omega
  have e1 : ¬ (m - i ≤ l) := by omega
  have e2 : (m - (i + 1) ≤ l) ↔ d = 0 := by omega
  rw [hd, h2]
  by_cases hd0 : d = 0
  · subst hd0; simp [e1]
  · simp only [e1, e2, hd0, Nat.even_add_one, false_or]
    rcases Nat.even_or_odd d with he | he
    · have : ¬ Odd d := Nat.not_odd_iff_even.2 he
      simp [he]
    · have : ¬ Even d := Nat.not_even_iff_odd.2 he
      simp [this]

end GlobalTheory.ParPairArrows

namespace GlobalTheory.ParPairArrows

open GlobalTheory.SignedHC Finset

section
variable (G : GridData)

theorem gap_parPi (hN : G.NearMid) (hs : 1 ≤ G.s) (hγ : (G.s : ℚ) ≤ G.ga) {j : ℕ} (hj : j ≤ G.m) :
    ∀ x ∈ G.parPi j, ∀ y ∈ G.parPi j, x.2 ≠ y.2 → (G.ga : ℚ) ≤ |x.1 - y.1| := by
  have key : ∀ x ∈ G.parPi j, x.2 = false → ∀ y ∈ G.parPi j, y.2 = true → (G.ga : ℚ) ≤ |x.1 - y.1| := by
    intro x hx hxf y hy hyt
    rcases GridData.mem_parPi.1 hx with ⟨l, hl, rfl⟩ | ⟨_, h⟩ | ⟨_, _, _, _, h⟩
    · simp only [decide_eq_false_iff_not, not_or] at hxf
      have hax := a_add_le G (show l + 1 ≤ G.m - j by omega)
      rcases GridData.mem_parPi.1 hy with ⟨l', hl', rfl⟩ | ⟨hq, _⟩ | ⟨l', h1, h2, hq, _⟩
      · have hne : l ≠ l' := by
          rintro rfl
          simp only [decide_eq_true_eq] at hyt
          exact hxf.2 (hyt.resolve_left hxf.1)
        rcases Nat.lt_or_gt_of_ne hne with h | h
        · have := a_add_le G (show l + 1 ≤ l' by omega)
          rw [le_abs]; left; simp only; linarith
        · have := a_add_le G (show l' + 1 ≤ l by omega)
          rw [le_abs]; right; simp only; linarith
      · have := low_bound G hN hs hj (Or.inl hq)
        rw [le_abs]; left; simp only; linarith
      · have := low_bound G hN hs hj (Or.inr ⟨l', h1, h2, hq⟩)
        rw [le_abs]; left; simp only; linarith
    · rw [hxf] at h; exact absurd h (by decide)
    · rw [hxf] at h; exact absurd h (by decide)
  intro x hx y hy hne
  cases hx2 : x.2 <;> cases hy2 : y.2
  · exact absurd (hx2.trans hy2.symm) hne
  · exact key x hx hx2 y hy hy2
  · rw [abs_sub_comm]; exact key y hy hy2 x hx hx2
  · exact absurd (hx2.trans hy2.symm) hne

theorem far_parPi (hN : G.NearMid) (hs : 1 ≤ G.s) (hγ : (G.s : ℚ) + 4 ≤ G.ga) {i : ℕ} (hi : i < G.m) :
    FarFrom (G.cen (G.m - i) : ℚ) (((G.s : ℚ) + 2) / 2) (G.parPi i) := by
  intro x hx
  obtain ⟨b, hb⟩ := mem_entries.1 hx
  obtain ⟨hc1, hc2⟩ := cen_bounds G hN hi
  rcases GridData.mem_parPi.1 hb with ⟨l, hl, he⟩ | ⟨hq, _⟩ | ⟨l', h1, h2, hq, _⟩
  · have hx' : x = G.a l := congrArg Prod.fst he
    subst hx'
    by_cases hlt : l < G.m - i
    · have := a_add_le G (show l + 1 ≤ G.m - i by omega)
      rw [le_abs]; left; linarith
    · have := a_le_of_le G (show G.m - i ≤ l by omega)
      rw [le_abs]; right; linarith
  · have := low_bound G hN hs hi.le (Or.inl hq)
    rw [le_abs]; right; linarith
  · have := low_bound G hN hs hi.le (Or.inr ⟨l', h1, h2, hq⟩)
    rw [le_abs]; right; linarith

theorem partner_parPi (hN : G.NearMid) (hs : 1 ≤ G.s) (hγ : (G.s : ℚ) + 4 ≤ G.ga) {i : ℕ} (hi : i < G.m) :
    partner (G.s - 1) false (G.cen (G.m - i) : ℚ) (G.cen (G.m - i) : ℚ) (G.parPi i) = flip (G.parPi (i + 1)) := by
  obtain ⟨hc1, hc2⟩ := cen_bounds G hN hi
  have hlow : ∀ x, (x ∈ G.cloudHalf ∨ ∃ l, G.m - i + 1 ≤ l ∧ l ≤ G.m ∧ x ∈ G.blockC' l) →
      x < (G.cen (G.m - i) : ℚ) := fun x hx => by
    have := low_bound G hN hs hi.le hx; linarith
  have habove : ∀ l, l < G.m - i → (G.cen (G.m - i) : ℚ) < G.a l := fun l hl => by
    have := a_add_le G (show l + 1 ≤ G.m - i by omega); linarith
  have hbelow : ∀ l, G.m - i ≤ l → G.a l < (G.cen (G.m - i) : ℚ) := fun l hl => by
    have := a_le_of_le G hl; linarith
  ext ⟨q, b⟩
  simp only [partner, mem_union, mem_image, mem_flip, sub_add_cancel, Prod.mk.injEq]
  constructor
  · rintro (⟨⟨y, yb⟩, hy, rfl, rfl⟩ | ⟨z, hz, rfl, rfl⟩)
    · rw [GridData.mem_parPi]
      rcases GridData.mem_parPi.1 hy with ⟨l, hl, he⟩ | ⟨hq, hyb⟩ | ⟨l, h1, h2, hq, hyb⟩
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        left
        refine ⟨l, hl, ?_⟩
        by_cases hlt : l < G.m - i
        · rw [if_neg (not_lt.2 (habove l hlt).le)]
          simp only [Prod.mk.injEq, true_and]
          exact sign_step hlt
        · rw [if_pos (hbelow l (by omega))]
          simp only [Prod.mk.injEq, true_and, Bool.not_not]
          have h1 : G.m - i ≤ l := by omega
          have h2 : G.m - (i + 1) ≤ l := by omega
          simp [h1, h2]
      · simp only at hq hyb
        subst hyb
        rw [if_pos (hlow y (Or.inl hq))]
        exact Or.inr (Or.inl ⟨hq, rfl⟩)
      · simp only at hq hyb
        subst hyb
        rw [if_pos (hlow y (Or.inr ⟨l, h1, h2, hq⟩))]
        exact Or.inr (Or.inr ⟨l, by omega, h2, hq, rfl⟩)
    · exact GridData.mem_parPi.2 (Or.inr (Or.inr ⟨G.m - i, by omega, by omega, hz, rfl⟩))
  · intro h
    rcases GridData.mem_parPi.1 h with ⟨l, hl, he⟩ | ⟨hq, hb⟩ | ⟨l, h1, h2, hq, hb⟩
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, hb⟩ := he
      left
      by_cases hlt : l < G.m - i
      · refine ⟨(G.a l, decide (G.m - i ≤ l ∨ Even (G.m - i - l))),
          GridData.mem_parPi.2 (Or.inl ⟨l, hl, rfl⟩), rfl, ?_⟩
        rw [if_neg (not_lt.2 (habove l hlt).le)]
        rw [← sign_step hlt] at hb
        exact (Bool.not_inj hb).symm
      · have h1 : G.m - i ≤ l := by omega
        have h2 : G.m - (i + 1) ≤ l := by omega
        refine ⟨(G.a l, true), GridData.mem_parPi.2 (Or.inl ⟨l, hl, by simp [h1]⟩), rfl, ?_⟩
        rw [if_pos (hbelow l h1)]
        simp [h2] at hb
        simp [hb]
    · simp only at hq hb
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hb
      subst hb
      exact Or.inl ⟨(q, true), GridData.mem_parPi.2 (Or.inr (Or.inl ⟨hq, rfl⟩)), rfl,
        by rw [if_pos (hlow q (Or.inl hq))]; rfl⟩
    · simp only at hq hb
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hb
      subst hb
      by_cases hl : l = G.m - i
      · subst hl
        exact Or.inr ⟨q, hq, rfl, rfl⟩
      · exact Or.inl ⟨(q, true), GridData.mem_parPi.2 (Or.inr (Or.inr ⟨l, by omega, h2, hq, rfl⟩)), rfl,
          by rw [if_pos (hlow q (Or.inr ⟨l, by omega, h2, hq⟩))]; rfl⟩

end

end GlobalTheory.ParPairArrows

namespace GlobalTheory.ParPairArrows

open GlobalTheory.SignedHC Finset

section
variable (G : GridData)

theorem inCoset_parPi {q : ℕ} (hq : G.s = 2 * q + 1) (c : ℤ) (i : ℕ) :
    InCoset ((c : ℚ) + (((G.s - 1 : ℕ) : ℚ) + 1) / 2) (entries (G.parPi i)) := by
  have hcast : ((G.s - 1 : ℕ) : ℚ) = 2 * q := by rw [hq, Nat.add_sub_cancel]; push_cast; ring
  intro x hx
  obtain ⟨b, hb⟩ := mem_entries.1 hx
  rw [hcast]
  rcases GridData.mem_parPi.1 hb with ⟨l, hl, he⟩ | ⟨hq', _⟩ | ⟨l', h1, h2, hq', _⟩
  · have hx' : x = G.a l := congrArg Prod.fst he
    subst hx'
    refine ⟨G.v 2 + ((G.m : ℤ) + 1 - l) * G.ga - c - q, ?_⟩
    simp only [GridData.a]; push_cast; ring
  · obtain ⟨j, _, _, rfl⟩ := GridData.mem_cloudHalf.1 hq'
    refine ⟨G.v j - 1 - c - q, ?_⟩
    simp only [GridData.vHalf]; push_cast; ring
  · obtain ⟨a, _, rfl⟩ := mem_block.1 (show x ∈ TPar.block (G.cen l' : ℚ) (G.s - 1) from hq')
    rw [hcast]
    refine ⟨G.cen l' - a - 1 - c, ?_⟩
    push_cast; ring

theorem card_parPi (i : ℕ) : (G.parPi i).card ≤ (G.m + 1) + (G.k - 1) + i * (G.s - 1) := by
  unfold GridData.parPi GridData.cloudHalf plus
  refine (card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · exact card_image_le.trans (by simp)
  · exact card_image_le.trans (card_image_le.trans (by simp))
  · refine card_image_le.trans (card_biUnion_le.trans ?_)
    simp only [GridData.blockC', card_block, sum_const, smul_eq_mul, Nat.card_Icc]
    apply Nat.mul_le_mul_right
    omega

end

theorem parPi_pairPar : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (i : ℕ) (τ : D.what₂.Tau), i < D.R.m →
    PairPar (dualPar (GlobalTheory.SignedHC.flip (parP D (i + 1) τ))) (dualPar (parP D i τ)) (cen D τ (D.R.m - i))
      (cen D τ (D.R.m - i)) ∧
    PairPar (dualPar (parP D i τ)) (dualPar (GlobalTheory.SignedHC.flip (parP D (i + 1) τ))) (cen D τ (D.R.m - i))
      (cen D τ (D.R.m - i)) := by
  intro D hS i τ hi
  have hN : (grid D τ).NearMid := grid_nearMid D τ
  have hγ := (isLeast_gap D).1.2.1
  have hr := hS.1
  have hsl : sLen D = D.R.r + 6 := rfl
  have hrk : D.R.r = D.R.k + D.R.m - 1 := rfl
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have hkm := D.R.m_add_three_le_k
  have hs1 : 1 ≤ (grid D τ).s := show 1 ≤ sLen D by omega
  have hq : (grid D τ).s = 2 * (a + b + 2) + 1 := show sLen D = _ by rw [hsl, hrk]; omega
  have hmN : D.R.m ≤ D.R.m * (D.R.t + sLen D + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hN1 : 1800 < bigN D := by unfold bigN; omega
  have hN3 : 1 ≤ bigN D ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hγq : ((grid D τ).s : ℚ) + 4 ≤ (grid D τ).ga := by
    show (sLen D : ℚ) + 4 ≤ (gap D : ℚ)
    exact_mod_cast (by omega : sLen D + 4 ≤ gap D)
  have hγ2 : 2 * (bigN D : ℚ) ^ 3 < (grid D τ).ga := by
    show 2 * (bigN D : ℚ) ^ 3 < (gap D : ℚ)
    exact_mod_cast (by omega : 2 * bigN D ^ 3 < gap D)
  have hsγ : ((grid D τ).s : ℚ) ≤ (grid D τ).ga := by linarith
  have hs0 : (0 : ℚ) ≤ (grid D τ).s := by positivity
  have hcastT : ((sLen D - 1 : ℕ) : ℚ) = (sLen D : ℚ) - 1 := by rw [Nat.cast_sub (show 1 ≤ sLen D by omega)]; simp
  have hsq : ((grid D τ).s : ℚ) = (sLen D : ℚ) := rfl
  have hpart : partner (sLen D - 1) false (cen D τ (D.R.m - i) : ℚ) (cen D τ (D.R.m - i) : ℚ) (parP D i τ) =
      flip (parP D (i + 1) τ) := partner_parPi (grid D τ) hN hs1 hγq hi
  have hgap : ∀ j, j ≤ D.R.m → GapOver (parP D j τ) (2 * (bigN D : ℚ) ^ 3) := fun j hj x hx y hy hne =>
    lt_of_lt_of_le hγ2 (gap_parPi (grid D τ) hN hs1 hsγ hj x hx y hy hne)
  have hfar : FarFrom (cen D τ (D.R.m - i) : ℚ) (((sLen D : ℚ) + 2) / 2) (parP D i τ) :=
    far_parPi (grid D τ) hN hs1 hγq hi
  have hth : ThetaPar (sLen D - 1) (parP D i τ) (flip (parP D (i + 1) τ)) (cen D τ (D.R.m - i))
      (cen D τ (D.R.m - i)) := by
    have h := GlobalTheory.T.isRealThetaParameterPair_thetaPartnerSignedParameter (sLen D - 1) false (cen D τ (D.R.m - i) : ℚ) (cen D τ (D.R.m - i) : ℚ) (parP D i τ) (bigN D)
      (by omega) ⟨_, GridData.mem_parPi.2 (Or.inl ⟨0, Nat.zero_le _, rfl⟩)⟩
      (by
        intro x hx y hy e
        by_contra hne
        have := gap_parPi (grid D τ) hN hs1 hsγ hi.le x hx y hy hne
        rw [e, sub_self, abs_zero] at this
        linarith)
      (inCoset_parPi (grid D τ) hq (cen D τ (D.R.m - i)) i)
      (fun x hx => by
        have := hfar x hx
        rw [hcastT]; linarith)
      (by
        have hc := card_parPi (grid D τ) i
        have h1 : (i + 1) * (sLen D - 1) ≤ D.R.m * (sLen D - 1) := Nat.mul_le_mul_right _ hi
        have h2 : (i + 1) * (sLen D - 1) = i * (sLen D - 1) + (sLen D - 1) := Nat.succ_mul _ _
        have h3 : D.R.m * (sLen D - 1) + D.R.m ≤ D.R.m * (D.R.t + sLen D + 1) := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
        show ((grid D τ).parPi i).card + (sLen D - 1) ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
        change _ ≤ (D.R.m + 1) + (D.R.k - 1) + i * (sLen D - 1) at hc
        omega)
      (by omega) (hgap i hi.le)
      (by
        rw [hpart]
        intro x hx y hy hne
        rw [mem_flip] at hx hy
        exact hgap (i + 1) hi (x.1, !x.2) hx (y.1, !y.2) hy fun h => hne (Bool.not_inj h))
    rwa [hpart] at h
  refine ⟨⟨sLen D - 1, flip (parP D (i + 1) τ), parP D i τ, rfl, rfl, Or.inr hth⟩,
    ⟨sLen D - 1, parP D i τ, flip (parP D (i + 1) τ), rfl, rfl, Or.inl ⟨hth, fun x hx => ?_⟩⟩⟩
  have := hfar x hx
  rw [hcastT]; linarith

end GlobalTheory.ParPairArrows
