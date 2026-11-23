import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.BlockYZeroLeOfBound
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.YcondCongr
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TCNumDef

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem jE_mono {s : ℕ} (S : SegData s) {f g : Fin S.t → ℕ} (h : ∀ l, f l ≤ g l) (i : ℕ) : jE S f i ≤ jE S g i := by
  unfold jE
  split_ifs
  · exact h _
  · exact le_rfl

theorem jE_add {s : ℕ} (S : SegData s) (f g : Fin S.t → ℕ) (i : ℕ) : jE S (fun l => f l + g l) i = jE S f i + jE S g i := by
  unfold jE
  split_ifs <;> rfl

theorem jE_uTop {s : ℕ} (S : SegData s) (g : Fin s → ℕ) (i : Fin s) (h : S.sigma ≤ i.val) :
    jE S (fun l => g (uTop S l)) i.val = g i := by
  unfold jE
  rw [dif_pos ⟨h, i.2⟩]
  have e : uTop S ⟨i.val - S.sigma, by unfold SegData.t; have := i.2; omega⟩ = i := by
    apply Fin.ext
    show S.sigma + (i.val - S.sigma) = i.val
    omega
  show g (uTop S ⟨i.val - S.sigma, _⟩) = g i
  rw [e]

theorem ch_cases {s : ℕ} (a : Fin (2 * s + 1)) : a = chU s ∨ (∃ i : Fin s, a = chW i) ∨ ∃ i : Fin s, a = chE i := by
  have ha := a.2
  by_cases h : a.val = 2 * s
  · exact Or.inl (Fin.ext h)
  · by_cases h2 : a.val % 2 = 0
    · exact Or.inr (Or.inl ⟨⟨a.val / 2, by omega⟩, Fin.ext (by show a.val = 2 * (a.val / 2); omega)⟩)
    · exact Or.inr (Or.inr ⟨⟨a.val / 2, by omega⟩, Fin.ext (by show a.val = 2 * (a.val / 2) + 1; omega)⟩)

set_option maxHeartbeats 1600000 in
theorem segCoreAt_of_num {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hN : NumCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    SegCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ _ O _ _ _ _ S hSq hD hH hc mm hmm n hn1 hnc β hβ L e he1 hen j
  intro (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ)
  intro hju Gu du hGI hGP hdu hGY A hcz hcw hcy hcx hy0 hγ dz dy dx
  classical
  have hp : 0 < X.p := hD.1.pos
  have hKz : CharZero (KK O) := Formalism.MainNotions.G.GLWeightTheory.dvr_fraction_field_charZero_prime S hD.1
  have hsN : segS X.TT j ≤ X.N1 := (hH.1.2.2.2.2.1 j).2
  have hQ1 : 1 ≤ X.p ^ X.G' * e := Nat.mul_pos (pow_pos hp _) he1
  obtain ⟨hroom, hnum⟩ := hN X hD hH hc mm hmm n hn1 hnc e he1 hen j (β j) (hβ j)
  obtain ⟨hdig, hU, hSt, hoP, -⟩ := hβ j
  have hA' := nb_coarseA C0 CE1 CE2 X j ju (L.jp j) du A hp dz
  have hC' := nb_coarseC C0 CE1 CE2 X j ju (L.jp j) du A hp dy
  have hdig' := nb_digits C0 CE1 CE2 X j ju (L.jp j) du A hp dz dy
  have hez : ∀ i, ∑ c, ezA C0 CE1 CE2 X j A i c ≤ X.p ^ X.G' * e := fun i =>
    nb_ez_le C0 CE1 CE2 X j A hp (β j) hdig _ i (hcw i)
  have hlb := level_bounds X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j) (L.lv j) (L.jp j) (L.ok j)
  have hjE : ∀ i : ℕ, jE (X.seg C0 CE1 CE2 j) ju i ≤ jE (X.seg C0 CE1 CE2 j) (L.lv j) i := fun i => jE_mono _ hju i

  have hduW : ∀ i : Fin (segS X.TT j), du (chW i) ≤
      (if i.val < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i) - jE (X.seg C0 CE1 CE2 j) (L.lv j) i.val := by
    intro i
    have h1 := hdu (chW i)
    have h2 := lev_deg X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j) (L.lv j) (L.jp j) (chW i)
    have h3 := segment_chain_degree_even X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j) (chW i) i rfl
    have q : (chW i).val / 2 = i.val := by show 2 * i.val / 2 = _; omega
    rw [h3, q] at h2
    have h1' : du (chW i) ≤ ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).lettersAt (L.lv j) (L.jp j)).deg (chW i) := h1
    omega
  have hduU : du (chU _) ≤ (β j).oPlus - L.jp j := by
    have h1 := hdu (chU _)
    have h2 := lev_deg X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j) (L.lv j) (L.jp j) (chU _)
    have h3 := chain_deg_U X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j) (chU _) rfl
    rw [h3, if_pos (show (chU (segS X.TT j)).val = 2 * segS X.TT j from rfl)] at h2
    have h1' : du (chU _) ≤ ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).lettersAt (L.lv j) (L.jp j)).deg (chU _) := h1
    omega

  have hy0U : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).sigma ≤ i.val → y0A C0 CE1 CE2 X j A i ≤ X.p ^ X.G' * e := by
    intro i hi
    have h := hcy i
    rw [if_neg (by omega)] at h
    have := block_y_zero_le_of_bound C0 CE1 CE2 X j A hp (β j) hdig _ hQ1 i 0 h
    omega
  have hy0S : ∀ i : Fin (segS X.TT j), i.val < (X.seg C0 CE1 CE2 j).sigma → y0A C0 CE1 CE2 X j A i ≤ (β j).sg i + X.p ^ X.G' * e := by
    intro i hi
    have h := hcy i
    rw [if_pos hi] at h
    exact block_y_zero_le_of_bound C0 CE1 CE2 X j A hp (β j) hdig _ hQ1 i _ h
  have hyz : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).sigma ≤ i.val → y0A C0 CE1 CE2 X j A i ≤ z0A C0 CE1 CE2 X j A i := by
    intro i hi
    have h1 := hcz i
    rw [if_neg (by omega)] at h1
    have h2 := hcy i
    rw [if_neg (by omega), mul_zero, add_zero] at h2
    have h3 := hroom i hi
    exact block_y_zero_le_z_zero C0 CE1 CE2 X j A hp (β j) hdig _ hQ1 i _ (by omega) h1 h2

  have oU : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).sigma ≤ i.val → (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A).o i =
      jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i) + y0A C0 CE1 CE2 X j A i + ∑ c, ezA C0 CE1 CE2 X j A i c := by
    intro i hi
    show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then 0 else _) = _
    rw [if_neg (by omega)]
  have wS : ∀ i : Fin (segS X.TT j), i.val < (X.seg C0 CE1 CE2 j).sigma → (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A).w i = du (chW i) + ∑ c, ezA C0 CE1 CE2 X j A i c := by
    intro i hi
    show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then _ else 0) = _
    rw [if_pos hi]
  have sgS : ∀ i : Fin (segS X.TT j), i.val < (X.seg C0 CE1 CE2 j).sigma → (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A).sg i = y0A C0 CE1 CE2 X j A i := by
    intro i hi
    show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then _ else 0) = _
    rw [if_pos hi]
  have oP : (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A).oPlus = L.jp j + du (chU _) + ∑ c, axA X j A c := rfl
  have dx' : L.jp j + du (chU _) + (A ((topEnd X j, true), 0) + ∑ c, axA X j A c) = (segAPlus X.TT X.aT j) := by
    rw [← dx, Fin.sum_univ_succ]
    rfl
  have hcx' : ∑ c, axA X j A c ≤ X.p ^ X.G' * e := hcx
  obtain ⟨hBL', hthr⟩ := hnum (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A) hdig' (fun i => nb_coarseA_ge C0 CE1 CE2 X j ju (L.jp j) du A hp (β j) i)
    (by
      intro i hi
      have a1 := hA' i
      have a2 := oU i hi
      have a3 := hyz i hi
      have a4 := hy0U i hi
      have a5 := hez i
      have a6 := hduW i
      rw [if_neg (by omega)] at a6
      have a7 := hjE i.val
      have a8 := (hlb.1 i hi).1
      refine ⟨by omega, by omega, ?_, ?_⟩
      · show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then _ else 0) = 0
        rw [if_neg (by omega)]
      · show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then _ else 0) = 0
        rw [if_neg (by omega)])
    (by
      intro i hi
      have a1 := hA' i
      have a2 := wS i hi
      have a3 := sgS i hi
      have a4 := hy0S i hi
      have a5 := hez i
      have a6 := hduW i
      rw [if_pos hi] at a6
      have a7 := hC' i
      refine ⟨?_, by omega, by omega, by omega, by omega⟩
      show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then 0 else _) = 0
      rw [if_pos hi])
    (by omega) (by have := hlb.2; omega)
  refine ⟨(segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A), hBL', nb_ord C0 CE1 CE2 X j ju (L.jp j) du A,
    uTot O X.m (X.seg C0 CE1 CE2 j) ju (L.jp j) (Gu * (mEps (KK O) (ezA C0 CE1 CE2 X j A) (eyA C0 CE1 CE2 X j A) (axA X j A)))
      (fun l => z0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l)) (fun l => y0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l))
      (A ((topEnd X j, true), 0)) (L.γ j), ?_, ?_⟩
  · refine uTot_mem (fun l => hyz _ (Nat.le_add_right _ _)) ?_ (by omega) (du + (dEps (ezA C0 CE1 CE2 X j A) (eyA C0 CE1 CE2 X j A) (axA X j A)))
      (intPol_mul' hGI (mEps_int _ _ _)) (hom_Pol_mul (KK O) hGP (mEps_pol (KK O) _ _ _)) ?_ ?_ ?_
    · intro l
      have hi : (X.seg C0 CE1 CE2 j).sigma ≤ (uTop (X.seg C0 CE1 CE2 j) l).val := Nat.le_add_right _ _
      have a1 := hA' (uTop (X.seg C0 CE1 CE2 j) l)
      have a2 := oU _ hi
      have a3 := hyz _ hi
      omega
    · intro a
      rw [jE_add]
      simp only [Pi.add_apply]
      rcases ch_cases a with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rw [chain_deg_U X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) _ (chU _) rfl, dEps_U,
          if_pos (show (chU (segS X.TT j)).val = 2 * segS X.TT j from rfl)]
        have q : (chU (segS X.TT j)).val / 2 = segS X.TT j := by show 2 * segS X.TT j / 2 = _; omega
        rw [q, jE_top, jE_top, oP]
        omega
      · have q : (chW i).val / 2 = i.val := by show 2 * i.val / 2 = _; omega
        have hne : ¬ (chW i).val = 2 * segS X.TT j := by have := i.2; show ¬ 2 * i.val = _; omega
        rw [segment_chain_degree_even X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) _ (chW i) i rfl, dEps_chW_eq_sum, q, if_neg hne]
        by_cases hi : i.val < (X.seg C0 CE1 CE2 j).sigma
        · rw [if_pos hi, wS i hi, jE_S _ _ hi, jE_S _ _ hi]
          omega
        · rw [if_neg hi, oU i (by omega), jE_uTop (X.seg C0 CE1 CE2 j) (y0A C0 CE1 CE2 X j A) i (by omega)]
          omega
      · have q : (chE i).val / 2 = i.val := by show (2 * i.val + 1) / 2 = _; omega
        have hne : ¬ (chE i).val = 2 * segS X.TT j := by show ¬ 2 * i.val + 1 = _; omega
        rw [chain_deg_E X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) _ (chE i) i rfl, dEps_E, q, if_neg hne, hC' i]
        by_cases hi : i.val < (X.seg C0 CE1 CE2 j).sigma
        · rw [if_pos hi, sgS i hi, jE_S _ _ hi, jE_S _ _ hi]
          omega
        · rw [if_neg hi, jE_uTop (X.seg C0 CE1 CE2 j) (y0A C0 CE1 CE2 X j A) i (by omega)]
          omega
    · have h1 := L.hγ j
      have h2 : L.jp j ≤ (X.seg C0 CE1 CE2 j).bPlus := le_trans (L.ok j).2 (min_le_right _ _)
      have h1' : ∑ c, L.γ j c = (X.seg C0 CE1 CE2 j).bPlus - L.jp j := h1
      omega
    · intro m hm k
      have hW : ∀ i : Fin (segS X.TT j), (L.LL j).vec (chW i) = true := by
        intro i
        show decide ((2 * i.val) % 2 = 0) = true
        simp
      have hE : ∀ i : Fin (segS X.TT j), (L.LL j).vec (chE i) = false := by
        intro i
        show decide ((2 * i.val + 1) % 2 = 0) = false
        simp
      have g0 := hGY k
      have g1 := ycond_mEps (K := KK O) (L.LL j) ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).T.J k) hE
        (ezA C0 CE1 CE2 X j A) (eyA C0 CE1 CE2 X j A) (axA X j A)
      have g2 := ycond_pairs (K := KK O) (r := X.m) (X.seg C0 CE1 CE2 j) (L.LL j) ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).T.J k) hW hE
        (fun l => y0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l) - m l)
      have g3 := ycond_mul (L.LL j) _ _ _ (ycond_mul (L.LL j) _ _ _ g0 g1) g2
      have hinc := rowInc_le (r := X.m) (X.seg C0 CE1 CE2 j) (L.LL j) ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).T.J k)
        (ezA C0 CE1 CE2 X j A) (axA X j A) (fun l => y0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l) - m l) (X.p ^ X.G' * e) hez hcx'
        (fun l => le_trans (Nat.sub_le _ _) (hy0U _ (Nat.le_add_right _ _)))
      have hcong := ycond_congr (K := KK O) (r := X.m)
        (LL := (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + ((n - e : ℕ) : ℝ) * ka1 X) (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A)).lettersAt (fun l => ju l + m l) (L.jp j)) (LL' := L.LL j) rfl
        ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + ((n - e : ℕ) : ℝ) * ka1 X) (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A)).T.J k) ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + ((n - e : ℕ) : ℝ) * ka1 X) (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A)).T.thr k)
      rw [hcong]
      refine ycond_mono (L.LL j) _ ?_ g3
      have t1 := thr_eq X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j) k
      have t2 := thr_eq X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + ((n - e : ℕ) : ℝ) * ka1 X) (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A) k
      have hV : ((∑ i, ((∑ c, ezA C0 CE1 CE2 X j A i c : ℕ) : ℤ) *
            (vWt (L.LL j) ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).T.J k) (chW i) : ℤ)) +
          ((∑ c, axA X j A c : ℕ) : ℤ) * (vWt (L.LL j) ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).T.J k) (chU _) : ℤ)) +
          ∑ l, ((y0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l) - m l : ℕ) : ℤ) *
            (pWt ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).T.J k) (chW (uTop (X.seg C0 CE1 CE2 j) l)) (chE (uTop (X.seg C0 CE1 CE2 j) l)) : ℤ) ≤
          ((X.N1 : ℤ) + 1) * (((X.m : ℤ) + 1) + (X.p : ℤ) ^ X.G' * e) := by
        refine le_trans hinc ?_
        have b1 : ((segS X.TT j : ℕ) : ℤ) ≤ X.N1 := by exact_mod_cast hsN
        have b2 : (0 : ℤ) ≤ ((X.p ^ X.G' * e : ℕ) : ℤ) := Int.natCast_nonneg _
        have b3 : ((X.p ^ X.G' * e : ℕ) : ℤ) = (X.p : ℤ) ^ X.G' * e := by push_cast; ring
        have b4 : (0 : ℤ) ≤ (X.m : ℤ) := Int.natCast_nonneg _
        have b5 : (0 : ℤ) ≤ (X.N1 : ℤ) := Int.natCast_nonneg _
        rw [← b3]
        nlinarith
      have hfin := hthr (capIdx (X.seg C0 CE1 CE2 j) k) _ hV
      have t1' : (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr k = _ := t1
      rw [t1', t2, ← WithTop.coe_add, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
      linarith
  · have hhead : L.head O j ju Gu = ioA (KK O) X.p C0 CE1 CE2 X j
        ((∏ l, EhS O X.m (X.seg C0 CE1 CE2 j) l ^ ju l) * EpS O X.m (X.seg C0 CE1 CE2 j) ^ L.jp j *
          rename (chainEmb (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) Gu) := rfl
    rw [hhead, segMon_eq O C0 CE1 CE2 X j ju (L.jp j) du A (L.γ j) ?_ hy0 hγ, ioBlock_eq]
    · unfold uTot
      simp only [map_mul]
      ring
    · intro i hi
      have a1 := hA' i
      have a2 := wS i hi
      rw [jE_S _ _ hi] at a1
      omega

theorem restSegCore_of_num (h : RestNumCore) : RestSegCore :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => segCoreAt_of_num h) h

end Formalism.MainNotions.ColumnSystems.Pf
