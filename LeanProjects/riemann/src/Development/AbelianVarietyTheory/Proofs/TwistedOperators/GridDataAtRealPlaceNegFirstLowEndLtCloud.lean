import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.GridParD

open GlobalTheory.SignedHC Finset

variable (G : GridData)

theorem b_add_lt {h : ℚ} (hbb : ∀ l, 1 ≤ l → l + 1 ≤ G.m → h < (G.b (l + 1) : ℚ) - G.b l) {l l' : ℕ} (h1 : 1 ≤ l)
    (hll : l < l') (hl' : l' ≤ G.m) : h + G.b l < G.b l' := by
  have e1 := hbb l h1 (by omega)
  have e2 : (G.b (l + 1) : ℚ) ≤ G.b l' := by
    rcases (Nat.succ_le_of_lt hll).eq_or_lt with h2 | h2
    · subst h2; exact le_rfl
    · exact_mod_cast (G.b_mono (l + 1) l' (by omega) h2 hl').le
  linarith

theorem b_le_b {l l' : ℕ} (h1 : 1 ≤ l) (hll : l ≤ l') (hl' : l' ≤ G.m) : (G.b l : ℚ) ≤ G.b l' := by
  rcases hll.eq_or_lt with h2 | h2
  · rw [h2]
  · exact_mod_cast (G.b_mono l l' h1 h2 hl').le

theorem signedHCGrid_cloud_le_second_vertex {q : ℕ} (h1 : 2 ≤ q) (h2 : q ≤ G.k) : (G.v q : ℚ) ≤ G.v 2 := by
  rcases h1.eq_or_lt with h | h
  · rw [h]
  · exact_mod_cast (G.v_anti 2 q le_rfl h h2).le

theorem a_def (l : ℕ) : G.a l = (G.v 2 : ℚ) + 1 / 2 + ((G.m : ℚ) + 1 - l) * G.ga := rfl

end GlobalTheory.GridParD

namespace GlobalTheory.GridParD

open GlobalTheory.SignedHC Finset

variable (G : GridData)

theorem entries_parD_le {i j : ℕ} (hi : i < G.m) (hj : j ≤ G.m) (hnear : G.NearMid)
    (hB1 : ∀ q, 2 ≤ q → q ≤ G.k → -(G.b 1 : ℚ) < G.v q)
    (hbe : ∀ l, 1 ≤ l → l ≤ G.m → ((G.t : ℚ) + 3) / 2 ≤ G.e l - G.b l) (hs : (G.s : ℚ) + 2 ≤ G.ga) :
    ∀ x ∈ entries (G.parD i j), x + ((G.s : ℚ) + 1) / 2 ≤ G.cen (G.m - i) := by
  have hga : (0 : ℚ) ≤ G.ga := by positivity
  have hs0 : (0 : ℚ) ≤ G.s := by positivity
  have hc : (G.v 2 : ℚ) + 1 / 2 + ((i : ℚ) + 1) * G.ga + G.ga / 2 - 1 ≤ G.cen (G.m - i) := by
    have h1 := hnear (G.m - i) (mem_Icc.2 ⟨by omega, by omega⟩)
    rw [G.mid_eq (by omega), a_def G, Nat.cast_sub hi.le] at h1
    have := (abs_le.1 h1).1
    linarith
  have hv2 : -(G.b 1 : ℚ) < G.v 2 := hB1 2 le_rfl G.two_le_k
  have hbig : (G.v 2 : ℚ) + ((G.s : ℚ) + 1) / 2 ≤ G.cen (G.m - i) := by
    have : (G.ga : ℚ) ≤ ((i : ℚ) + 1) * G.ga := le_mul_of_one_le_left hga (by linarith [show (0 : ℚ) ≤ i by positivity])
    linarith
  intro x hx
  obtain ⟨sg, hsg⟩ := mem_entries.1 hx
  rcases GridData.mem_parD.1 hsg with ⟨h1, -⟩ | ⟨l, hl1, hl2, he⟩ | ⟨l, hl1, hl2, hb, -⟩ | ⟨l, hl1, hl2, hb, -⟩
  · obtain ⟨q, hq1, hq2, rfl⟩ := GridData.mem_cloud.1 h1
    have := signedHCGrid_cloud_le_second_vertex G hq1 hq2
    linarith
  · have e : x = -(G.b l : ℚ) := congrArg Prod.fst he
    have := b_le_b G le_rfl hl1 hl2
    rw [e]; linarith
  · have hb' := abs_sub_le_of_mem_block hb
    have := hbe l hl1 (by omega)
    have := b_le_b G le_rfl hl1 (by omega)
    have := (abs_le.1 hb').2
    simp only at this ⊢
    linarith
  · have hb' := abs_sub_le_of_mem_block hb
    have h1 := hnear l (mem_Icc.2 ⟨by omega, hl2⟩)
    rw [G.mid_eq (by omega), a_def G] at h1
    have h2 := (abs_le.1 h1).2
    have h3 := (abs_le.1 hb').2
    have hl : ((G.m : ℚ) + 1 - l) * G.ga ≤ (i : ℚ) * G.ga := by
      refine mul_le_mul_of_nonneg_right ?_ hga
      have : ((G.m - i + 1 : ℕ) : ℚ) ≤ l := by exact_mod_cast hl1
      push_cast [Nat.cast_sub hi.le] at this
      linarith
    simp only at h3 ⊢
    linarith

end GlobalTheory.GridParD

namespace GlobalTheory.GridParD

open GlobalTheory.SignedHC Finset

variable (G : GridData)

theorem eq_low_of_mem_parD {i j : ℕ} {x : ℚ × Bool} (hx : x ∈ G.parD i j) (hs : x.2 = false) :
    ∃ l, j + 2 ≤ l ∧ l ≤ G.m ∧ ¬ Even (l - j - 1) ∧ x = (-(G.b l : ℚ), false) := by
  rcases GridData.mem_parD.1 hx with ⟨-, h⟩ | ⟨l, hl1, hl2, he⟩ | ⟨l, -, -, -, h⟩ | ⟨l, -, -, -, h⟩
  · rw [h] at hs; exact absurd hs (by simp)
  · have hs' : ¬ (l ≤ j + 1 ∨ Even (l - j - 1)) := by simpa [he] using hs
    refine ⟨l, by omega, hl2, fun h => hs' (Or.inr h), ?_⟩
    rw [he]; exact Prod.ext rfl (by simpa [he] using hs)
  · rw [h] at hs; exact absurd hs (by simp)
  · rw [h] at hs; exact absurd hs (by simp)

theorem lt_abs_low {i j : ℕ} {h : ℚ} (h0 : 0 ≤ h) (hnear : G.NearMid)
    (hB1 : ∀ q, 2 ≤ q → q ≤ G.k → -(G.b 1 : ℚ) < G.v q)
    (heb : ∀ l, 1 ≤ l → l + 1 ≤ G.m → ((G.t : ℚ) + 3) / 2 ≤ G.b (l + 1) - G.e l)
    (hbb : ∀ l, 1 ≤ l → l + 1 ≤ G.m → h < (G.b (l + 1) : ℚ) - G.b l) (hga : h + G.s + 2 ≤ G.ga)
    {l : ℕ} (hl1 : j + 2 ≤ l) (hl2 : l ≤ G.m) (hodd : ¬ Even (l - j - 1)) {y : ℚ × Bool} (hy : y ∈ G.parD i j) (hys : y.2 = true) :
    h < |-(G.b l : ℚ) - y.1| := by
  have hga0 : (0 : ℚ) ≤ G.ga := by positivity
  have hs0 : (0 : ℚ) ≤ G.s := by positivity
  have hlow : h + G.b 1 < G.b l := b_add_lt G hbb le_rfl (by omega) hl2
  rcases GridData.mem_parD.1 hy with ⟨h1, -⟩ | ⟨l', hl1', hl2', he⟩ | ⟨l', hl1', hl2', hb, -⟩ |
      ⟨l', hl1', hl2', hb, -⟩
  · obtain ⟨q, hq1, hq2, e⟩ := GridData.mem_cloud.1 h1
    have := hB1 q hq1 hq2
    rw [e]
    exact lt_abs.2 (Or.inr (by linarith))
  · have e : y.1 = -(G.b l' : ℚ) := congrArg Prod.fst he
    rcases lt_trichotomy l' l with hll | hll | hll
    · have := b_add_lt G hbb hl1' hll hl2
      rw [e]; exact lt_abs.2 (Or.inr (by linarith))
    · exfalso
      subst hll
      have hys' : l' ≤ j + 1 ∨ Even (l' - j - 1) := by simpa [he] using hys
      rcases hys' with h' | h'
      · omega
      · exact hodd h'
    · have := b_add_lt G hbb (by omega) hll hl2'
      rw [e]; exact lt_abs.2 (Or.inl (by linarith))
  · have hb' := (abs_le.1 (abs_sub_le_of_mem_block hb)).1
    have := heb l' hl1' (by omega)
    have := b_add_lt G hbb (by omega : 1 ≤ l' + 1) (by omega : l' + 1 < l) hl2
    exact lt_abs.2 (Or.inr (by linarith))
  · have hb' := (abs_le.1 (abs_sub_le_of_mem_block hb)).1
    have h1 := hnear l' (mem_Icc.2 ⟨by omega, hl2'⟩)
    rw [G.mid_eq (by omega), a_def G] at h1
    have h2 := (abs_le.1 h1).1
    have hl : (G.ga : ℚ) ≤ ((G.m : ℚ) + 1 - l') * G.ga := by
      refine le_mul_of_one_le_left hga0 ?_
      have : (l' : ℚ) ≤ G.m := by exact_mod_cast hl2'
      linarith
    have hv2 : -(G.b 1 : ℚ) < G.v 2 := hB1 2 le_rfl G.two_le_k
    have := b_le_b G le_rfl (by omega : 1 ≤ l) hl2
    exact lt_abs.2 (Or.inr (by linarith))

theorem gapOver_parD (i j : ℕ) {h : ℚ} (h0 : 0 ≤ h) (hnear : G.NearMid)
    (hB1 : ∀ q, 2 ≤ q → q ≤ G.k → -(G.b 1 : ℚ) < G.v q)
    (heb : ∀ l, 1 ≤ l → l + 1 ≤ G.m → ((G.t : ℚ) + 3) / 2 ≤ G.b (l + 1) - G.e l)
    (hbb : ∀ l, 1 ≤ l → l + 1 ≤ G.m → h < (G.b (l + 1) : ℚ) - G.b l) (hga : h + G.s + 2 ≤ G.ga) :
    GapOver (G.parD i j) h := by
  have key : ∀ x ∈ G.parD i j, ∀ y ∈ G.parD i j, x.2 = false → y.2 = true → h < |x.1 - y.1| := by
    intro x hx y hy hxs hys
    obtain ⟨l, hl1, hl2, hodd, rfl⟩ := eq_low_of_mem_parD G hx hxs
    exact lt_abs_low G h0 hnear hB1 heb hbb hga hl1 hl2 hodd hy hys
  intro x hx y hy hs
  rcases Bool.eq_false_or_eq_true x.2 with hxs | hxs
  · have hys : y.2 = false := by rw [hxs] at hs; simpa using hs.symm
    rw [abs_sub_comm]
    exact key y hy x hx hys hxs
  · have hys : y.2 = true := by rw [hxs] at hs; simpa using hs.symm
    exact key x hx y hy hxs hys

end GlobalTheory.GridParD

namespace GlobalTheory.GridParD

open GlobalTheory.SignedHC Finset

variable (G : GridData)

theorem int_of_mem_entries_parD {i j : ℕ} (ht : Odd G.t) (hs : Odd G.s) {x : ℚ} (hx : x ∈ entries (G.parD i j)) :
    ∃ z : ℤ, x = z := by
  have hblk : ∀ {c : ℤ} {n : ℕ}, Odd n → ∀ y ∈ TPar.block (c : ℚ) n, ∃ z : ℤ, y = z := by
    intro c n hn y hy
    obtain ⟨w, rfl⟩ := hn
    obtain ⟨a, -, rfl⟩ := mem_block.1 hy
    exact ⟨c + w - a, by push_cast; ring⟩
  obtain ⟨sg, hsg⟩ := mem_entries.1 hx
  rcases GridData.mem_parD.1 hsg with ⟨h1, -⟩ | ⟨l, -, -, he⟩ | ⟨l, -, -, hb, -⟩ | ⟨l, -, -, hb, -⟩
  · obtain ⟨q, -, -, e⟩ := GridData.mem_cloud.1 h1
    exact ⟨_, e⟩
  · exact ⟨-G.b l, by have := congrArg Prod.fst he; simp only at this; rw [this]; push_cast; ring⟩
  · exact hblk ht _ hb
  · exact hblk hs _ hb

theorem card_parD_le {i j : ℕ} (hi : i ≤ G.m) : (G.parD i j).card ≤ G.rankD i j := by
  have h1 : (plus G.cloud).card ≤ G.k - 1 := by
    refine card_image_le.trans (card_image_le.trans ?_)
    simp
  have h2 : ((Icc 1 G.m).image fun l => (-(G.b l : ℚ), decide (l ≤ j + 1 ∨ Even (l - j - 1)))).card ≤ G.m := by
    refine card_image_le.trans ?_
    simp
  have h3 : (plus ((Icc 1 j).biUnion G.blockM)).card ≤ j * G.t := by
    refine card_image_le.trans (card_biUnion_le.trans ?_)
    simp [GridData.blockM]
  have h4 : (plus ((Icc (G.m - i + 1) G.m).biUnion G.blockC)).card ≤ i * G.s := by
    refine card_image_le.trans (card_biUnion_le.trans ?_)
    simp only [GridData.blockC, card_block, sum_const, Nat.card_Icc, smul_eq_mul]
    exact Nat.mul_le_mul_right _ (by omega)
  have hk := G.two_le_k
  unfold GridData.parD GridData.rankD GridData.r
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _)) _).trans ?_
  omega

theorem parD_succ {i j : ℕ} (hi : i < G.m) : G.parD (i + 1) j = G.parD i j ∪ plus (G.blockC (G.m - i)) := by
  have e : Icc (G.m - (i + 1) + 1) G.m = insert (G.m - i) (Icc (G.m - i + 1) G.m) := by
    ext l; simp only [mem_Icc, mem_insert]; omega
  rw [GridData.parD, GridData.parD, e, biUnion_insert, plus_union]
  ext x
  simp only [mem_union]
  tauto

end GlobalTheory.GridParD

namespace GlobalTheory.GridParD

open GlobalTheory.SignedHC Finset

theorem gapOver_shift {S : SPar} {g : ℚ} (h : ℚ) (H : GapOver S g) : GapOver (shift h S) g := by
  intro x hx y hy hs
  have := H _ (mem_shift.1 hx) _ (mem_shift.1 hy) hs
  simpa [sub_sub_sub_cancel_right] using this

theorem gapOver_flip {S : SPar} {g : ℚ} (H : GapOver S g) : GapOver (flip S) g := by
  intro x hx y hy hs
  exact H (x.1, !x.2) (mem_flip.1 hx) (y.1, !y.2) (mem_flip.1 hy) fun e => hs (Bool.not_inj e)

theorem GapOver.isRegular {S : SPar} {g : ℚ} (hg : 0 ≤ g) (H : GapOver S g) : IsRegular S := by
  intro x hx y hy e
  by_contra hne
  have := H x hx y hy hne
  rw [e, sub_self, abs_zero] at this
  linarith

theorem flip_dualPar (S : SPar) : flip (dualPar S) = dualPar (flip S) := by
  simp only [GlobalTheory.SignedHC.flip, dualPar, Finset.image_image]
  rfl

variable (D : D7) (τ : D.what₂.Tau)

theorem gridDataAtRealPlace_neg_firstLowEnd_lt_cloud : ∀ q, 2 ≤ q → q ≤ (grid D τ).k → -((grid D τ).b 1 : ℚ) < (grid D τ).v q := by
  obtain ⟨hv, hb, -⟩ := GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D) (cen D τ)
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have h1 := (D.hc τ).u_last_gt (by omega) (by omega)
  have h2 := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
  have e1 : ((D.hc τ).u ⟨D.R.k - 2 + 1, by omega⟩) = (D.hc τ).u ⟨D.R.k - 1, by omega⟩ := by
    congr 1; ext; simp only; omega
  have hb1 : (D.hc τ).b ⟨0, by omega⟩ = ((grid D τ).b 1 : ℚ) := hb ⟨0, by omega⟩
  have hvk : (D.hc τ).v ⟨D.R.k - 2, by omega⟩ = ((grid D τ).v D.R.k : ℚ) := by
    have := hv ⟨D.R.k - 2, by omega⟩
    rw [this]; congr 2; simp only; omega
  intro q hq1 hq2
  have hvq : ((grid D τ).v D.R.k : ℚ) ≤ (grid D τ).v q := by
    rcases hq2.eq_or_lt with h | h
    · rw [h]; rfl
    · exact_mod_cast ((grid D τ).v_anti q D.R.k hq1 h le_rfl).le
  rw [e1] at h2
  linarith

theorem grid_hbe : ∀ l, 1 ≤ l → l ≤ (grid D τ).m → (((grid D τ).t : ℚ) + 3) / 2 ≤ (grid D τ).e l - (grid D τ).b l := by
  obtain ⟨-, hb, he⟩ := GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D) (cen D τ)
  intro l h1 h2
  obtain ⟨l, rfl⟩ : ∃ l0, l = l0 + 1 := ⟨l - 1, by omega⟩
  have := (D.hc τ).gap_be ⟨l, by change _ ≤ D.R.m at h2; omega⟩
  rw [hb, he] at this
  exact this

theorem grid_heb : ∀ l, 1 ≤ l → l + 1 ≤ (grid D τ).m →
    (((grid D τ).t : ℚ) + 3) / 2 ≤ (grid D τ).b (l + 1) - (grid D τ).e l := by
  obtain ⟨-, hb, he⟩ := GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D) (cen D τ)
  intro l h1 h2
  obtain ⟨l, rfl⟩ : ∃ l0, l = l0 + 1 := ⟨l - 1, by omega⟩
  have := (D.hc τ).gap_eb ⟨l, by change _ ≤ D.R.m at h2; omega⟩ (by change _ ≤ D.R.m at h2; simp only; omega)
  rw [hb, he] at this
  exact this

theorem grid_hbb (hS : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D) : ∀ l, 1 ≤ l → l + 1 ≤ (grid D τ).m →
    2 * (bigN D : ℚ) ^ 3 < (grid D τ).b (l + 1) - (grid D τ).b l := by
  obtain ⟨-, hb, -⟩ := GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D) (cen D τ)
  intro l h1 h2
  obtain ⟨l, rfl⟩ : ∃ l0, l = l0 + 1 := ⟨l - 1, by omega⟩
  have := hS.2 τ l (by change _ ≤ D.R.m at h2; omega)
  rw [hb, hb] at this
  exact this

theorem grid_hga : 2 * (bigN D : ℚ) ^ 3 + (grid D τ).s + 2 ≤ (grid D τ).ga := by
  have h := (isLeast_gap D).1.2.1
  have : 2 * bigN D ^ 3 + sLen D + 2 ≤ gap D := by omega
  exact_mod_cast this

theorem odd_r : Odd D.R.r := by
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have := D.R.m_add_three_le_k
  exact ⟨a + b - 1, by unfold Ranks.r; omega⟩

theorem odd_sLen : Odd (sLen D) := by
  obtain ⟨a, ha⟩ := odd_r D
  exact ⟨a + 3, by unfold sLen; omega⟩

theorem odd_rkV_iff (i j : ℕ) : Odd (rkV D i j) ↔ ¬ Odd (i + j) := by
  have hr := odd_r D
  have ht := D.R.t_odd
  have hs := odd_sLen D
  obtain ⟨a, ha⟩ := hr
  obtain ⟨b, hb⟩ := ht
  obtain ⟨c, hc⟩ := hs
  unfold rkV
  rw [hc, hb, ha]
  have e1 : j * (2 * b + 1) = 2 * (j * b) + j := by ring
  have e2 : i * (2 * c + 1) = 2 * (i * c) + i := by ring
  rw [e1, e2]
  generalize j * b = A
  generalize i * c = B
  simp only [Nat.odd_iff]
  omega

end GlobalTheory.GridParD

end
