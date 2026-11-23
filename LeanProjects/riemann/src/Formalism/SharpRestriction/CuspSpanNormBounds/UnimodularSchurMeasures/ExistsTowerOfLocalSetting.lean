import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Formalism.FlagUnipotentLattices.ThirdHeightFromSecond

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Matrix Finset
open scoped InnerProductSpace
open Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.BasicNotions Formalism.BasicNotions.TH

def LocalOrderedConclusion (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ)
    (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : CayleySignature.Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∃ B : H → Vp, IsBesselMapSm z (psiGen k r z c) σ π B ∧ HasOrdLe k r (rk48 k r ^ 2 / 2 + 1) σ B ∧
    ∃ x ∈ smoothVecs (k := k) (r := r) σ, B x ≠ 0

def OrderedAtRanks (D : D7) (C : ℝ) : Prop :=
  ∀ (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (c : Fin D.R.rS → ℂ) (u : Fin D.R.k → ℝ) (v : Fin (D.R.k - 1) → ℝ)
    (b : Fin (2 * D.R.rS + 2) → ℝ), RealPlaceNumericalSetting D.R.k D.R.rS z c u v b → GapC C D.R.k D.R.rS b →
    LocalOrderedConclusion D.R.k D.R.rS z c u v b

theorem two_rS_add_two_eq_m (D : D7) : 2 * D.R.rS + 2 = D.R.m := by
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := h1
  show 2 * (D.R.m / 2 - 1) + 2 = D.R.m
  omega

theorem localRank_eq_r (D : D7) : rk48 D.R.k D.R.rS = D.R.r := by
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := h1
  show 2 * (D.R.m / 2 - 1) + D.R.k + 1 = D.R.k + D.R.m - 1
  omega

theorem mem_discrete_params_iff {D : D7} (P : TPar D) (j : ℕ) (τ : D.what₂.Tau) (x : ℚ × Bool) (hx : x ∈ P.Dpar j τ) :
    ∃ w : ℚ, x.1 = w + (if Odd j then P.eta τ else 0) ∧
      ((x.2 = true ∧ ∃ i, w = P.v τ i) ∨
        (∃ i : Fin D.R.m, w = -P.b τ i ∧ (x.2 = true ↔ (i.1 ≤ j ∨ Even (i.1 - j)))) ∨
        (x.2 = true ∧ ∃ i : Fin D.R.m, i.1 < j ∧ ∃ a : ℕ, a < P.t ∧ w = -P.e τ i + ((P.t : ℚ) - 1) / 2 - a)) := by
  unfold TPar.Dpar at hx
  obtain ⟨⟨w, bo⟩, ha, hxe⟩ := Finset.mem_image.mp hx
  subst hxe
  dsimp only
  refine ⟨w, rfl, ?_⟩
  rcases Finset.mem_union.mp ha with ha | ha
  · rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp ha
      simp only [Prod.mk.injEq] at hi
      exact Or.inl ⟨hi.2.symm, i, hi.1.symm⟩
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp ha
      simp only [Prod.mk.injEq] at hi
      refine Or.inr (Or.inl ⟨i, hi.1.symm, ?_⟩)
      rw [← hi.2]
      simp only [decide_eq_true_eq]
  · obtain ⟨i, hi, hmem⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨y, hy, hyw⟩ := Finset.mem_image.mp hmem
    have hij : i.1 < j := (Finset.mem_filter.mp hi).2
    unfold TPar.block at hy
    obtain ⟨a, ha', rfl⟩ := Finset.mem_image.mp hy
    simp only [Prod.mk.injEq] at hyw
    exact Or.inr (Or.inr ⟨hyw.2.symm, i, hij, a, Finset.mem_range.mp ha', hyw.1.symm⟩)

private theorem noncompact_gaps_of_spacing_lemma {D : D7} (P : TPar D) (g : ℚ) (τ : D.what₂.Tau) (j : ℕ) (M3 : ℚ)
    (hM : 0 ≤ M3) (hg : 2 * M3 + (P.t : ℚ) + 3 ≤ g)
    (h1 : ∀ τ i (h0 : 0 < D.R.m), -P.b τ ⟨0, h0⟩ < P.v τ i)
    (h2 : ∀ τ (i i' : Fin D.R.m), i < i' → g ≤ P.b τ i' - P.b τ i)
    (h3 : ∀ τ (i : Fin D.R.m) (h : i.1 + 1 < D.R.m), P.e τ i < P.b τ ⟨i.1 + 1, h⟩)
    (i : Fin D.R.m) (hji : j < i.1) (w : ℚ)
    (hw : (∃ i', w = P.v τ i') ∨ (∃ i' : Fin D.R.m, w = -P.b τ i' ∧ i' ≠ i) ∨
      (∃ i' : Fin D.R.m, i'.1 < j ∧ ∃ a : ℕ, a < P.t ∧ w = -P.e τ i' + ((P.t : ℚ) - 1) / 2 - a)) :
    M3 < |w - -P.b τ i| := by
  have hi := i.isLt
  have ht0 : (0:ℚ) ≤ (P.t : ℚ) := Nat.cast_nonneg _
  rcases hw with ⟨i', rfl⟩ | ⟨i', rfl, hne⟩ | ⟨i', hi'j, a, ha, rfl⟩
  · have h0 : 0 < D.R.m := by omega
    have e1 := h1 τ i' h0
    have e2 := h2 τ ⟨0, h0⟩ i (Fin.lt_def.mpr (show 0 < i.1 by omega))
    rw [abs_of_pos (by linarith)]
    linarith
  · rcases lt_or_gt_of_ne hne with h | h
    · have := h2 τ i' i h
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have := h2 τ i i' h
      rw [abs_of_nonpos (by linarith)]
      linarith
  · have hlt : i'.1 + 1 < D.R.m := by omega
    have e3 := h3 τ i' hlt
    have e4 := h2 τ ⟨i'.1 + 1, hlt⟩ i (Fin.lt_def.mpr (show i'.1 + 1 < i.1 by omega))
    have ha' : (a : ℚ) + 1 ≤ (P.t : ℚ) := by exact_mod_cast Nat.succ_le_of_lt ha
    rw [abs_of_pos (by linarith)]
    linarith

theorem noncompact_gaps_of_spacing {D : D7} (P : TPar D) (g : ℚ)
    (hg : 2 * ((D.R.r + D.R.m * P.t : ℕ) : ℚ) ^ 3 + (P.t : ℚ) + 3 ≤ g)
    (h1 : ∀ τ i (h0 : 0 < D.R.m), -P.b τ ⟨0, h0⟩ < P.v τ i)
    (h2 : ∀ τ (i i' : Fin D.R.m), i < i' → g ≤ P.b τ i' - P.b τ i)
    (h3 : ∀ τ (i : Fin D.R.m) (h : i.1 + 1 < D.R.m), P.e τ i < P.b τ ⟨i.1 + 1, h⟩) : NCGaps P := by
  intro j hj τ x hx y hy hxy
  have hM : (0:ℚ) ≤ ((D.R.r + D.R.m * P.t : ℕ) : ℚ) ^ 3 := by positivity
  obtain ⟨w, hw, hxc⟩ := mem_discrete_params_iff P j τ x hx
  obtain ⟨w', hw', hyc⟩ := mem_discrete_params_iff P j τ y hy
  have hd : x.1 - y.1 = w - w' := by rw [hw, hw']; ring
  rw [hd]
  cases hx2 : x.2 <;> cases hy2 : y.2
  · exact absurd (hx2.trans hy2.symm) hxy
  · rw [hx2] at hxc
    rw [hy2] at hyc
    obtain ⟨i, rfl, hi⟩ : ∃ i : Fin D.R.m, w = -P.b τ i ∧ ¬ (i.1 ≤ j ∨ Even (i.1 - j)) := by
      rcases hxc with ⟨h, -⟩ | ⟨i, hwi, hiff⟩ | ⟨h, -⟩
      · exact absurd h Bool.false_ne_true
      · exact ⟨i, hwi, fun h => absurd (hiff.mpr h) Bool.false_ne_true⟩
      · exact absurd h Bool.false_ne_true
    have hji : j < i.1 := by
      by_contra hc
      exact hi (Or.inl (by omega))
    have hy' : (∃ i', w' = P.v τ i') ∨ (∃ i' : Fin D.R.m, w' = -P.b τ i' ∧ i' ≠ i) ∨
        (∃ i' : Fin D.R.m, i'.1 < j ∧ ∃ a : ℕ, a < P.t ∧ w' = -P.e τ i' + ((P.t : ℚ) - 1) / 2 - a) := by
      rcases hyc with ⟨-, i', h⟩ | ⟨i', h, hiff⟩ | ⟨-, i', hlt, a, ha, h⟩
      · exact Or.inl ⟨i', h⟩
      · refine Or.inr (Or.inl ⟨i', h, ?_⟩)
        rintro rfl
        exact hi (hiff.mp rfl)
      · exact Or.inr (Or.inr ⟨i', hlt, a, ha, h⟩)
    rw [abs_sub_comm]
    exact noncompact_gaps_of_spacing_lemma P g τ j _ hM hg h1 h2 h3 i hji w' hy'
  · rw [hx2] at hxc
    rw [hy2] at hyc
    obtain ⟨i, rfl, hi⟩ : ∃ i : Fin D.R.m, w' = -P.b τ i ∧ ¬ (i.1 ≤ j ∨ Even (i.1 - j)) := by
      rcases hyc with ⟨h, -⟩ | ⟨i, hwi, hiff⟩ | ⟨h, -⟩
      · exact absurd h Bool.false_ne_true
      · exact ⟨i, hwi, fun h => absurd (hiff.mpr h) Bool.false_ne_true⟩
      · exact absurd h Bool.false_ne_true
    have hji : j < i.1 := by
      by_contra hc
      exact hi (Or.inl (by omega))
    have hx' : (∃ i', w = P.v τ i') ∨ (∃ i' : Fin D.R.m, w = -P.b τ i' ∧ i' ≠ i) ∨
        (∃ i' : Fin D.R.m, i'.1 < j ∧ ∃ a : ℕ, a < P.t ∧ w = -P.e τ i' + ((P.t : ℚ) - 1) / 2 - a) := by
      rcases hxc with ⟨-, i', h⟩ | ⟨i', h, hiff⟩ | ⟨-, i', hlt, a, ha, h⟩
      · exact Or.inl ⟨i', h⟩
      · refine Or.inr (Or.inl ⟨i', h, ?_⟩)
        rintro rfl
        exact hi (hiff.mp rfl)
      · exact Or.inr (Or.inr ⟨i', hlt, a, ha, h⟩)
    exact noncompact_gaps_of_spacing_lemma P g τ j _ hM hg h1 h2 h3 i hji w hx'
  · exact absurd (hx2.trans hy2.symm) hxy

theorem sub_ge_of_spaced_seq {m : ℕ} {g : ℤ} (hg : 0 ≤ g) (b : ℕ → ℤ) (hb : ∀ i, i + 1 < m → g ≤ b (i + 1) - b i) :
    ∀ i j, i < j → j < m → g ≤ b j - b i := by
  intro i j hij hjm
  induction j with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
    · have e1 := ih h (by omega)
      have e2 := hb n (by omega)
      linarith
    · subst h
      exact hb _ (by omega)

def gapCentre (m : ℕ) (g : ℤ) (b : ℕ → ℤ) (j : ℕ) : ℤ := if j + 1 < m then (b j + b (j + 1)) / 2 else b j + g

theorem lt_gapCentre {m : ℕ} {g : ℤ} (hg : 2 ≤ g) (b : ℕ → ℤ) (hb : ∀ i, i + 1 < m → g ≤ b (i + 1) - b i) (j : ℕ) :
    b j < gapCentre m g b j := by
  unfold gapCentre
  split_ifs with h
  · have := hb j h
    omega
  · omega

theorem gapCentre_lt_succ {m : ℕ} {g : ℤ} (hg : 2 ≤ g) (b : ℕ → ℤ) (hb : ∀ i, i + 1 < m → g ≤ b (i + 1) - b i) (j : ℕ)
    (h : j + 1 < m) : gapCentre m g b j < b (j + 1) := by
  unfold gapCentre
  rw [if_pos h]
  have := hb j h
  omega

def towerOfIntegers (D : D7) (X : ThetaX D) (t : ℕ) (h1 : Odd t) (h2 : D.R.r + 5 ≤ t) (uZ : Fin D.R.k → ℤ)
    (vZ : Fin (D.R.k - 1) → ℤ) (bN : ℕ → ℤ) (g : ℤ) : TPar D where
  t := t
  t_odd := h1
  t_ge := h2
  u := fun _ i => (uZ i : ℚ) + 1 / 2
  v := fun _ i => (vZ i : ℚ)
  b := fun _ j => (bN j.1 : ℚ)
  e := fun _ j => (gapCentre D.R.m g bN j.1 : ℚ)
  eta := fun τ => -X.infTy X.etaT τ
  eta_half := by
    intro τ
    rcases X.etaT_inf τ with h | h
    · right; rw [h]
    · left; rw [h]; ring

theorem tower_hyp_of_integer_params (D : D7) (X : ThetaX D) (t : ℕ) (h1 : Odd t) (h2 : D.R.r + 5 ≤ t) (h18 : 1801 ≤ D.R.r + t) (uZ : Fin D.R.k → ℤ)
    (vZ : Fin (D.R.k - 1) → ℤ) (bN : ℕ → ℤ)
    (huv : ∀ i : Fin (D.R.k - 1), vZ i ≤ uZ ⟨i.1, by omega⟩ ∧ uZ ⟨i.1 + 1, by omega⟩ < vZ i)
    (hub : ∀ i, -bN 0 ≤ uZ i)
    (hb : ∀ i, i + 1 < D.R.m → 2 * ((D.R.r + D.R.m * t : ℕ) : ℤ) ^ 3 + (t : ℤ) + 4 ≤ bN (i + 1) - bN i) :
    Hyp3 X (towerOfIntegers D X t h1 h2 uZ vZ bN (2 * ((D.R.r + D.R.m * t : ℕ) : ℤ) ^ 3 + (t : ℤ) + 4)) := by
  have hpow : (0:ℤ) ≤ ((D.R.r + D.R.m * t : ℕ) : ℤ) ^ 3 := by positivity
  have ht0 : (0:ℤ) ≤ (t : ℤ) := by positivity
  generalize hGd : 2 * ((D.R.r + D.R.m * t : ℕ) : ℤ) ^ 3 + (t : ℤ) + 4 = G at hb ⊢
  have hGt : (t : ℤ) + 4 ≤ G := by rw [← hGd]; linarith
  have hG0 : (0:ℤ) ≤ G := by linarith
  have hG2 : (2:ℤ) ≤ G := by linarith
  have hmono := sub_ge_of_spaced_seq hG0 bN hb
  have hle : ∀ i j, i ≤ j → j < D.R.m → bN i ≤ bN j := by
    intro i j hij hj
    rcases Nat.lt_or_eq_of_le hij with h | h
    · have := hmono i j h hj
      linarith
    · rw [h]
  have he1 : ∀ j, G - 1 ≤ 2 * (gapCentre D.R.m G bN j - bN j) := by
    intro j
    unfold gapCentre
    split_ifs with h
    · have := hb j h
      omega
    · omega
  have he2 : ∀ j, j + 1 < D.R.m → G ≤ 2 * (bN (j + 1) - gapCentre D.R.m G bN j) := by
    intro j h
    unfold gapCentre
    rw [if_pos h]
    have := hb j h
    omega
  have hsep : ∀ j j', j < j' → j' < D.R.m →
      2 * G - 1 ≤ 2 * (gapCentre D.R.m G bN j' - gapCentre D.R.m G bN j) := by
    intro j j' hjj hj'
    have e1 := he2 j (by omega)
    have e2 := he1 j'
    have e3 := hle (j + 1) j' (by omega) hj'
    linarith
  have hvb : ∀ i : Fin (D.R.k - 1), -bN 0 + 1 ≤ vZ i := by
    intro i
    have e1 := (huv i).2
    have e2 := hub ⟨i.1 + 1, by omega⟩
    linarith
  have hGq : ((G : ℤ) : ℚ) = 2 * ((D.R.r + D.R.m * t : ℕ) : ℚ) ^ 3 + (t : ℚ) + 4 := by
    rw [← hGd]
    push_cast
    try ring
  have htq : (0:ℚ) ≤ (t : ℚ) := by positivity
  unfold Hyp3
  refine ⟨h18, ?_, ?_, ?_, ?_, fun τ => rfl⟩
  · intro τ
    refine ⟨fun i => ⟨?_, ?_⟩, fun hk hm => ?_, fun j => ?_, fun j hj => ?_⟩
    · dsimp only [towerOfIntegers]
      have c : ((vZ i : ℤ) : ℚ) ≤ _ := Int.cast_le.mpr (huv i).1
      linarith
    · dsimp only [towerOfIntegers]
      have c : (((uZ _ + 1 : ℤ)) : ℚ) ≤ _ := Int.cast_le.mpr (Int.add_one_le_of_lt (huv i).2)
      push_cast at c
      linarith
    · dsimp only [towerOfIntegers]
      have c : ((-bN 0 : ℤ) : ℚ) ≤ _ := Int.cast_le.mpr (hub ⟨D.R.k - 1, by omega⟩)
      push_cast at c
      linarith
    · dsimp only [towerOfIntegers]
      exact_mod_cast lt_gapCentre hG2 bN hb j.1
    · dsimp only [towerOfIntegers]
      exact_mod_cast gapCentre_lt_succ hG2 bN hb j.1 hj
  · intro τ
    exact ⟨fun i => ⟨uZ i, rfl⟩, fun i => ⟨vZ i, rfl⟩, fun j => ⟨bN j.1, rfl⟩,
      fun j => ⟨gapCentre D.R.m G bN j.1, rfl⟩⟩
  · intro τ j
    have hj := j.isLt
    have hE1 := he1 j.1
    have hb0j := hle 0 j.1 (Nat.zero_le _) hj
    have hGtq : (t : ℚ) + 4 ≤ ((G : ℤ) : ℚ) := by exact_mod_cast hGt
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun j' hj' x hx => ?_⟩
    · dsimp only [towerOfIntegers]
      have e1 := hub i
      have key : (t : ℤ) + 3 ≤ 2 * (uZ i + gapCentre D.R.m G bN j.1) := by linarith
      have keyq : (((t : ℤ) + 3 : ℤ) : ℚ) ≤ ((2 * (uZ i + gapCentre D.R.m G bN j.1) : ℤ) : ℚ) :=
        Int.cast_le.mpr key
      push_cast at keyq
      rw [le_abs]
      left
      linarith
    · dsimp only [towerOfIntegers]
      have e1 := hvb i
      have key : (t : ℤ) + 3 ≤ 2 * (vZ i + gapCentre D.R.m G bN j.1) := by linarith
      have keyq : (((t : ℤ) + 3 : ℤ) : ℚ) ≤ ((2 * (vZ i + gapCentre D.R.m G bN j.1) : ℤ) : ℚ) :=
        Int.cast_le.mpr key
      push_cast at keyq
      rw [le_abs]
      left
      linarith
    · dsimp only [towerOfIntegers]
      rcases Nat.lt_or_ge j.1 i.1 with hij | hij
      · have e1 := hle (j.1 + 1) i.1 (by omega) i.isLt
        have e2 := he2 j.1 (by omega)
        have key : (t : ℤ) + 3 ≤ 2 * (bN i.1 - gapCentre D.R.m G bN j.1) := by linarith
        have keyq : (((t : ℤ) + 3 : ℤ) : ℚ) ≤ ((2 * (bN i.1 - gapCentre D.R.m G bN j.1) : ℤ) : ℚ) :=
          Int.cast_le.mpr key
        push_cast at keyq
        rw [le_abs]
        right
        linarith
      · have e1 := hle i.1 j.1 hij hj
        have key : (t : ℤ) + 3 ≤ 2 * (gapCentre D.R.m G bN j.1 - bN i.1) := by linarith
        have keyq : (((t : ℤ) + 3 : ℤ) : ℚ) ≤ ((2 * (gapCentre D.R.m G bN j.1 - bN i.1) : ℤ) : ℚ) :=
          Int.cast_le.mpr key
        push_cast at keyq
        rw [le_abs]
        left
        linarith
    · dsimp only [towerOfIntegers] at hx ⊢
      unfold TPar.block at hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      have ha' : (a : ℚ) + 1 ≤ (t : ℚ) := by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp ha)
      have ha0 : (0 : ℚ) ≤ (a : ℚ) := Nat.cast_nonneg _
      have hne : j'.1 ≠ j.1 := fun h => hj' (Fin.ext h)
      rcases lt_or_gt_of_ne hne with h | h
      · have s := hsep j'.1 j.1 h hj
        have sq : (((2 * G - 1 : ℤ)) : ℚ) ≤ ((2 * (gapCentre D.R.m G bN j.1 - gapCentre D.R.m G bN j'.1) : ℤ) : ℚ) :=
          Int.cast_le.mpr s
        push_cast at sq
        rw [le_abs]
        left
        linarith
      · have s := hsep j.1 j'.1 h j'.isLt
        have sq : (((2 * G - 1 : ℤ)) : ℚ) ≤ ((2 * (gapCentre D.R.m G bN j'.1 - gapCentre D.R.m G bN j.1) : ℤ) : ℚ) :=
          Int.cast_le.mpr s
        push_cast at sq
        rw [le_abs]
        right
        linarith
  · apply noncompact_gaps_of_spacing _ ((G : ℤ) : ℚ)
    · dsimp only [towerOfIntegers]
      rw [hGq]
      linarith
    · intro τ i h0
      dsimp only [towerOfIntegers]
      have c : ((-bN 0 + 1 : ℤ) : ℚ) ≤ _ := Int.cast_le.mpr (hvb i)
      push_cast at c
      linarith
    · intro τ i i' hii'
      dsimp only [towerOfIntegers]
      exact_mod_cast hmono i.1 i'.1 hii' i'.isLt
    · intro τ i h
      dsimp only [towerOfIntegers]
      exact_mod_cast gapCentre_lt_succ hG2 bN hb i.1 h

def towerParamU {D : D7} (P : TPar D) (τ : D.what₂.Tau) : Fin D.R.k → ℝ := fun i => (P.u τ i : ℝ)

def towerParamV {D : D7} (P : TPar D) (τ : D.what₂.Tau) : Fin (D.R.k - 1) → ℝ := fun i => (P.v τ i : ℝ)

def towerParamB {D : D7} (P : TPar D) (τ : D.what₂.Tau) : Fin (2 * D.R.rS + 2) → ℝ :=
  fun j => (P.b τ (Fin.cast (two_rS_add_two_eq_m D) j) : ℝ)

theorem localParam_shift_v (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (i : Fin (k - 1))
    (h : i.1 < 2 * r + k + 1) : lam48 k r v b ⟨i.1, h⟩ = v i := by
  simp [lam48, i.isLt]

theorem localParam_shift_b (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) (j : Fin (2 * r + 2))
    (h : k - 1 + j.1 < 2 * r + k + 1) : lam48 k r v b ⟨k - 1 + j.1, h⟩ = -b j := by
  have hn : ¬ (k - 1 + j.1 < k - 1) := by omega
  simp [lam48, hn]

theorem halfInt_of_integrality (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (hu : Formalism.QuantumDeterminants.IsHCParam u) (hl : Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b)) : HalfIntegralDifference k r u v b := by
  intro i s
  obtain ⟨m1, e1⟩ := hu.2 i
  obtain ⟨m2, e2⟩ := hl.2 s
  refine ⟨m1 - m2 - r - 1, ?_⟩
  push_cast at e1 e2 ⊢
  linarith

theorem exists_tower_of_local_setting (D : D7) (X : ThetaX D) (z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ) (c : Fin D.R.rS → ℂ)
    (u : Fin D.R.k → ℝ) (v : Fin (D.R.k - 1) → ℝ) (b : Fin (2 * D.R.rS + 2) → ℝ)
    (hS : RealPlaceNumericalSetting D.R.k D.R.rS z c u v b) :
    ∃ P : TPar D, Hyp3 X P ∧ ∀ τ, towerParamU P τ = u ∧ towerParamV P τ = v ∧ towerParamB P τ = b := by
  obtain ⟨hk1, hke, hW, hT0, hc, hu, hl, hI, -, hGB⟩ := hS
  obtain ⟨K, hK⟩ := hke
  have hkR : (D.R.k : ℝ) = 2 * (K : ℝ) := by
    rw [hK]
    push_cast
    ring
  choose mu hmu using hu.2
  choose ml hml using hl.2
  have hL : ∀ s, lam48 D.R.k D.R.rS v b s = ((ml s : ℤ) : ℝ) + (D.R.rS : ℝ) + (K : ℝ) := by
    intro s
    have e := hml s
    push_cast at e
    linarith
  obtain ⟨uZ, huZ⟩ : ∃ uZ : Fin D.R.k → ℤ, ∀ i, u i = ((uZ i : ℤ) : ℝ) + 1 / 2 := by
    refine ⟨fun i => mu i + K - 1, fun i => ?_⟩
    have e := hmu i
    push_cast
    linarith
  obtain ⟨vZ, hvZ⟩ : ∃ vZ : Fin (D.R.k - 1) → ℤ, ∀ i, v i = ((vZ i : ℤ) : ℝ) := by
    refine ⟨fun i => ml ⟨i.1, by omega⟩ + D.R.rS + K, fun i => ?_⟩
    rw [← localParam_shift_v D.R.k D.R.rS v b i (by omega), hL]
    push_cast
    ring
  obtain ⟨bN, hbN⟩ : ∃ bN : ℕ → ℤ, ∀ n (h : n < 2 * D.R.rS + 2), b ⟨n, h⟩ = ((bN n : ℤ) : ℝ) := by
    refine ⟨fun n => if h : n < 2 * D.R.rS + 2 then -(ml ⟨D.R.k - 1 + n, by omega⟩ + D.R.rS + K) else 0,
      fun n h => ?_⟩
    have e := localParam_shift_b D.R.k D.R.rS v b ⟨n, h⟩ (by show D.R.k - 1 + n < 2 * D.R.rS + D.R.k + 1; omega)
    rw [hL] at e
    simp only [dif_pos h]
    push_cast
    linarith
  obtain ⟨t, ht1, ht2, ht3, hgap⟩ := hGB
  rw [localRank_eq_r D] at ht2 ht3
  have hmN := two_rS_add_two_eq_m D
  have huv : ∀ i : Fin (D.R.k - 1), vZ i ≤ uZ ⟨i.1, by omega⟩ ∧ uZ ⟨i.1 + 1, by omega⟩ < vZ i := by
    intro i
    obtain ⟨e1, e2⟩ := hI.1 i
    rw [hvZ, huZ] at e1
    rw [hvZ, huZ] at e2
    constructor
    · have c : ((vZ i : ℤ) : ℝ) < ((uZ ⟨i.1, by omega⟩ + 1 : ℤ) : ℝ) := by
        push_cast
        linarith
      exact Int.lt_add_one_iff.mp (Int.cast_lt.mp c)
    · have c : ((uZ ⟨i.1 + 1, by omega⟩ : ℤ) : ℝ) < ((vZ i : ℤ) : ℝ) := by linarith
      exact Int.cast_lt.mp c
  have hub : ∀ i, -bN 0 ≤ uZ i := by
    intro i
    have hk0 : 0 < D.R.k := by omega
    have e1 := hI.2 hk0
    have e2 : u ⟨D.R.k - 1, by omega⟩ ≤ u i :=
      hu.1.antitone (Fin.le_def.mpr (show i.1 ≤ D.R.k - 1 by omega))
    have e3 := hbN 0 (by omega)
    have e4 := huZ i
    have c : ((-bN 0 : ℤ) : ℝ) < ((uZ i + 1 : ℤ) : ℝ) := by
      push_cast
      linarith
    exact Int.lt_add_one_iff.mp (Int.cast_lt.mp c)
  have hb : ∀ i, i + 1 < D.R.m →
      2 * ((D.R.r + D.R.m * t : ℕ) : ℤ) ^ 3 + (t : ℤ) + 4 ≤ bN (i + 1) - bN i := by
    intro i hi
    have g1 := hgap ⟨i, by omega⟩ (by show i + 1 < 2 * D.R.rS + 2; omega)
    have e1 := hbN (i + 1) (by omega)
    have e2 := hbN i (by omega)
    rw [e1, e2, localRank_eq_r D, hmN] at g1
    have c : ((2 * ((D.R.r + D.R.m * t : ℕ) : ℤ) ^ 3 + (t : ℤ) + 3 : ℤ) : ℝ) < ((bN (i + 1) - bN i : ℤ) : ℝ) := by
      push_cast at g1 ⊢
      linarith
    have c' := Int.cast_lt.mp c
    linarith
  refine ⟨towerOfIntegers D X t ht1 ht2 uZ vZ bN (2 * ((D.R.r + D.R.m * t : ℕ) : ℤ) ^ 3 + (t : ℤ) + 4),
    tower_hyp_of_integer_params D X t ht1 ht2 ht3 uZ vZ bN huv hub hb, fun τ => ⟨?_, ?_, ?_⟩⟩
  · funext i
    show ((((uZ i : ℤ) : ℚ) + 1 / 2 : ℚ) : ℝ) = u i
    rw [huZ i]
    push_cast
    try ring
  · funext i
    show ((((vZ i : ℤ) : ℚ)) : ℝ) = v i
    rw [hvZ i]
    push_cast
    try rfl
  · funext j
    show ((((bN (Fin.cast (two_rS_add_two_eq_m D) j).1 : ℤ) : ℚ)) : ℝ) = b j
    rw [show b j = ((bN j.1 : ℤ) : ℝ) from hbN j.1 j.isLt]
    push_cast
    try rfl

def LocalOrderedSomeModel (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ) : Prop :=
  ∃ (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ), Formalism.QuantumDeterminants.inWb k r z ∧ 0 < Formalism.QuantumDeterminants.Tz k r z ∧ (∀ a, c a ≠ 0) ∧
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (σ : CayleySignature.Mat k r → (H →L[ℂ] H)), IsDSHpk k r (eps48 k r) (lam48 k r v b) σ ∧
    ∃ (Vp : Type) (_ : NormedAddCommGroup Vp) (_ : InnerProductSpace ℂ Vp) (_ : FiniteDimensional ℂ Vp)
      (π : CayleySignature.Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π ∧
    ∃ B : H → Vp, IsBesselMapSm z (psiGen k r z c) σ π B ∧ HasOrdLe k r (rk48 k r ^ 2 / 2 + 1) σ B ∧
      ∃ x ∈ smoothVecs (k := k) (r := r) σ, B x ≠ 0

def LocalTransport : Prop :=
  ∀ (k r : ℕ) (u : Fin k → ℝ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ), Formalism.QuantumDeterminants.IsHCParam u →
    Formalism.QuantumDeterminants.IsHCParam (lam48 k r v b) → LocalOrderedSomeModel k r u v b →
    ∀ (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → (∀ a, c a ≠ 0) →
      LocalOrderedConclusion k r z c u v b

def Step4 (D : D7) (X : ThetaX D) : Prop :=
  ∀ P : TPar D, Hyp3 X P →
  ∀ (π : Submodule ℂ (X.AF (X.Xs P.t 0))) (φ : X.AF (X.Xs P.t 0)) (F : X.cusp (X.Ys P.t 0))
    (pos : X.Pos (X.Xs P.t 0) (X.Ys P.t 0) (X.iXYs P.t 0)),
    IsAutRep X _ π → π ≤ X.typeX P 0 → φ ∈ π → IsDv X P 0 (F : X.AF (X.Ys P.t 0)) → bB X P.t 0 pos 0 φ F ≠ 0 →
    ∀ τ, LocalOrderedSomeModel D.R.k D.R.rS (towerParamU P τ) (towerParamV P τ) (towerParamB P τ)

theorem ordered_at_ranks_of_tower_hyp (D : D7) (X : ThetaX D) (C : ℝ) (h3 : PointsLemma D X) (h4 : Step4 D X) (hT : LocalTransport) :
    OrderedAtRanks D C := by
  intro z c u v b hS hG
  obtain ⟨P, hP, hPe⟩ := exists_tower_of_local_setting D X z c u v b hS
  obtain ⟨μ, π, φ, F, Φ, pos, -, hπ, hπle, hφ, -, hF, hB⟩ := h3 P hP
  have hm : 0 < D.R.m := by
    have := D.R.two_le_m
    omega
  have hDv := (hF 0 hm).2.2.2
  have τ : D.what₂.Tau := D.eTau.symm 1
  have hL := h4 P hP π φ (F 0) pos hπ hπle hφ hDv hB τ
  obtain ⟨e1, e2, e3⟩ := hPe τ
  rw [e1, e2, e3] at hL
  obtain ⟨-, -, hW, hT0, hc, hu, hl, -, -, -⟩ := hS
  exact hT _ _ u v b hu hl hL z c hW hT0 hc

def FamilyOrderedAtRanks {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) : Prop :=
  ∀ (x : ℝ) (_ : Fm.x1 < x) (i : Fm.Ix x), OrderedAtRanks (Fm.D x i) C

def Step4F {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Step4 (Fm.D x i) (Fm.ex x hx i).th

end Formalism.MainNotions.LeviCoordinates

end
