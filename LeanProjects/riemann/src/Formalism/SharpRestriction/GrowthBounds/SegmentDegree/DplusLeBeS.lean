import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.PsiCutSupported

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Gen6

variable {N r : ℕ}

theorem stg_castSucc (ν : Fin (N + 1) → Fin r → ℤ) (l : Fin N) : ν l.castSucc = stg ν l.val := by
  unfold stg
  rw [dif_pos (by have := l.isLt; omega)]
  rfl

theorem stg_succ (ν : Fin (N + 1) → Fin r → ℤ) (l : Fin N) : ν l.succ = stg ν (l.val + 1) := by
  unfold stg
  rw [dif_pos (by have := l.isLt; omega)]
  rfl

theorem stg_plPart {K : ℕ} (μ : Fin (N + 1) → Fin (r + K) → ℤ) (i : ℕ) (m : Fin r) :
    stg (plPart μ) i m = stg μ i (Fin.castAdd K m) := by
  unfold stg
  split_ifs <;> rfl

theorem colH_step {ν ν' : Fin r → ℤ} (hν : Antitone ν) (hν' : Antitone ν') (ha : ∀ a, ν a ≤ ν' a)
    (hb : ∀ (a : Fin r) (h : a.val + 1 < r), ν' ⟨a.val + 1, h⟩ ≤ ν a) (c : ℤ) :
    colH ν c ≤ colH ν' c ∧ colH ν' c ≤ colH ν c + 1 := by
  constructor
  · unfold colH
    apply Finset.card_le_card
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    exact le_trans hm (ha m)
  · unfold colH
    set S := Finset.univ.filter fun m => c ≤ ν m with hS
    set S' := Finset.univ.filter fun m => c ≤ ν' m with hS'
    have hsub : S'.image Fin.val ⊆ insert 0 (S.image fun a => a.val + 1) := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, S', S, Finset.mem_insert] at hx ⊢
      obtain ⟨m, hm, rfl⟩ := hx
      rcases Nat.eq_zero_or_pos m.val with h0 | hpos
      · left
        exact h0
      · right
        have hlt : m.val - 1 < r := by omega
        have h1 : (m.val - 1) + 1 < r := by omega
        have hm' : (⟨(m.val - 1) + 1, h1⟩ : Fin r) = m := Fin.ext (by simp; omega)
        refine ⟨⟨m.val - 1, hlt⟩, ?_, by simp; omega⟩
        have h2 := hb ⟨m.val - 1, hlt⟩ h1
        rw [hm'] at h2
        exact le_trans hm h2
    calc S'.card = (S'.image Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ ≤ (insert 0 (S.image fun a => a.val + 1)).card := Finset.card_le_card hsub
      _ ≤ (S.image fun a => a.val + 1).card + 1 := Finset.card_insert_le _ _
      _ ≤ S.card + 1 := by
        have := Finset.card_image_le (s := S) (f := fun a : Fin r => a.val + 1)
        omega

theorem cut_ppath {LL : Letters (Fin N)} {b' : Fin N → ℕ} (P1 : PPath r N LL b') (n0 : ℕ) :
    ∃ bc, ∃ Pc : PPath r N LL bc, Pc.mu = cutPath n0 P1.mu := by
  classical
  have hdom : ∀ k, k < N + 1 → Antitone (stg P1.mu k) := by
    intro k hk
    rw [← stg_eq P1.mu k hk]; exact P1.dom _
  refine ⟨fun i => if i.val < n0 then b' i else 0, ⟨cutPath n0 P1.mu, ?_, ?_, ?_⟩, rfl⟩
  · show stg P1.mu (min (0 : Fin (N + 1)).val n0) = 0
    simp only [Fin.val_zero, Nat.zero_min]
    rw [← stg_eq P1.mu 0 (by omega)]
    exact P1.zero
  · intro i
    exact hdom _ (lt_of_le_of_lt (min_le_left _ _) i.isLt)
  · intro i
    have hi := i.isLt
    by_cases h : i.val < n0
    · have e1 : cutPath n0 P1.mu i.castSucc = P1.mu i.castSucc := by
        show stg P1.mu (min i.val n0) = _
        rw [min_eq_left (by omega), stg_castSucc P1.mu]
      have e2 : cutPath n0 P1.mu i.succ = P1.mu i.succ := by
        show stg P1.mu (min (i.val + 1) n0) = _
        rw [min_eq_left (by omega), stg_succ P1.mu]
      rw [e1, e2]
      simp only [h, if_true]
      exact P1.step i
    · have e1 : cutPath n0 P1.mu i.castSucc = stg P1.mu n0 := by
        show stg P1.mu (min i.val n0) = _
        rw [min_eq_right (by omega)]
      have e2 : cutPath n0 P1.mu i.succ = stg P1.mu n0 := by
        show stg P1.mu (min (i.val + 1) n0) = _
        rw [min_eq_right (by omega)]
      rw [e1, e2]
      simp only [h, if_false]
      have hs : HStrip (stg P1.mu n0) (stg P1.mu n0) 0 :=
        ⟨fun _ => le_rfl, fun a h' => hdom n0 (by omega) (by rw [Fin.le_def]; simp), by simp⟩
      split_ifs <;> exact hs

theorem joinPT_parts {K : ℕ} (μ : Fin (N + 1) → Fin (r + K) → ℤ) : joinPT (plPart μ) (tanPart μ) = μ := by
  funext i
  exact Fin.append_castAdd_natAdd

end Gen6

section Dat6

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

theorem dplus_le_beS (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) (hP : X.IsPATH p K j b μ dd) (s : ℕ) (hs : s ≤ segN X.F j - r) :
    T.dplus (segLL X.F j) dd s ≤ X.beS p K j b := by
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  unfold T.dplus Dat.beS
  have himg : (X.F.letters j).filter (· < X.F.fr j 0) =
      (Finset.univ.filter fun l : Fin (segN X.F j) => l.val < segN X.F j - r).image (segE X.F j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨i, rfl⟩ := segE_surj X.F j hx
      exact ⟨i, (segE_lt_fr_iff X.F hV hr j i).mp hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨segE_mem X.F j i, (segE_lt_fr_iff X.F hV hr j i).mpr hi⟩
  rw [himg, Finset.sum_image (fun a _ b _ h => (segE_strictMono X.F j).injective h), Finset.sum_filter]
  refine Finset.sum_le_sum fun l _ => ?_
  split_ifs with h1 h2 h2
  · rw [hP.degs l ((segE_lt_fr_iff X.F hV hr j l).mpr h2)]
  · omega
  · exact Nat.zero_le _
  · exact le_rfl

theorem plHyp_of (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) (hP : X.IsPATH p K j b μ dd) :
    PlHyp (segN X.F j - r) (X.beS p K j b : ℤ) (plPart μ) := by
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  obtain ⟨P, hPμ⟩ := hP.path
  have hrN : r ≤ segN X.F j := k_r_le_segN X.F hV hr j
  have hNK : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK

  have htau : ∀ t (ht : t < r), ∃ l : Fin (segN X.F j), l.val = segN X.F j - r + t ∧
      segE X.F j l = X.F.fr j t ∧ HStrip (stg μ (segN X.F j - r + t)) (stg μ (segN X.F j - r + t + 1)) (dd l) := by
    intro t ht
    let l : Fin (segN X.F j) := ⟨segN X.F j - r + t, by omega⟩
    have hl : segE X.F j l = X.F.fr j t := (segE_eq_fr_iff X.F hV j l ht).mpr rfl
    have hvec : (segLL X.F j).vec l = true := by
      rw [comb_vec, hl]; exact (hV.2.2.2.2.1 j t ht).2
    have hs := T.step_vec P l hvec
    rw [hPμ, stg_castSucc μ, stg_succ μ] at hs
    exact ⟨l, rfl, hl, hs⟩
  have hlow : ∀ i ≤ segN X.F j - r, ∀ m, stg μ i m ≤ (X.beS p K j b : ℤ) := by
    intro i hi m
    have h1 := T.mu_le_dplus P i (by omega) m
    rw [hPμ, stg_eq μ i (by omega)] at h1
    have h2 := dplus_le_beS X p K hX j b μ dd hP i hi
    exact le_trans h1 (by exact_mod_cast h2)
  have hup : ∀ t ≤ r, ∀ m, stg μ (segN X.F j - r + t) m ≤ (X.beS p K j b : ℤ) := by
    intro t
    induction t with
    | zero => intro _ m; exact hlow _ le_rfl m
    | succ t ih =>
      intro ht m
      obtain ⟨l, hlv, hl, hs⟩ := htau t (by omega)
      rw [show segN X.F j - r + (t + 1) = segN X.F j - r + t + 1 by ring]
      by_cases hm : m.val = 0
      · have := hP.head l ⟨t, by omega⟩ hl m (by omega)
        rw [stg_succ μ, hlv] at this
        rw [this]
      · have hm' := m.isLt
        have h2 := hs.2.1 ⟨m.val - 1, by omega⟩ (by simp only []; omega)
        have e : (⟨(⟨m.val - 1, by omega⟩ : Fin (r + K)).val + 1, by simp only []; omega⟩ : Fin (r + K)) = m :=
          Fin.ext (by simp only []; omega)
        rw [e] at h2
        exact le_trans h2 (ih (by omega) _)
  have hdom : ∀ k, k < segN X.F j + 1 → Antitone (stg (plPart μ) k) := by
    intro k hk a a' haa
    rw [stg_plPart, stg_plPart, ← stg_eq μ k hk, ← hPμ]
    exact P.dom _ (by rw [Fin.le_def]; simpa using haa)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi m
    rw [stg_plPart]
    constructor
    · have h1 := T.mu_nonneg P i (by omega) (Fin.castAdd K m) (by
        have := m.isLt
        simp only [Fin.val_castAdd]; omega)
      rwa [hPμ, stg_eq μ i (by omega)] at h1
    · by_cases h : i ≤ segN X.F j - r
      · exact hlow i h _
      · have := hup (i - (segN X.F j - r)) (by omega) (Fin.castAdd K m)
        rwa [show segN X.F j - r + (i - (segN X.F j - r)) = i by omega] at this
  · intro m
    rw [stg_plPart]
    obtain ⟨l, hlv, hl, -⟩ := htau (r - 1) (by omega)
    have := hP.head l ⟨r - 1, by omega⟩ hl (Fin.castAdd K m) (by
      have := m.isLt
      simp only [Fin.val_castAdd]; omega)
    rw [stg_succ μ, hlv, show segN X.F j - r + (r - 1) + 1 = segN X.F j by omega] at this
    exact this
  · intro t ht c
    obtain ⟨l, hlv, hl, hs⟩ := htau t ht
    refine colH_step (hdom _ (by omega)) (hdom _ (by omega)) ?_ ?_ c
    · intro a
      rw [stg_plPart, stg_plPart]
      exact hs.1 _
    · intro a h
      rw [stg_plPart, stg_plPart]
      have := hs.2.1 (Fin.castAdd K a) (by simp only [Fin.val_castAdd]; omega)
      exact this

end Dat6

end Formalism.MainNotions.SelectionLemmas.Pf
