import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KLettersDegEven

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Function

variable {s r : ℕ}

def jE (S : SegData s) (jl : Fin S.t → ℕ) (i : ℕ) : ℕ :=
  if h : S.sigma ≤ i ∧ i < s then jl ⟨i - S.sigma, by unfold SegData.t; omega⟩ else 0

theorem tieSum (S : SegData s) (jl : Fin S.t → ℕ) (a : ℕ) :
    (∑ l : Fin S.t, if a = 2 * (S.sigma + l.val) ∨ a = 2 * (S.sigma + l.val) + 1 then jl l else 0) =
      jE S jl (a / 2) := by
  have key : ∀ l : Fin S.t, (a = 2 * (S.sigma + l.val) ∨ a = 2 * (S.sigma + l.val) + 1) ↔
      a / 2 = S.sigma + l.val := by
    intro l
    constructor
    · intro h
      omega
    · intro h
      omega
  simp only [key]
  unfold jE
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    rw [Finset.sum_eq_single (⟨a / 2 - S.sigma, by unfold SegData.t; omega⟩ : Fin S.t)]
    · rw [if_pos (show a / 2 = S.sigma + (a / 2 - S.sigma) by omega)]
    · intro l _ hl
      rw [if_neg]
      intro h'
      apply hl
      apply Fin.ext
      show l.val = a / 2 - S.sigma
      omega
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · apply Finset.sum_eq_zero
    intro l _
    rw [if_neg]
    intro h'
    have hl := l.2
    unfold SegData.t at hl
    exact h ⟨by omega, by omega⟩

theorem lev_deg (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r)
    (jl : Fin S.t → ℕ) (jp : ℕ) (a : Fin (2 * s + 1)) :
    ((blockData p S aTop aPlus m b).lettersAt jl jp).deg a =
      (segChain p S aTop b).deg a - jE S jl (a.val / 2) - (if a.val = 2 * s then jp else 0) := by
  have e1 := tieSum S jl a.val
  have e2 : (if a = (⟨2 * s, by omega⟩ : Fin (2 * s + 1)) then jp else 0) = (if a.val = 2 * s then jp else 0) := by
    by_cases h : a.val = 2 * s
    · rw [if_pos (Fin.ext h), if_pos h]
    · rw [if_neg (fun h' => h (congrArg Fin.val h')), if_neg h]
  show (segChain p S aTop b).deg a -
      (∑ l : Fin S.t, if a.val = 2 * (S.sigma + l.val) ∨ a.val = 2 * (S.sigma + l.val) + 1 then jl l else 0) -
      (if a = (⟨2 * s, by omega⟩ : Fin (2 * s + 1)) then jp else 0) = _
  rw [e1, e2]

theorem segment_chain_degree_even (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (b : SegBlock s r) (x : Fin (2 * s + 1)) (i : Fin s)
    (hx : x.val = 2 * i.val) : (segChain p S aTop b).deg x = if i.val < S.sigma then b.w i else b.o i := by
  have h1 : (x : ℕ) ≠ 2 * s := by have := i.2; omega
  have h2 : (x : ℕ) % 2 = 0 := by omega
  have h3 : topOf x h1 = i := Fin.ext (by show (x : ℕ) / 2 = i.val; omega)
  unfold segChain
  dsimp only
  rw [dif_neg h1, if_pos h2, h3]

theorem chain_deg_E (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (b : SegBlock s r) (x : Fin (2 * s + 1)) (i : Fin s)
    (hx : x.val = 2 * i.val + 1) : (segChain p S aTop b).deg x =
      if i.val < S.sigma then coarseC p S aTop b i - b.sg i else coarseC p S aTop b i := by
  have h1 : (x : ℕ) ≠ 2 * s := by have := i.2; omega
  have h2 : ¬ ((x : ℕ) % 2 = 0) := by omega
  have h3 : topOf x h1 = i := Fin.ext (by show (x : ℕ) / 2 = i.val; omega)
  unfold segChain
  dsimp only
  rw [dif_neg h1, if_neg h2, h3]

theorem chain_deg_U (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (b : SegBlock s r) (x : Fin (2 * s + 1))
    (hx : x.val = 2 * s) : (segChain p S aTop b).deg x = b.oPlus := by
  unfold segChain
  dsimp only
  rw [dif_pos hx]

theorem jE_S (S : SegData s) (jl : Fin S.t → ℕ) {i : ℕ} (h : i < S.sigma) : jE S jl i = 0 := by
  unfold jE
  split_ifs with h1
  · exact absurd h1.1 (by omega)
  · rfl

theorem jE_top (S : SegData s) (jl : Fin S.t → ℕ) : jE S jl s = 0 := by
  unfold jE
  split_ifs with h1
  · exact absurd h1.2 (lt_irrefl _)
  · rfl

theorem level_bounds (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r)
    (jl : Fin S.t → ℕ) (jp : ℕ) (h : (blockData p S aTop aPlus m b).LevelOK jl jp) :
    (∀ i : Fin s, S.sigma ≤ i.val → jE S jl i.val ≤ b.o i ∧ jE S jl i.val ≤ coarseC p S aTop b i) ∧ jp ≤ b.oPlus := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun i hi => ?_, ?_⟩
  · have hit : i.val - S.sigma < S.t := by unfold SegData.t; have := i.2; omega
    have hl := h1 ⟨i.val - S.sigma, hit⟩
    have eA : jE S jl i.val = jl ⟨i.val - S.sigma, hit⟩ := by
      unfold jE
      rw [dif_pos ⟨hi, i.2⟩]
    have k1 : (blockData p S aTop aPlus m b).LL.deg ((blockData p S aTop aPlus m b).letterAt
        ((blockData p S aTop aPlus m b).T.pos ⟨i.val - S.sigma, hit⟩)) = b.o i := by
      have e : (blockData p S aTop aPlus m b).letterAt ((blockData p S aTop aPlus m b).T.pos
          ⟨i.val - S.sigma, hit⟩) = ⟨2 * i.val, by omega⟩ := by
        apply Fin.ext
        show min (2 * (S.sigma + (i.val - S.sigma))) (2 * s + 1 - 1) = 2 * i.val
        omega
      rw [e]
      exact (segment_chain_degree_even p S aTop b ⟨2 * i.val, by omega⟩ i rfl).trans (if_neg (by omega))
    have k2 : (blockData p S aTop aPlus m b).LL.deg ((blockData p S aTop aPlus m b).letterAt
        ((blockData p S aTop aPlus m b).T.pos ⟨i.val - S.sigma, hit⟩ + 1)) = coarseC p S aTop b i := by
      have e : (blockData p S aTop aPlus m b).letterAt ((blockData p S aTop aPlus m b).T.pos
          ⟨i.val - S.sigma, hit⟩ + 1) = ⟨2 * i.val + 1, by omega⟩ := by
        apply Fin.ext
        show min (2 * (S.sigma + (i.val - S.sigma)) + 1) (2 * s + 1 - 1) = 2 * i.val + 1
        omega
      rw [e]
      exact (chain_deg_E p S aTop b ⟨2 * i.val + 1, by omega⟩ i rfl).trans (if_neg (by omega))
    rw [eA]
    exact ⟨hl.1.trans (le_of_eq k1), hl.2.trans (le_of_eq k2)⟩
  · exact h2.trans ((min_le_left _ _).trans (le_of_eq (chain_deg_U p S aTop b ⟨2 * s, by omega⟩ rfl)))

theorem cap_zero (p : ℕ) (S : SegData s) (b : SegBlock s r) : cap p S b 0 = S.A0 p := by
  simp [cap]

theorem cap_succ (p : ℕ) (S : SegData s) (b : SegBlock s r) (i : Fin s) :
    cap p S b (i.val + 1) = cap p S b i.val + ((coarseA p S b i : ℤ) - (oEff S b i : ℤ)) := by
  unfold cap
  have key : ∀ k : Fin s, (if (k : ℕ) < i.val + 1 then ((coarseA p S b k : ℤ) - (oEff S b k : ℤ)) else 0) =
      (if (k : ℕ) < i.val then ((coarseA p S b k : ℤ) - (oEff S b k : ℤ)) else 0) +
        (if k = i then ((coarseA p S b k : ℤ) - (oEff S b k : ℤ)) else 0) := by
    intro k
    by_cases h1 : (k : ℕ) < i.val
    · have h2 : k ≠ i := fun h => by rw [h] at h1; exact lt_irrefl _ h1
      rw [if_pos (show (k : ℕ) < i.val + 1 by omega), if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : k = i
      · subst h2
        rw [if_pos (show (k : ℕ) < k.val + 1 by omega), if_neg h1, if_pos rfl, zero_add]
      · have h3 : ¬ (k : ℕ) < i.val + 1 := fun h => h2 (Fin.ext (by omega))
        rw [if_neg h3, if_neg h1, if_neg h2, add_zero]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  ring

theorem levW (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r)
    (jl : Fin S.t → ℕ) (jp : ℕ) (i : Fin s) :
    ((blockData p S aTop aPlus m b).lettersAt jl jp).deg ⟨2 * i.val, by omega⟩ =
      (if i.val < S.sigma then b.w i else b.o i) - jE S jl i.val := by
  rw [lev_deg, segment_chain_degree_even p S aTop b ⟨2 * i.val, by omega⟩ i rfl]
  have h1 : (⟨2 * i.val, by omega⟩ : Fin (2 * s + 1)).val / 2 = i.val := by
    show 2 * i.val / 2 = i.val
    omega
  have h2 : ¬ ((⟨2 * i.val, by omega⟩ : Fin (2 * s + 1)).val = 2 * s) := by
    show ¬ (2 * i.val = 2 * s)
    have := i.2
    omega
  rw [h1, if_neg h2, Nat.sub_zero]

theorem levE (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r)
    (jl : Fin S.t → ℕ) (jp : ℕ) (i : Fin s) :
    ((blockData p S aTop aPlus m b).lettersAt jl jp).deg ⟨2 * i.val + 1, by omega⟩ =
      (if i.val < S.sigma then coarseC p S aTop b i - b.sg i else coarseC p S aTop b i) - jE S jl i.val := by
  rw [lev_deg, chain_deg_E p S aTop b ⟨2 * i.val + 1, by omega⟩ i rfl]
  have h1 : (⟨2 * i.val + 1, by omega⟩ : Fin (2 * s + 1)).val / 2 = i.val := by
    show (2 * i.val + 1) / 2 = i.val
    omega
  have h2 : ¬ ((⟨2 * i.val + 1, by omega⟩ : Fin (2 * s + 1)).val = 2 * s) := by
    show ¬ (2 * i.val + 1 = 2 * s)
    omega
  rw [h1, if_neg h2, Nat.sub_zero]

theorem levU (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r)
    (jl : Fin S.t → ℕ) (jp : ℕ) :
    ((blockData p S aTop aPlus m b).lettersAt jl jp).deg ⟨2 * s, by omega⟩ = b.oPlus - jp := by
  rw [lev_deg, chain_deg_U p S aTop b ⟨2 * s, by omega⟩ rfl]
  have h1 : (⟨2 * s, by omega⟩ : Fin (2 * s + 1)).val / 2 = s := by
    show 2 * s / 2 = s
    omega
  have h2 : (⟨2 * s, by omega⟩ : Fin (2 * s + 1)).val = 2 * s := rfl
  rw [h1, if_pos h2, jE_top, Nat.sub_zero]

theorem jE_at (S : SegData s) (jl : Fin S.t → ℕ) (l : Fin S.t) : jE S jl (S.sigma + l.val) = jl l := by
  have hl := l.2
  unfold SegData.t at hl
  unfold jE
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1
  apply Fin.ext
  show S.sigma + l.val - S.sigma = l.val
  omega

theorem segBlock_ext (b b' : SegBlock s r) (h1 : b.rz = b'.rz) (h2 : b.ry = b'.ry) (h3 : b.o = b'.o) (h4 : b.w = b'.w)
    (h5 : b.sg = b'.sg) (h6 : b.oPlus = b'.oPlus) : b = b' := by
  cases b
  cases b'
  dsimp only at h1 h2 h3 h4 h5 h6
  subst h1 h2 h3 h4 h5 h6
  rfl

private theorem chainLetters_deg_eq_of_vec_eq_of_isChain {N r : ℕ} (L L' : ChainLetters N) (ka : Fin (N + 1) → Fin r → ℤ)
    (hv : L.vec = L'.vec) (h : IsChain L ka) (h' : IsChain L' ka) (a : Fin N) : L.deg a = L'.deg a := by
  have e := h.2 a
  have e' := h'.2 a
  rw [hv] at e
  by_cases hva : L'.vec a = true
  · rw [if_pos hva] at e e'
    have q := e.2.2
    have q' := e'.2.2
    omega
  · rw [if_neg hva] at e e'
    have q := e.2.2
    have q' := e'.2.2
    omega

theorem srcInjAt : SrcInjAt := by
  intro C0 CE1 CE2 X _ j m rz ry z z' hz hz' hka hjp
  obtain ⟨b, ⟨jl, jp⟩, ka⟩ := z
  obtain ⟨b', ⟨jl', jp'⟩, ka'⟩ := z'
  dsimp only at hka hjp
  subst hka hjp
  obtain ⟨⟨hK, hrz, hry⟩, hL, hch, -⟩ := hz
  obtain ⟨⟨hK', hrz', hry'⟩, hL', hch', -⟩ := hz'
  dsimp only at hK hrz hry hL hch hK' hrz' hry' hL' hch'
  have hdeg : ∀ a, ((BD C0 CE1 CE2 X j m b).lettersAt jl jp).deg a = ((BD C0 CE1 CE2 X j m b').lettersAt jl' jp).deg a := by
    intro a
    have h1 := hch.2 a
    have h2 := hch'.2 a
    by_cases hv : ((BD C0 CE1 CE2 X j m b).lettersAt jl jp).vec a = true
    · have hv' : ((BD C0 CE1 CE2 X j m b').lettersAt jl' jp).vec a = true := hv
      rw [if_pos hv] at h1
      rw [if_pos hv'] at h2
      exact_mod_cast h1.2.2.symm.trans h2.2.2
    · have hv' : ¬ ((BD C0 CE1 CE2 X j m b').lettersAt jl' jp).vec a = true := hv
      rw [if_neg hv] at h1
      rw [if_neg hv'] at h2
      exact_mod_cast h1.2.2.symm.trans h2.2.2
  have hC : ∀ i, coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i =
      coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b' i := fun i => by
    unfold coarseC
    rw [hry, hry']
  have hB := level_bounds _ _ _ _ _ _ _ _ hL
  have hB' := level_bounds _ _ _ _ _ _ _ _ hL'
  have key : ∀ i : Fin (segS X.TT j), b.o i = b'.o i ∧ b.w i = b'.w i ∧ b.sg i = b'.sg i ∧
      jE (X.seg C0 CE1 CE2 j) jl i.val = jE (X.seg C0 CE1 CE2 j) jl' i.val := by
    intro i
    have dW := hdeg ⟨2 * i.val, by omega⟩
    have dE := hdeg ⟨2 * i.val + 1, by omega⟩
    rw [levW, levW] at dW
    rw [levE, levE] at dE
    have hCi := hC i
    rcases Nat.lt_or_ge i.val (X.seg C0 CE1 CE2 j).sigma with h | h
    · obtain ⟨ho, -, hsg, -, -⟩ := hK.2.2.1 i h
      obtain ⟨ho', -, hsg', -, -⟩ := hK'.2.2.1 i h
      rw [if_pos h, if_pos h, jE_S _ _ h, jE_S _ _ h] at dW dE
      rw [jE_S _ _ h, jE_S _ _ h]
      refine ⟨by omega, by omega, by omega, rfl⟩
    · obtain ⟨-, -, hw, hsg⟩ := hK.2.1 i h
      obtain ⟨-, -, hw', hsg'⟩ := hK'.2.1 i h
      have b1 := hB.1 i h
      have b2 := hB'.1 i h
      rw [if_neg (by omega), if_neg (by omega)] at dW dE
      refine ⟨by omega, by omega, by omega, by omega⟩
  have hU := hdeg ⟨2 * segS X.TT j, by omega⟩
  rw [levU, levU] at hU
  have hbb : b = b' := segBlock_ext b b' (hrz.trans hrz'.symm) (hry.trans hry'.symm) (funext fun i => (key i).1)
    (funext fun i => (key i).2.1) (funext fun i => (key i).2.2.1) (by have := hB.2; have := hB'.2; omega)
  have hjl : jl = jl' := by
    funext l
    have hl : l.val < segS X.TT j - (X.seg C0 CE1 CE2 j).sigma := l.2
    have := (key ⟨(X.seg C0 CE1 CE2 j).sigma + l.val, by omega⟩).2.2.2
    rw [jE_at, jE_at] at this
    exact this
  rw [hbb, hjl]

def FirstRowsAt (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (m : ℝ), 0 ≤ m →
    ∀ rz ry : Fin (segS X.TT j) → Fin (X.m + 1) → ℕ,
      DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) →
      ∀ z, SrcOK C0 CE1 CE2 X j m rz ry z →
        (∀ (i : Fin (segS X.TT j)) (c : Fin X.m), c.val = 0 →
          z.2.2 ⟨2 * i.val + 1, by omega⟩ c ≤ cap X.p (X.seg C0 CE1 CE2 j) z.1 i.val ∧
          z.2.2 ⟨2 * i.val + 1, by omega⟩ c ≤ cap X.p (X.seg C0 CE1 CE2 j) z.1 (i.val + 1)) ∧
        ∀ c : Fin X.m, c.val = 0 → z.2.2 (Fin.last _) c ≤ cap X.p (X.seg C0 CE1 CE2 j) z.1 (segS X.TT j)

theorem levFactsAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc H : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 H X)
    (hR : FirstRowsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : LevFactsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  unfold LevFactsAt
  intro X _ hD hI hc j m hm rz ry hdig z hz
  have hrows := hR X hD hI hc j m hm rz ry hdig z hz
  obtain ⟨b, ⟨jl, jp⟩, ka⟩ := z
  obtain ⟨⟨hK, hrz, hry⟩, hlev, hch, -⟩ := hz
  dsimp only at hrows hK hrz hry hlev hch ⊢
  have hA : ∀ i, coarseA X.p (X.seg C0 CE1 CE2 j) (digitBlock rz ry) i = coarseA X.p (X.seg C0 CE1 CE2 j) b i := by
    intro i
    rw [← hrz]
    rfl
  have hC : ∀ i, coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (digitBlock rz ry) i =
      coarseC X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b i := by
    intro i
    rw [← hry]
    rfl
  have hL := level_bounds X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) m b jl jp hlev
  refine ⟨cap_zero X.p (X.seg C0 CE1 CE2 j) b, ?_, fun a => rfl, fun i => ?_, fun i => ?_, fun i => ?_,
    fun i c hc0 => (hrows.1 i c hc0).1, fun i c hc0 => (hrows.1 i c hc0).2, hrows.2⟩
  · rw [← cap_zero X.p (X.seg C0 CE1 CE2 j) b]
    obtain ⟨hk0, hst⟩ := hch
    have e := hst ⟨0, by omega⟩
    rw [if_pos (show ((BD C0 CE1 CE2 X j m b).lettersAt jl jp).vec ⟨0, by omega⟩ = true from rfl)] at e
    have c0 : (0 : Fin X.m).val = 0 := by simp
    have e1 := e.1 0
    have e0 : Fin.castSucc (⟨0, by omega⟩ : Fin (2 * segS X.TT j + 1)) = 0 := Fin.ext (by simp)
    rw [e0, hk0] at e1
    simp only [Pi.zero_apply] at e1
    have e2 : ka (Fin.succ ⟨0, by omega⟩) 0 ≤ cap X.p (X.seg C0 CE1 CE2 j) b 0 := by
      rcases Nat.eq_zero_or_pos (segS X.TT j) with hs | hs
      · have h3 := hrows.2 0 c0
        have e3 : Fin.last (2 * segS X.TT j + 1) = Fin.succ ⟨0, by omega⟩ :=
          Fin.ext (by show 2 * segS X.TT j + 1 = 1; omega)
        rw [e3, congrArg (cap X.p (X.seg C0 CE1 CE2 j) b) hs] at h3
        exact h3
      · exact (hrows.1 ⟨0, hs⟩ 0 c0).1
    exact le_trans e1 e2
  · rw [hA i, levW]
    have key : (if i.val < (X.seg C0 CE1 CE2 j).sigma then b.w i else b.o i) ≤
        coarseA X.p (X.seg C0 CE1 CE2 j) b i := by
      split_ifs with hi
      · exact (hK.2.2.1 i hi).2.1
      · exact (hK.2.1 i (by omega)).1
    have := Nat.sub_le (if i.val < (X.seg C0 CE1 CE2 j).sigma then b.w i else b.o i)
      (jE (X.seg C0 CE1 CE2 j) jl i.val)
    exact_mod_cast this.trans key
  · rw [hA i, cap_succ, levW]
    have key : (if i.val < (X.seg C0 CE1 CE2 j).sigma then b.w i else b.o i) - jE (X.seg C0 CE1 CE2 j) jl i.val ≤
        oEff (X.seg C0 CE1 CE2 j) b i := by
      unfold oEff
      split_ifs <;> omega
    omega
  · rw [hA i, hC i, cap_succ, levW, levE]
    unfold oEff
    by_cases hi : i.val < (X.seg C0 CE1 CE2 j).sigma
    · have h1 := (hK.2.2.1 i hi).2.2.1
      have h2 := jE_S (X.seg C0 CE1 CE2 j) jl hi
      simp only [hi, ↓reduceIte]
      omega
    · obtain ⟨h1, h1'⟩ := hL.1 i (by omega)
      simp only [hi, ↓reduceIte]
      omega

def RestFirstRows : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => FirstRowsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem restMatchUp_of (hR : RestFirstRows) : RestMatchUp := by
  unfold RestFirstRows TransportedAlt at hR
  unfold RestMatchUp TransportedAlt
  intro Cc hCc
  obtain ⟨U0, hU0, hR0⟩ := hR Cc hCc
  refine ⟨max U0 1, lt_max_of_lt_right one_pos, fun C0 hC0 => ?_⟩
  obtain ⟨U1, hU1, hR1⟩ := hR0 C0 (le_trans (le_max_left _ _) hC0)
  refine ⟨max U1 1, lt_max_of_lt_right one_pos, fun CE1 CE2 Cm h1 h2 h3 => ?_⟩
  obtain ⟨U2, hU2, hR2⟩ := hR1 CE1 CE2 Cm (le_trans (le_max_left _ _) h1) (le_trans (le_max_left _ _) h2)
    (le_trans (le_max_left _ _) h3)
  refine ⟨max U2 (T2 CE1 CE2 Cc 1), lt_max_of_lt_left hU2, fun CYb Cde Ck CD Cb t1 t2 t3 t4 t5 => ?_⟩
  have hrows := hR2 CYb Cde Ck CD Cb (le_trans (le_max_left _ _) t1) (le_trans (le_max_left _ _) t2)
    (le_trans (le_max_left _ _) t3) (le_trans (le_max_left _ _) t4) (le_trans (le_max_left _ _) t5)
  exact matchUp_of (levFactsAt_of (H := 1) (fun X hD hI hc => std_of hCc (le_trans (le_max_right _ _) hC0)
    (le_trans (le_max_right _ _) h1) (le_trans (le_max_right _ _) h2) le_rfl
    (le_trans (le_max_right _ _) t1) (le_trans (le_max_right _ _) t2) (le_trans (le_max_right _ _) t3)
    (le_trans (le_max_right _ _) t4) (le_trans (le_max_right _ _) t5) hD hI hc) hrows) srcInjAt

theorem restCountUp_of_rows (hCD : ChainDimAt) (hNB : NumBranchAt) (hR : RestFirstRows) : RestCountUp := restCountUp_of hCD hNB (restMatchUp_of hR)

end Formalism.MainNotions.ColumnSystems.Pf
