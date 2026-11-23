import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ExponentMatrixFirstDepthEq

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Hyp

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestTMSize : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ a ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl a,
    (∀ i, (XMof C0 CE1 CE2 X dl a x.1 x.2).T.S ((XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies
        (XMof C0 CE1 CE2 X dl a x.1 x.2).T (XMof C0 CE1 CE2 X dl a x.1 x.2).top) i ≤
      (XMof C0 CE1 CE2 X dl a x.1 x.2).n₀ i) ∧
    (∀ y, ((XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies (XMof C0 CE1 CE2 X dl a x.1 x.2).T
        (XMof C0 CE1 CE2 X dl a x.1 x.2).top).deg y ≤ 2 * X.L.a) ∧
    (∀ i, (XMof C0 CE1 CE2 X dl a x.1 x.2).T.z i ≤ 2 * X.L.a) ∧
    (∑ y, ((XMof C0 CE1 CE2 X dl a x.1 x.2).LL.setTies (XMof C0 CE1 CE2 X dl a x.1 x.2).T
        (XMof C0 CE1 CE2 X dl a x.1 x.2).top).deg y) ≤ 8 * X.L.a ∧
    1 ≤ X.L.a

variable {C0 CE1 CE2 X}

theorem lgA_ge_one (p a r : ℕ) (hp : 1 < p) (hr : 1 ≤ r) : 1 ≤ lgA p a r := by
  unfold lgA
  have : 0 ≤ Real.logb p (8 * a + r) := by
    apply Real.logb_nonneg (by exact_mod_cast hp)
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg _
    linarith
  linarith

theorem r_ge_two {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : 2 ≤ X.r := by
  have h := hH.1.2.2.2.2.2.2.1
  have h1 := hH.1.2.2.2.2.2.1
  show 2 ≤ X.L.m
  omega

theorem p_ne_two {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : X.p ≠ 2 := by
  have h5 := X.std.1.five_le
  show X.L.p ≠ 2
  omega

private theorem setTies_deg_succ_pos_eq_of_strictMono {N : ℕ} (LL : GM.M.Letters N) (T : GM.M.TieData) (n : Fin T.t → ℕ)
    (hT : StrictMono T.pos) (i : Fin T.t) (h : T.pos i + 1 < N) :
    (LL.setTies T n).deg ⟨T.pos i + 1, h⟩ = n i := by
  have hex : ∃ j : Fin T.t, T.pos j + 1 = T.pos i + 1 := ⟨i, rfl⟩
  have hc : Classical.choose hex = i := hT.injective (by have := Classical.choose_spec hex; omega)
  show (if h' : ∃ j : Fin T.t, T.pos j + 1 = T.pos i + 1 then n (Classical.choose h')
    else LL.deg ⟨T.pos i + 1, h⟩) = n i
  rw [dif_pos hex, hc]

set_option maxHeartbeats 400000 in

theorem restTMHyp_of {CYb Cde Ck CD Cb Cc : ℝ} (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (hS : RestTMSize C0 CE1 CE2 X) : RestTMHyp C0 CE1 CE2 X := by
  intro dl hdl a ha x hx
  obtain ⟨hS1, hS2, hS3, hS4, hS5⟩ := hS dl hdl a ha x hx
  have hY : 1 ≤ X.L.Y := by
    obtain ⟨⟨hY, -⟩, -⟩ := hH
    exact hY
  set M := XMof C0 CE1 CE2 X dl a x.fst x.snd with hM
  have hpos : ∀ l : Fin M.T.t, M.T.pos l = 2 * ((uTop (X.S C0 CE1 CE2) l : Fin X.s) : ℕ) := fun l => rfl
  have hlt : ∀ l : Fin M.T.t, M.T.pos l + 1 < 2 * M.s + 1 := by
    intro l
    rw [hpos l]
    have := (uTop (X.S C0 CE1 CE2) l).isLt
    show _ < 2 * X.s + 1
    omega
  have hmono : StrictMono M.T.pos := by
    intro i j hij
    rw [hpos i, hpos j]
    have : (i : ℕ) < j := hij
    show 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) < 2 * ((X.S C0 CE1 CE2).sigma + (j : ℕ))
    omega
  have hvec : ∀ y, M.LL.vec y = decide ((y : ℕ) % 2 = 0) := fun y => rfl
  have htop : ∀ i, M.top i ≤ 2 * X.L.a := by
    intro i
    have := hS2 ⟨M.T.pos i + 1, hlt i⟩
    rwa [setTies_deg_succ_pos_eq_of_strictMono _ _ _ hmono i (hlt i)] at this
  have hdd : ∀ i, M.dd i = 1 := fun i => rfl
  have hYl : ∀ i, M.Yl i = (Nl C0 CE1 CE2 X dl x.snd i).sup id
      - sInf ↑(Nl C0 CE1 CE2 X dl x.snd i) + 1 := fun i => rfl
  have hYl1 : ∀ i, 1 ≤ M.Yl i := fun i => by rw [hYl i]; omega
  have htop' : ∀ i, M.top i = M.n₀ i + (M.Yl i - 1) := fun i => by
    show M.n₀ i + M.dd i * (M.Yl i - 1) = _
    rw [hdd, one_mul]
  have hr2 : 2 ≤ X.r := r_ge_two hH
  have key : ∀ n : ℕ, n ≤ 8 * X.L.a + X.r → (n : ℝ) ≤ 8 * M.a + M.r := by
    intro n hn
    rw [show M.a = (X.L.a : ℝ) from rfl, show M.r = X.r from rfl]
    exact_mod_cast hn
  have hd : ∀ j, M.degAt j ≤ 2 * X.L.a := by
    intro j
    unfold InstM.degAt
    split
    · exact hS2 _
    · omega
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, hS1, ?_⟩
  · exact p_ne_two hH
  · exact hr2
  · refine ⟨hmono, fun i => ⟨hlt i, ?_, ?_⟩, fun i => ⟨⟨i, Nat.lt_succ_of_lt i.isLt⟩, ?_⟩⟩
    · rw [hvec]
      simp only [decide_eq_true_eq]
      rw [hpos]
      omega
    · rw [hvec]
      simp only [decide_eq_false_iff_not]
      rw [hpos]
      omega
    · show (if h : (i : ℕ) < (X.S C0 CE1 CE2).t then
          2 * ((uTop (X.S C0 CE1 CE2) ⟨i, h⟩ : Fin X.s) : ℕ) + 1 else 2 * X.s + 1) = M.T.pos i + 1
      rw [dif_pos (show (i : ℕ) < (X.S C0 CE1 CE2).t from i.isLt)]
      rfl
  · intro y
    rfl
  · intro k
    by_cases hk : (k : ℕ) < (X.S C0 CE1 CE2).t
    · right
      refine ⟨⟨k, hk⟩, ?_⟩
      show (if h : (k : ℕ) < (X.S C0 CE1 CE2).t then
          2 * ((uTop (X.S C0 CE1 CE2) ⟨k, h⟩ : Fin X.s) : ℕ) + 1 else 2 * X.s + 1) = _
      rw [dif_pos hk]
      rfl
    · left
      show (if h : (k : ℕ) < (X.S C0 CE1 CE2).t then
          2 * ((uTop (X.S C0 CE1 CE2) ⟨k, h⟩ : Fin X.s) : ℕ) + 1 else 2 * X.s + 1) = _
      rw [dif_neg hk]
      rfl
  · show (1 : ℝ) ≤ X.L.a
    exact_mod_cast hS5
  · show 1 ≤ X.L.Y * kapS X
    have hp1 : 1 < X.p := by
      have := X.std.1.five_le
      show 1 < X.L.p
      omega
    have hl := lgA_ge_one X.p X.L.a X.r hp1 (by omega)
    have hr2' : (2 : ℝ) ≤ X.r := by exact_mod_cast hr2
    have hs0 : (0 : ℝ) ≤ X.s := Nat.cast_nonneg _
    unfold kapS
    have h1 : (1 : ℝ) ≤ 3 * (↑X.s + 2) * ↑X.r ^ 2 := by nlinarith
    have h2 : (1 : ℝ) ≤ 3 * (↑X.s + 2) * ↑X.r ^ 2 * lgA X.p X.L.a X.r := by nlinarith
    nlinarith
  · intro i
    refine ⟨hYl1 i, ?_, ?_⟩
    · rw [hdd]
      norm_num
    · rw [hdd, Nat.cast_one]
      exact isCoprime_one_left
  · refine ⟨?_, fun i => ⟨?_, ?_, ?_⟩⟩
    · apply key
      have : M.LLt.total ≤ 8 * X.L.a := hS4
      omega
    · apply key
      have h1 := hd (M.T.pos i)
      have h2 := hd (M.T.pos i + 1)
      have h3 := hS3 i
      have : M.r = X.r := rfl
      omega
    · apply key
      have := htop i
      have := htop' i
      omega
    · apply key
      have h1 : M.Si i ≤ M.n₀ i := hS1 i
      have := htop i
      have := htop' i
      omega

end Hyp

end Formalism.MainNotions.G.SymmetricFormBlocks

end
