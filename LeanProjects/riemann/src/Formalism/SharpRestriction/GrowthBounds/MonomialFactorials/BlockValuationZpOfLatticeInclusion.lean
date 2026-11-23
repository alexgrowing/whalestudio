import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.DegFactNeZero

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Gen

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem le_expM (l : (Fin G.T.t → ℕ) × ℕ) (hl : l ∈ levels G) :
    padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2) ≤ expM p (r := r) G :=
  Finset.le_sup (f := fun l : (Fin G.T.t → ℕ) × ℕ => padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2)) hl

theorem levels_nonempty : (levels G).Nonempty := by
  classical
  refine ⟨(fun _ => 0, 0), ?_⟩
  unfold levels
  rw [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset]
  exact ⟨⟨fun _ => Finset.mem_range.2 (Nat.succ_pos _), Finset.mem_range.2 (Nat.succ_pos _)⟩,
    fun _ => ⟨Nat.zero_le _, Nat.zero_le _⟩, Nat.zero_le _⟩

theorem exists_expM : ∃ l ∈ levels G, expM p (r := r) G = padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2) :=
  Finset.exists_mem_eq_sup (levels G) (levels_nonempty G)
    (fun l : (Fin G.T.t → ℕ) × ℕ => padicValNat p (lvC (r := r) G l.1 l.2 * degFact G l.1 l.2))

end Gen

section Inst

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def aBig : ℕ := (3 * X.s + 2) * X.L.a

def RestLL : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
      ∀ x ∈ (gB C0 CE1 CE2 X aTop aPlus b).PSZ X.p (r := X.r),
        ((X.p : ℚ_[X.p]) ^ (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X))) • x ∈
          (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r)

def RestVal : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
      ∀ l ∈ levels (gB C0 CE1 CE2 X aTop aPlus b),
        ∀ z ∈ (gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r), ∀ μ ∈ z.support,
          (padicValNat X.p (lvC (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2 *
              degFact (gB C0 CE1 CE2 X aTop aPlus b) l.1 l.2) : ℝ) +
            2 * (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X) : ℝ) ≤
          (padicValNat X.p (μ.prod fun _ k => k.factorial) : ℝ) + levelPassageLoss X

theorem lv_eq (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) :
    lv C0 CE1 CE2 X aTop b = levels (gB C0 CE1 CE2 X aTop aPlus b) := rfl

theorem gB_blockOK (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r) :
    (gB C0 CE1 CE2 X aTop aPlus b).BlockOK := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i i' h
    have h' : (i : ℕ) < (i' : ℕ) := h
    show 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) < 2 * ((X.S C0 CE1 CE2).sigma + (i' : ℕ))
    omega
  · intro i
    have hi : (X.S C0 CE1 CE2).sigma + (i : ℕ) < X.s := (uTop (X.S C0 CE1 CE2) i).2
    refine ⟨?_, ?_, ?_⟩
    · show 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1 < 2 * X.s + 1
      omega
    · show decide ((2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ))) % 2 = 0) = true
      simp
    · show decide ((2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1) % 2 = 0) = false
      rw [decide_eq_false_iff_not]
      omega
  · intro i
    have hi : (i : ℕ) < (X.S C0 CE1 CE2).t := i.2
    refine ⟨(⟨(i : ℕ), Nat.lt_succ_of_lt hi⟩ : Fin ((X.S C0 CE1 CE2).t + 1)), ?_⟩
    show (if h : (i : ℕ) < (X.S C0 CE1 CE2).t then 2 * (uTop (X.S C0 CE1 CE2) ⟨(i : ℕ), h⟩ : ℕ) + 1 else 2 * X.s + 1) =
      2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1
    rw [dif_pos hi]
    rfl
  · intro i
    have hi : (X.S C0 CE1 CE2).sigma + (i : ℕ) < X.s := (uTop (X.S C0 CE1 CE2) i).2
    show 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1 < 2 * X.s
    omega
  · show decide ((2 * X.s) % 2 = 0) = true
    simp
  · rfl

theorem block_valuation_Zp_of_lattice_inclusion (hr : 1 ≤ X.r) (hLL : RestLL C0 CE1 CE2 X) (hV : RestVal C0 CE1 CE2 X) :
    BlockBoundIntegers C0 CE1 CE2 X := by
  intro aTop hT aPlus hP b hK D _
  obtain ⟨n, x, y, hx, hy, hxy, hsum⟩ := blkZ_gen X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b)
    (gB_blockOK C0 CE1 CE2 X aTop aPlus b) hr (expU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) (aBig X))
    (expM X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b)) (hLL aTop hT aPlus hP b hK)
    (fun l hl => le_expM X.p _ l hl) D
  refine ⟨n, x, y, _, hx, hy, hxy, ?_, hsum⟩
  intro z hz μ hμ
  obtain ⟨l, hl, hl'⟩ := exists_expM X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b)
  have h := hV aTop hT aPlus hP b hK l hl z hz μ hμ
  rw [← hl'] at h
  push_cast
  linarith

theorem gB_deg_le {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) (aTop : Fin X.s → ℕ)
    (haTop : aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA)) (aPlus : ℕ) (haPlus : aPlus ∈ X.winA)
    (b : SegBlock X.s X.r) (hK : Kept X.p X.r (X.S C0 CE1 CE2) aTop b) :
    1 ≤ aBig X ∧ (∀ x, (gB C0 CE1 CE2 X aTop aPlus b).LL.deg x ≤ 2 * aBig X) ∧
      (gB C0 CE1 CE2 X aTop aPlus b).B ≤ 2 * aBig X ∧
      (∀ i, (gB C0 CE1 CE2 X aTop aPlus b).T.z i ≤ 2 * aBig X) ∧
      (gB C0 CE1 CE2 X aTop aPlus b).zPlus ≤ 2 * aBig X := by
  have hF := hiFacts C0 CYb Cde Ck CD Cb Cc X hCYb hH
  have hmR : (4 : ℝ) ≤ (X.L.m : ℝ) := by exact_mod_cast hF.m4
  have hp25 : (25 : ℝ) ≤ (X.L.p : ℝ) := by nlinarith [hF.p_ge]
  have hp1 : 1 ≤ X.p := by
    have : (1 : ℝ) ≤ (X.L.p : ℝ) := by linarith
    exact_mod_cast this
  have ha0 : (0 : ℝ) ≤ (X.L.a : ℝ) := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ (X.s : ℝ) := Nat.cast_nonneg _
  have hb10 : 5 / 2 * X.L.b' ≤ (X.L.a : ℝ) / 10 := by nlinarith [hF.b_lt, hF.b0]
  have hE0 : 0 ≤ (X.S C0 CE1 CE2).E0 := by
    show 0 ≤ errorTermBound CE1 CE2 X.L.p X.L.k X.L.N1 X.L.Q X.L.c X.L.a X.L.b' (X.L.La C0)
    unfold errorTermBound
    have h1 := hF.La0
    have h2 := hF.b0.le
    have h3 : (0 : ℝ) ≤ X.L.k := by show (0 : ℝ) ≤ (X.L.m : ℝ) + 1; positivity
    have h4 : (0 : ℝ) ≤ X.L.Q := by show (0 : ℝ) ≤ (X.L.p : ℝ) ^ X.L.G'; positivity
    positivity
  have hLa : (X.S C0 CE1 CE2).La / ((X.r : ℝ) + 1) + 4 / (X.p : ℝ) ^ 2 ≤ 1 := by
    show X.L.La C0 / ((X.L.m : ℝ) + 1) + 4 / (X.L.p : ℝ) ^ 2 ≤ 1
    have h1 : X.L.La C0 / ((X.L.m : ℝ) + 1) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith [hF.La_lt]
    have h2 : 4 / (X.L.p : ℝ) ^ 2 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have hbig : ((2 * aBig X : ℕ) : ℝ) = 2 * ((3 * (X.s : ℝ) + 2) * (X.L.a : ℝ)) := by
    unfold aBig; push_cast; ring
  have hsa : 0 ≤ (X.s : ℝ) * (X.L.a : ℝ) := mul_nonneg hs0 ha0
  have hwin : ∀ x ∈ X.winA, (x : ℝ) ≤ 2 * (X.L.a : ℝ) := by
    intro x hx
    have h2 := (Finset.mem_Icc.1 hx).2
    have h3 : (x : ℝ) ≤ (⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℝ) := by exact_mod_cast h2
    exact (h3.trans (Nat.floor_le hF.win0)).trans hF.win_le
  have hbT : ∀ i, ((X.S C0 CE1 CE2).bTop i : ℝ) ≤ (X.L.a : ℝ) / 10 := fun i =>
    (hF.bT_le _ (segPos_mem X.L.TT X.j i)).trans hb10
  have hbP : ((X.S C0 CE1 CE2).bPlus : ℝ) ≤ (X.L.a : ℝ) / 10 := (hF.bT_le _ (segNext_mem X.L.TT X.j)).trans hb10
  refine ⟨?_, fun x => ?_, ?_, fun i => ?_, ?_⟩
  · have h1 : 1 ≤ X.L.a := by exact_mod_cast hF.a1
    unfold aBig
    exact Nat.mul_pos (by omega) h1
  · have h1 := segChain_deg_le (X.S C0 CE1 CE2) aTop b hK hp1 hE0 hF.La0 hLa (2 * (X.L.a : ℝ)) ((X.L.a : ℝ) / 10)
      hbT hbP (fun i => hwin _ (Fintype.mem_piFinset.1 haTop i))
      (show (X.L.a : ℝ) ≤ 2 * (X.L.a : ℝ) by linarith) x
    have h2 : (((gB C0 CE1 CE2 X aTop aPlus b).LL.deg x : ℕ) : ℝ) ≤ ((2 * aBig X : ℕ) : ℝ) := by
      rw [hbig]
      refine le_trans h1 ?_
      nlinarith
    exact_mod_cast h2
  · have h2 : (((gB C0 CE1 CE2 X aTop aPlus b).B : ℕ) : ℝ) ≤ ((2 * aBig X : ℕ) : ℝ) := by
      rw [hbig]
      refine le_trans hbP ?_
      nlinarith
    exact_mod_cast h2
  · have h0 : (gB C0 CE1 CE2 X aTop aPlus b).T.z i ≤ (X.S C0 CE1 CE2).bTop (uTop (X.S C0 CE1 CE2) i) :=
      (Nat.sub_le _ _).trans (coarseA_le (X.S C0 CE1 CE2) b _)
    have h2 : (((gB C0 CE1 CE2 X aTop aPlus b).T.z i : ℕ) : ℝ) ≤ ((2 * aBig X : ℕ) : ℝ) := by
      rw [hbig]
      refine le_trans (Nat.cast_le.2 h0) (le_trans (hbT _) ?_)
      nlinarith
    exact_mod_cast h2
  · have h0 : (gB C0 CE1 CE2 X aTop aPlus b).zPlus ≤ aPlus := Nat.sub_le _ _
    have h2 : (((gB C0 CE1 CE2 X aTop aPlus b).zPlus : ℕ) : ℝ) ≤ ((2 * aBig X : ℕ) : ℝ) := by
      rw [hbig]
      refine le_trans (Nat.cast_le.2 h0) (le_trans (hwin _ haPlus) ?_)
      nlinarith
    exact_mod_cast h2

theorem restLL_of {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X)
    (hTU : ∀ (aTop : Fin X.s → ℕ) (aPlus : ℕ) (b : SegBlock X.s X.r),
      Formalism.InvariantFactorPaths.KP.LL.HypJoin X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) ∧
      Formalism.InvariantFactorPaths.KP.LL.HypU X.p (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b)) : RestLL C0 CE1 CE2 X := by
  intro aTop hT aPlus hP b hK
  obtain ⟨h1, h2, h3, h4, h5⟩ := gB_deg_le C0 CE1 CE2 X hCYb hCE1 hCE2 hH aTop hT aPlus hP b hK
  have hr : 1 ≤ X.r := by have := r_ge C0 CYb Cde Ck CD Cb Cc X hH; omega
  exact (Formalism.InvariantFactorPaths.KP.Top.levelLattice X.p (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b) (aBig X)
    (gB_blockOK C0 CE1 CE2 X aTop aPlus b) hr h1 h2 h3 h4 h5 (hTU aTop aPlus b).1 (hTU aTop aPlus b).2).2.2

end Inst

end Formalism.MainNotions.G.SymmetricFormBlocks

end
