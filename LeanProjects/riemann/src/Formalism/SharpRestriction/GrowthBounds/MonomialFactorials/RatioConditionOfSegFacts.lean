import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.DigitsOKOfCompat

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

theorem ratio_num (x y r : ℕ) (hx : 1 ≤ x) (hxy : x ≤ y) (h : (r : ℝ) * ((y : ℝ) - x) ≤ 3 * x) :
    (((y + r).choose r : ℕ) : ℝ) ≤ Real.exp 3 * (((x + r).choose r : ℕ) : ℝ) := by
  have h1 := choose_ratio r x y hx hxy
  have hx0 : (0 : ℝ) < x := by exact_mod_cast hx
  have hq : (y : ℝ) / x ≤ Real.exp (((y : ℝ) - x) / x) := by
    have := Real.add_one_le_exp (((y : ℝ) - x) / x)
    have e : ((y : ℝ) - x) / x + 1 = (y : ℝ) / x := by field_simp; ring
    linarith
  have hq0 : 0 ≤ (y : ℝ) / x := by positivity
  have h2 : ((y : ℝ) / x) ^ r ≤ Real.exp 3 := by
    calc ((y : ℝ) / x) ^ r ≤ Real.exp (((y : ℝ) - x) / x) ^ r := pow_le_pow_left₀ hq0 hq r
      _ = Real.exp ((r : ℝ) * (((y : ℝ) - x) / x)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp 3 := by
          apply Real.exp_le_exp.2
          rw [← mul_div_assoc, div_le_iff₀ hx0]
          exact h
  calc (((y + r).choose r : ℕ) : ℝ) ≤ ((y : ℝ) / x) ^ r * (((x + r).choose r : ℕ) : ℝ) := h1
    _ ≤ Real.exp 3 * (((x + r).choose r : ℕ) : ℝ) := by gcongr

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

theorem topA_spec (dl : DCl X) (aTop : Fin X.s → ℕ) (ha : aTop ∈ cbox C0 CE1 CE2 X dl) (l : Fin X.s) :
    topA C0 CE1 CE2 X dl l ∈ X.winA ∧ ∑ c, dl.2 l c ≤ topA C0 CE1 CE2 X dl l ∧
      (X.S C0 CE1 CE2).P X.p l ∣ topA C0 CE1 CE2 X dl l - ∑ c, dl.2 l c ∧ aTop l ≤ topA C0 CE1 CE2 X dl l := by
  classical
  obtain ⟨hT, hc⟩ := mem_cbox' ha
  have hmem : aTop l ∈ X.winA.filter fun x => ∑ c, dl.2 l c ≤ x ∧ (X.S C0 CE1 CE2).P X.p l ∣ x - ∑ c, dl.2 l c := by
    simp only [Finset.mem_filter]
    exact ⟨Fintype.mem_piFinset.1 hT l, hc.2.2 l⟩
  unfold topA
  obtain ⟨x, hxF, hx⟩ := Finset.exists_mem_eq_sup _ ⟨_, hmem⟩ (id : ℕ → ℕ)
  have hle : aTop l ≤ (X.winA.filter fun x => ∑ c, dl.2 l c ≤ x ∧
      (X.S C0 CE1 CE2).P X.p l ∣ x - ∑ c, dl.2 l c).sup id := Finset.le_sup (f := id) hmem
  rw [hx] at hle ⊢
  simp only [Finset.mem_filter] at hxF
  exact ⟨hxF.1, hxF.2.1, hxF.2.2, hle⟩

theorem upd_mem (dl : DCl X) (aTop : Fin X.s → ℕ) (ha : aTop ∈ cbox C0 CE1 CE2 X dl) (i : Fin (X.S C0 CE1 CE2).t) :
    upd C0 CE1 CE2 X dl aTop i ∈ cbox C0 CE1 CE2 X dl := by
  classical
  obtain ⟨hT, hc⟩ := mem_cbox' ha
  have hs := topA_spec dl aTop ha (uTop (X.S C0 CE1 CE2) i)
  unfold cbox
  simp only [Finset.mem_filter]
  refine ⟨Fintype.mem_piFinset.2 fun l => ?_, ⟨hc.1, hc.2.1, fun l => ?_⟩⟩
  · unfold upd
    by_cases h : l = uTop (X.S C0 CE1 CE2) i
    · subst h; rw [Function.update_self]; exact hs.1
    · rw [Function.update_of_ne h]; exact Fintype.mem_piFinset.1 hT l
  · unfold upd
    by_cases h : l = uTop (X.S C0 CE1 CE2) i
    · subst h; rw [Function.update_self]; exact ⟨hs.2.1, hs.2.2.1⟩
    · rw [Function.update_of_ne h]; exact hc.2.2 l

theorem prod_ratio {ι : Type*} [DecidableEq ι] (s : Finset ι) (u : ι) (hu : u ∈ s) (f g : ι → ℝ) (K : ℝ)
    (hg : ∀ l, 0 ≤ g l) (hfg : ∀ l ∈ s, l ≠ u → f l = g l) (hK : f u ≤ K * g u) :
    ∏ l ∈ s, f l ≤ K * ∏ l ∈ s, g l := by
  rw [← Finset.mul_prod_erase s f hu, ← Finset.mul_prod_erase s g hu]
  have e : ∏ l ∈ s.erase u, f l = ∏ l ∈ s.erase u, g l :=
    Finset.prod_congr rfl fun l hl => hfg l (Finset.mem_of_mem_erase hl) (Finset.ne_of_mem_erase hl)
  rw [e]
  have hP : 0 ≤ ∏ l ∈ s.erase u, g l := Finset.prod_nonneg fun l _ => hg l
  calc f u * ∏ l ∈ s.erase u, g l ≤ (K * g u) * ∏ l ∈ s.erase u, g l := mul_le_mul_of_nonneg_right hK hP
    _ = K * (g u * ∏ l ∈ s.erase u, g l) := by ring

theorem ratioCondition_of_segFacts (hS : SegFacts C0 CE1 CE2 X) : RestRatio C0 CE1 CE2 X := by
  classical
  intro dl _ aTop ha i
  refine ⟨upd_mem dl aTop ha i, ?_⟩
  obtain ⟨hT, hc⟩ := mem_cbox' ha
  have hs := topA_spec dl aTop ha (uTop (X.S C0 CE1 CE2) i)
  have hD : DigitsOK X.p (X.S C0 CE1 CE2) aTop (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) := hc
  have hc2 := upd_mem dl aTop ha i
  have hD2 : DigitsOK X.p (X.S C0 CE1 CE2) (upd C0 CE1 CE2 X dl aTop i) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) :=
    (mem_cbox' hc2).2
  obtain ⟨x, hx⟩ : ∃ x, x = coarseC X.p (X.S C0 CE1 CE2) aTop (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2)
      (uTop (X.S C0 CE1 CE2) i) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = coarseC X.p (X.S C0 CE1 CE2) (upd C0 CE1 CE2 X dl aTop i)
      (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) (uTop (X.S C0 CE1 CE2) i) := ⟨_, rfl⟩
  have hupdu : upd C0 CE1 CE2 X dl aTop i (uTop (X.S C0 CE1 CE2) i) = topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i) := by
    unfold upd
    exact Function.update_self _ _ _
  have hP1 : (1 : ℝ) ≤ ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by exact_mod_cast hS.P1 _
  have hkP := hS.kP (uTop (X.S C0 CE1 CE2) i)
  have hkb := hS.kb
  have hb0 := hS.hF.b0
  have hr0 : (0 : ℝ) ≤ (X.r : ℝ) := Nat.cast_nonneg _
  have hxP : (x : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) =
      (aTop (uTop (X.S C0 CE1 CE2) i) : ℝ) -
        ((∑ c, (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2 : SegBlock X.s X.r).ry (uTop (X.S C0 CE1 CE2) i) c : ℕ) : ℝ) := by
    have e := Nat.div_mul_cancel (hD.2.2 (uTop (X.S C0 CE1 CE2) i)).2
    rw [hx, ← Nat.cast_mul]
    unfold coarseC
    rw [e, Nat.cast_sub (hD.2.2 (uTop (X.S C0 CE1 CE2) i)).1]
  have hyP : (y : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) =
      (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i) : ℝ) -
        ((∑ c, (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2 : SegBlock X.s X.r).ry (uTop (X.S C0 CE1 CE2) i) c : ℕ) : ℝ) := by
    have e := Nat.div_mul_cancel (hD2.2.2 (uTop (X.S C0 CE1 CE2) i)).2
    rw [hy, ← Nat.cast_mul]
    unfold coarseC
    rw [e, Nat.cast_sub (hD2.2.2 (uTop (X.S C0 CE1 CE2) i)).1, hupdu]
  have hlow := coarseC_lower hS aTop _ hD (uTop (X.S C0 CE1 CE2) i)
  rw [← hx] at hlow
  have haw := win_ge hS aTop hT (uTop (X.S C0 CE1 CE2) i)
  have hxy : x ≤ y := by
    have h1 : (x : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
        (y : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
      rw [hxP, hyP]
      have : (aTop (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
        exact_mod_cast hs.2.2.2
      linarith
    have := le_of_mul_le_mul_right h1 (by linarith)
    exact_mod_cast this
  have hxP2 : (X.L.a : ℝ) * (3 / 4) ≤ (x : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
    nlinarith
  have hx1 : 1 ≤ x := by
    have h2 : ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤ (X.L.a : ℝ) * (3 / 4) := by nlinarith
    have h4 : (1 : ℝ) ≤ (x : ℝ) := by
      by_contra hcn
      push Not at hcn
      have : (x : ℝ) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) <
          1 * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) :=
        mul_lt_mul_of_pos_right hcn (by linarith)
      linarith
    exact_mod_cast h4
  have hnum : (X.r : ℝ) * ((y : ℝ) - x) ≤ 3 * x := by
    have htop : (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
        (X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa := by
      have h1 := (Finset.mem_Icc.1 hs.1).2
      have h2 : (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
          (⌊(X.L.a : ℝ) + X.L.a / (X.L.k * X.L.Y) + X.xa⌋₊ : ℝ) := by exact_mod_cast h1
      exact h2.trans (Nat.floor_le hS.hF.win0)
    have hk : X.L.k = (X.r : ℝ) + 1 := rfl
    have hY := hS.Y1
    have ha0 : (0 : ℝ) ≤ X.L.a := Nat.cast_nonneg _
    have hrk : (X.r : ℝ) * ((X.L.a : ℝ) / (X.L.k * X.L.Y)) ≤ X.L.a := by
      rw [hk]
      have h0 : (0 : ℝ) < ((X.r : ℝ) + 1) * X.L.Y := by nlinarith
      rw [mul_div_assoc', div_le_iff₀ h0]
      have h1 : (X.L.a : ℝ) * (((X.r : ℝ) + 1) * 1) ≤ (X.L.a : ℝ) * (((X.r : ℝ) + 1) * X.L.Y) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY (by linarith)) ha0
      linarith
    have hJ : (X.r : ℝ) * X.xa ≤ (X.L.a : ℝ) / 8 := by
      have h1 := hS.xa
      have hLa := hS.La4
      have hLa0 := hS.hF.La0
      unfold Formalism.MainNotions.ColumnSystems.Loc.J0 at h1
      rw [hk] at h1
      have hk0 : (0 : ℝ) < (X.r : ℝ) + 1 := by linarith
      have h2 : (X.r : ℝ) * X.xa ≤ ((X.r : ℝ) + 1) * X.xa := by nlinarith [hS.xa0]
      have h3 : ((X.r : ℝ) + 1) * X.xa ≤ 2 * X.L.La C0 * X.L.b' := by
        have := mul_le_mul_of_nonneg_left h1 hk0.le
        have e : ((X.r : ℝ) + 1) * (2 * (X.L.La C0 * X.L.b' / ((X.r : ℝ) + 1))) = 2 * X.L.La C0 * X.L.b' := by
          field_simp
        linarith
      have h4 : 2 * X.L.La C0 * X.L.b' ≤ ((X.r : ℝ) + 1) / 2 * X.L.b' := by nlinarith
      have h5 : ((X.r : ℝ) + 1) / 2 * X.L.b' ≤ (X.L.a : ℝ) / 8 := by nlinarith
      linarith
    have hd : ((y : ℝ) - x) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
        X.L.a / (X.L.k * X.L.Y) + X.xa := by
      have : ((y : ℝ) - x) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) =
          (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i) : ℝ) - aTop (uTop (X.S C0 CE1 CE2) i) := by
        rw [sub_mul, hxP, hyP]; ring
      rw [this]
      linarith
    have h7 : (X.r : ℝ) * (((y : ℝ) - x) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ)) ≤
        (X.r : ℝ) * ((X.L.a : ℝ) / (X.L.k * X.L.Y) + X.xa) := mul_le_mul_of_nonneg_left hd hr0
    have h6 : (X.r : ℝ) * ((y : ℝ) - x) * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) ≤
        3 * x * ((X.S C0 CE1 CE2).P X.p (uTop (X.S C0 CE1 CE2) i) : ℝ) := by
      nlinarith
    exact le_of_mul_le_mul_right h6 (by linarith)
  have hratio := ratio_num x y X.r hx1 hxy hnum
  have hoth : ∀ l, l ≠ uTop (X.S C0 CE1 CE2) i →
      coarseC X.p (X.S C0 CE1 CE2) (upd C0 CE1 CE2 X dl aTop i) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) l =
        coarseC X.p (X.S C0 CE1 CE2) aTop (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) l := by
    intro l hl
    unfold coarseC upd
    rw [Function.update_of_ne hl]
  unfold mCl Formalism.MainNotions.ColumnSystems.dimMM
  push_cast
  have hprod := prod_ratio Finset.univ (uTop (X.S C0 CE1 CE2) i) (Finset.mem_univ _)
    (fun l => (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1) (coarseA X.L.p (X.S C0 CE1 CE2) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) l : ℤ) : ℝ) *
      (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1)
        (coarseC X.L.p (X.S C0 CE1 CE2) (upd C0 CE1 CE2 X dl aTop i) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) l : ℤ) : ℝ))
    (fun l => (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1) (coarseA X.L.p (X.S C0 CE1 CE2) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) l : ℤ) : ℝ) *
      (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1) (coarseC X.L.p (X.S C0 CE1 CE2) aTop (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) l : ℤ) : ℝ))
    (Real.exp 3) (fun l => by positivity)
    (fun l _ hl => by rw [hoth l hl])
    (by
      rw [← hx, ← hy, symDim_choose X.L.m y, symDim_choose X.L.m x]
      have h0 : (0 : ℝ) ≤ (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1)
          (coarseA X.L.p (X.S C0 CE1 CE2) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) (uTop (X.S C0 CE1 CE2) i) : ℤ) : ℝ) := by
        positivity
      calc _ ≤ (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1)
              (coarseA X.L.p (X.S C0 CE1 CE2) (Formalism.MainNotions.ColumnSystems.digitBlock dl.1 dl.2) (uTop (X.S C0 CE1 CE2) i) : ℤ) : ℝ) *
            (Real.exp 3 * (((x + X.r).choose X.r : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hratio h0
        _ = _ := by ring)
  have hA : (0 : ℝ) ≤ (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1) ((X.S C0 CE1 CE2).A0 X.L.p) : ℝ) := by positivity
  have hB : (0 : ℝ) ≤ (Formalism.MainNotions.ColumnSystems.symDim (X.L.m + 1) ((X.S C0 CE1 CE2).bPlus : ℤ) : ℝ) := by positivity
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hA) hB
  calc _ ≤ _ := this
    _ = _ := by ring

end Formalism.MainNotions.G.SymmetricFormBlocks

end
