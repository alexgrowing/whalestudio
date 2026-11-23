import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes

noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf

variable {D : D7} {L : SizeData₂ D}

theorem sc_x_pos (s : Scale) : 0 < s.x := lt_trans zero_lt_one s.one_lt_alt

theorem sc_one_le_b (s : Scale) : 1 ≤ s.b := by
  unfold Scale.b
  exact Real.one_le_exp (Real.rpow_nonneg (sc_x_pos s).le _)

theorem sc_one_lt_a (s : Scale) : 1 < s.a := by
  unfold Scale.a
  exact one_lt_mul_of_lt_of_le s.one_lt_alt (sc_one_le_b s)

theorem sc_b'_nonneg (s : Scale) : 0 ≤ s.b' := by
  unfold Scale.b'
  exact div_nonneg (by linarith [sc_one_lt_a s]) (Real.exp_pos _).le

theorem sc_w''_nonneg (s : Scale) (n : ℕ) : 0 ≤ s.w'' n := by
  unfold Scale.w''
  exact div_nonneg (sc_b'_nonneg s) (mul_nonneg (sc_x_pos s).le (Nat.cast_nonneg n))

theorem sc_delta1_pos (s : Scale) : 0 < s.delta1 := by
  unfold Scale.delta1
  exact Real.rpow_pos_of_pos (sc_x_pos s) _

theorem X'_le_X'' (s : Scale) (n : ℕ) (hn : 1 ≤ n) : s.X' ≤ s.X'' n := by
  have hX' : 0 < s.X' := Real.exp_pos _
  have ha : 0 < s.a := by linarith [sc_one_lt_a s]
  have hx := sc_x_pos s
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h : s.X'' n = s.x * n * s.X' := by
    unfold Scale.X'' Scale.w'' Scale.b'
    field_simp
  rw [h]
  exact le_mul_of_one_le_left hX'.le (one_le_mul_of_one_le_of_one_le s.one_lt_alt.le hn')

theorem cand_of_VV_ne (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (h : VV X K a b p ≠ ∅) :
    Cand D L K p := by
  unfold VV at h
  split_ifs at h with hc
  · exact hc.1
  · exact absurd rfl h

theorem Nm_le_Sc (P : ParameterChoice' D L) : (5 : ℝ) ≤ (D.R.k : ℝ) ∧ (D.R.N D.R.m : ℝ) ≤ L.Sc ∧ 100 ≤ L.Sc := by
  have hm : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast D.R.two_le_m
  have hk : (5 : ℝ) ≤ (D.R.k : ℝ) := by
    have := D.R.m_add_three_le_k
    have h2 := D.R.two_le_m
    exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hNk : (D.R.k : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    have : D.R.k ≤ D.R.N D.R.m := by unfold Ranks.N; omega
    exact_mod_cast this
  have h := P.Del_ge.2.2.2
  have hm10 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ (by linarith)
  have hN0 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) := Nat.cast_nonneg _
  have hND : (D.R.N D.R.m : ℝ) ≤ (D.s.Del : ℝ) := by
    have := mul_le_mul_of_nonneg_left hm10 hN0
    linarith
  have hD : (5 : ℝ) ≤ (D.s.Del : ℝ) := by linarith
  have hkD : 5 * (D.s.Del : ℝ) ≤ (D.R.k : ℝ) * (D.s.Del : ℝ) := mul_le_mul_of_nonneg_right hk (by linarith)
  refine ⟨hk, ?_, ?_⟩ <;> rw [L.Sc_eq] <;> nlinarith

theorem kaJ_le (P : ParameterChoice' D L) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) : kaJ D j ≤ L.Sc := by
  obtain ⟨hk, hN, _⟩ := Nm_le_Sc P
  have hj2 : (j : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hj).2
  have hNe : (D.R.N D.R.m : ℝ) = (D.R.k : ℝ) + (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) := by
    unfold Ranks.N; push_cast; ring
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) + 1 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hj2 ht
  unfold kaJ
  nlinarith

theorem w''_le (s : Scale) (n : ℕ) (hn : 1 ≤ n) : s.w'' n ≤ s.b' / s.x ∧ s.b' / s.x ≤ s.b' := by
  have hx := sc_x_pos s
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb := sc_b'_nonneg s
  refine ⟨?_, div_le_self hb s.one_lt_alt.le⟩
  unfold Scale.w''
  exact div_le_div_of_nonneg_left hb hx (le_mul_of_one_le_right hx.le hn')

theorem two_b'_le_a (s : Scale) : 2 * s.b' ≤ s.a := by
  have hy : 1 < s.x ^ (s.eps / 3) := Real.one_lt_rpow s.one_lt_alt (by linarith [s.eps_pos])
  have hX : 2 ≤ s.X' := by
    unfold Scale.X'
    linarith [Real.add_one_le_exp (s.x ^ (s.eps / 3))]
  have ha : 0 < s.a := by linarith [sc_one_lt_a s]
  unfold Scale.b'
  rw [mul_div_assoc', div_le_iff₀ (by linarith)]
  nlinarith

def InWin (L : SizeData₂ D) (a b : HH D → ℤ) : Prop :=
  ∀ t ∈ D.host.TT, L.sc.a ≤ (a t : ℝ) ∧
    (a t : ℝ) ≤ L.sc.a + L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ∧ L.sc.b' ≤ (b t : ℝ)

def GainBoundAtPairUniform (X : Inst D L) (K : Consts) (C bo : ℝ) (a b : HH D → ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (IsResidueClassZero D p ∨ IsSg D p) → (p : ℝ) ≤ L.sc.X'' D.R.n →
    (∀ j ∈ SizeData₂.lifts D, 0 ≤ gainP X K a b p j ∧
      gainP X K a b p j ≤ 4 * (D.host.TT.card : ℝ) * L.sc.a / (p : ℝ)) ∧
    (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ TTP X K a b p,
        (askP X a b p j s - lo K L C bo p)) - (D.R.m : ℝ) * fl D L.sc C p ≤
      (∑ j ∈ SizeData₂.lifts D, gainP X K a b p j) - tauP X K a b p

def GainBoundAllUniform (X : Inst D L) (K : Consts) (C bo : ℝ) : Prop := ∀ a b, InWin L a b → GainBoundAtPairUniform X K C bo a b

def GainBoundAt (X : Inst D L) (K : Consts) (C bo : ℝ) (a b : HH D → ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → (IsResidueClassZero D p ∨ IsSg D p) → (p : ℝ) ≤ L.sc.X'' D.R.n →
    (∀ j ∈ SizeData₂.lifts D, 0 ≤ gainP X K a b p j ∧
      gainP X K a b p j ≤ 4 * (D.host.TT.card : ℝ) * L.sc.a / (p : ℝ)) ∧
    (∑ j ∈ SizeData₂.lifts D, ∑ s ∈ TTP X K a b p,
        (askG X a b p j s - lo K L C bo p)) - (D.R.m : ℝ) * fl D L.sc C p ≤
      (∑ j ∈ SizeData₂.lifts D, gainP X K a b p j) - tauP X K a b p

def GainBoundAll (X : Inst D L) (K : Consts) (C bo : ℝ) : Prop := ∀ a b, InWin L a b → GainBoundAt X K C bo a b

def RequiresAll (X : Inst D L) : Prop :=
  ∀ a b : HH D → ℤ, (∀ s ∈ D.host.TT, (a s : ℝ) ≤ 2 * L.sc.a) → (∀ s ∈ D.host.TT, (0 : ℝ) ≤ (b s : ℝ)) →
    ∀ p : ℕ, p.Prime → ∀ j ∈ SizeData₂.lifts D, ∀ s ∈ D.host.TT,
    askP X a b p j s ≤ askG X a b p j s ∧
    askG X a b p j s ≤ askP X a b p j s + Nm D * Real.logb p (2 * L.sc.a)

def StarAt (X : Inst D L) (K : Consts) (C bo : ℝ) (a b : HH D → ℤ) (p j : ℕ) (t0 : HH D) : Prop :=
  ∑ s ∈ topsOn X p t0, (askP X a b p j s - lo K L C bo p) ≤
    gU X K a b p j t0 + dl X K p t0 - Pr X K b p j t0 - (⌈tv X K a b p t0⌉₊ : ℝ) - (Dp K L p : ℝ) - 1

def StarAll (X : Inst D L) (K : Consts) (C bo : ℝ) : Prop :=
  ∀ a b, InWin L a b → ∀ p, Cand D L K p → ∀ t0 ∈ goodReps X p, ∀ j ∈ SizeData₂.lifts D, StarAt X K C bo a b p j t0

open Classical in

def candF (D : D7) (L : SizeData₂ D) (K : Consts) : Finset ℕ :=
  (Finset.range ⌈L.sc.X'⌉₊).filter (fun p => Cand D L K p)

open Classical in

def ZZ (X : Inst D L) (K : Consts) (a b : HH D → ℤ) : ℝ :=
  ∑ p ∈ candF D L K, Real.log p / p *
    ((if L.sc.x ^ (-L.sc.eps) < Sig X K a b p then 1 else 0) + Sig X K a b p)

def MeanEx (X : Inst D L) (K : Consts) : Prop :=
  (∀ a b p, Cand D L K p → 0 ≤ Sig X K a b p) ∧
  ∃ a ∈ box D (winA D L.sc), ∃ b ∈ box D (winB D K L.sc), ZZ X K a b ≤ L.sc.x ^ (-9 : ℝ) / 4

theorem inWin_sizeData (L : SizeData₂ D) : InWin L (aL L) (bL L) := by
  intro t ht
  simp only [aL, bL, dif_pos ht]
  exact ⟨(L.aT_win _).1, (L.aT_win _).2, L.bT_ge _⟩

def AdmFam {eps : ℝ} (Fm : FamP eps) (K : Consts) (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i))
    (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)) (C31 Ce Cm : ℝ) : Prop :=
  ∀ δ > 0, ∃ x0 : ℝ, 1 < x0 ∧ ∀ x ≥ x0, ∀ i : Fm.Ix x,
    admitted (Fm.D x i) (Fm.L x i) (X x i) (Y x i) K ⟨C31, Ce, Cm, δ⟩

end Formalism.MainNotions.AuxBlock8.Pf

end
