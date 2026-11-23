import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.Development

noncomputable section

namespace PI.SzCt.UnitaryGroupMassFormula

open Formalism.BasicNotions Formalism.MainNotions.G

theorem ct_le (hA : RowA) (hB : RowB) (hC : RowC) (hS : SizeFacts) (hP : PlaceFacts)
    (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (hx : 3 ≤ L.sc.x) (hSz : Formalism.MainNotions.SizesAt L)
    (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (u : D.what₂.Word) (t : HH D) :
    ctD D u j t ≤ (if t ∈ D.host.TT then 2 * L.sc.b else 0) + 4 * (D.R.k : ℝ) * L.sc.b' := by
  obtain ⟨hbT, hη, hkSc, hw'', hmη, hb1, hb'0⟩ := hS D L hSz hx
  obtain ⟨hP1, hP2, hP3, hP4⟩ := hP D
  have hj' := hj
  simp only [SizeData₂.lifts, Finset.mem_Icc] at hj'
  obtain ⟨hj1, hj2⟩ := hj'
  have hk5 : (5 : ℝ) ≤ (D.R.k : ℝ) := by
    have h1 := D.R.m_add_three_le_k
    have h2 := D.R.two_le_m
    exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hx0 : 0 < L.sc.x := by linarith
  have hxne : L.sc.x ≠ 0 := hx0.ne'
  have hSc : 0 < L.Sc := L.Sc_pos
  have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ) := by linarith

  have hq : L.sc.b' / L.sc.x * L.sc.x = L.sc.b' := by field_simp
  have hq0 : 0 ≤ L.sc.b' / L.sc.x := div_nonneg hb'0 hx0.le
  have hbx : 3 * (L.sc.b' / L.sc.x) ≤ L.sc.b' := by nlinarith
  have hkSc0 : 0 ≤ (D.R.k : ℝ) * L.Sc := mul_nonneg hk0 hSc.le
  have hw0 : 0 ≤ L.sc.w'' D.R.n := le_trans hkSc0 hkSc
  have hr : L.sc.w'' D.R.n / L.sc.x * L.sc.x = L.sc.w'' D.R.n := by field_simp
  have hr0 : 0 ≤ L.sc.w'' D.R.n / L.sc.x := div_nonneg hw0 hx0.le
  have hwx : L.sc.w'' D.R.n / L.sc.x ≤ L.sc.w'' D.R.n := by nlinarith
  have h3Sc : 3 * L.Sc ≤ (D.R.k : ℝ) * L.Sc := by nlinarith
  have hkb' : 5 * L.sc.b' ≤ (D.R.k : ℝ) * L.sc.b' := mul_le_mul_of_nonneg_right hk5 hb'0
  have hmη0 : 0 ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by
    have : (0 : ℝ) ≤ L.etaSz := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hEta, -⟩ := hSz
      exact le_trans (Nat.cast_nonneg _) hEta.1
    positivity
  by_cases ht : t ∈ D.host.TT
  · simp only [ctD, if_pos ht]
    have hRA := hA D L j hj u (tauPl D (false, t))
    have hRC := hC D L P j hj u (tauPl D (true, t)) (hP3 t)
    have hwF := L.win_top j hj1 hj2 (tauPl D (false, t)) ⟨t, ht⟩ (hP1 t)
    have hbt := hbT ⟨t, ht⟩
    have hwT : wj D j (tauPl D (true, t)) ≤ L.sc.b + L.etaSz + 1 ∨
        wj D j (tauPl D (true, t)) ≤ L.sc.w'' D.R.n + L.etaSz := by
      rcases hP4 t with h | h
      · exact Or.inl (L.win_thick j hj1 hj2 _ h).2
      · exact Or.inr (L.win_thin j hj1 hj2 _ h).2
    have hkw : (D.R.k : ℝ) * wj D j (tauPl D (false, t)) ≤
        (D.R.k : ℝ) * ((L.bT ⟨t, ht⟩ : ℝ) + L.sc.b' / L.sc.x + L.etaSz) :=
      mul_le_mul_of_nonneg_left hwF.2 hk0
    have e1 : (D.R.k : ℝ) * ((L.bT ⟨t, ht⟩ : ℝ) + L.sc.b' / L.sc.x + L.etaSz) =
        (D.R.k : ℝ) * (L.bT ⟨t, ht⟩ : ℝ) + (D.R.k : ℝ) * (L.sc.b' / L.sc.x) +
          (D.R.k : ℝ) * L.etaSz := by ring
    have e2 : (D.R.k : ℝ) * (L.Sc + wj D j (tauPl D (false, t))) =
        (D.R.k : ℝ) * L.Sc + (D.R.k : ℝ) * wj D j (tauPl D (false, t)) := by ring
    have k1 : (D.R.k : ℝ) * (L.bT ⟨t, ht⟩ : ℝ) ≤ (D.R.k : ℝ) * (5 / 4 * L.sc.b') :=
      mul_le_mul_of_nonneg_left hbt hk0
    have k2 : (D.R.k : ℝ) * (L.sc.b' / L.sc.x) ≤ (D.R.k : ℝ) * (L.sc.b' / 3) :=
      mul_le_mul_of_nonneg_left (by linarith) hk0
    have k3 : (D.R.k : ℝ) * L.etaSz ≤ (D.R.k : ℝ) * (L.sc.b' / 3) :=
      mul_le_mul_of_nonneg_left (by linarith) hk0
    have e3 : (D.R.k : ℝ) * (5 / 4 * L.sc.b') + (D.R.k : ℝ) * (L.sc.b' / 3) +
        (D.R.k : ℝ) * (L.sc.b' / 3) = 23 / 12 * ((D.R.k : ℝ) * L.sc.b') := by ring
    have e4 : 4 * (D.R.k : ℝ) * L.sc.b' = 4 * ((D.R.k : ℝ) * L.sc.b') := by ring
    rcases hwT with hT | hT <;> linarith
  · simp only [ctD, if_neg ht]
    have hthin := hP2 t ht
    have hRB := hB D L P j hj u (tauPl D (false, t)) hthin.2.1
    have hwF := (L.win_thin j hj1 hj2 (tauPl D (false, t)) hthin).2
    have hkw : (D.R.k : ℝ) * wj D j (tauPl D (false, t)) ≤
        (D.R.k : ℝ) * (L.sc.w'' D.R.n + L.etaSz) :=
      mul_le_mul_of_nonneg_left hwF hk0
    have k1 : (D.R.k : ℝ) * (L.sc.w'' D.R.n + L.etaSz) ≤ (D.R.k : ℝ) * (2 * (L.sc.b' / 3)) :=
      mul_le_mul_of_nonneg_left (by linarith) hk0
    have e1 : ((D.R.k : ℝ) + 2) * L.Sc = (D.R.k : ℝ) * L.Sc + 2 * L.Sc := by ring
    have e2 : (D.R.k : ℝ) * (2 * (L.sc.b' / 3)) = 2 / 3 * ((D.R.k : ℝ) * L.sc.b') := by ring
    have e4 : 4 * (D.R.k : ℝ) * L.sc.b' = 4 * ((D.R.k : ℝ) * L.sc.b') := by ring
    linarith

theorem szCt_of (hA : RowA) (hB : RowB) (hC : RowC) (hS : SizeFacts) (hP : PlaceFacts) :
    PI.SzCt.SzCt := by
  unfold PI.SzCt.SzCt
  intro eps Ct CGam Cc CT2 PK
  refine ⟨3, ?_⟩
  intro D L P _ hx hSz j hj u
  have hsum : ∑ t : HH D, ctD D u j t ≤
      ∑ t : HH D, ((if t ∈ D.host.TT then 2 * L.sc.b else 0) + 4 * (D.R.k : ℝ) * L.sc.b') :=
    Finset.sum_le_sum (fun t _ => ct_le hA hB hC hS hP D L P hx hSz j hj u t)
  refine le_trans hsum ?_
  obtain ⟨-, -, -, -, -, -, hb'0⟩ := hS D L hSz hx
  have hcard : Fintype.card (HH D) = D.R.n := by
    rw [Fintype.card_eq_nat_card]
    show Nat.card (Fin D.R.ord) = D.R.n
    simp [Nat.card_eq_fintype_card, Formalism.BasicNotions.Ranks.n]
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ, hcard]
  have hf : (D.R.f : ℝ) = 2 * (D.R.n : ℝ) := by
    unfold Formalism.BasicNotions.Ranks.f
    push_cast
    ring
  rw [hf]
  have e : (D.R.n : ℝ) * (4 * (D.R.k : ℝ) * L.sc.b') = 2 * (2 * (D.R.n : ℝ)) * (D.R.k : ℝ) * L.sc.b' := by
    ring
  have e2 : (D.host.TT.card : ℝ) * (2 * L.sc.b) = 2 * (D.host.TT.card : ℝ) * L.sc.b := by ring
  linarith

end PI.SzCt.UnitaryGroupMassFormula
