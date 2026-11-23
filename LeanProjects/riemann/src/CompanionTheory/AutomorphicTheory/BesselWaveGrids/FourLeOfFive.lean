import CompanionTheory.AutomorphicTheory.BesselWaveGrids.Bridge
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.NqMovedExample
import CompanionTheory.AutomorphicTheory.BesselWaveGrids.InterlacingGrids.ProgYInjective

namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Finset GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

noncomputable def gridY (P : M.Par) (l N : ℕ) : Finset ℝ := progY (2 - max (P.u l) (P.u' l)) (N * (2 * P.r + 1))

noncomputable def gridΛ (P : M.Par) (b : ℝ) (N : ℕ) : ℝ :=
  max 1 (Real.sqrt ((4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T'))))

theorem one_le_gridΛ (P : M.Par) (b : ℝ) (N : ℕ) : 1 ≤ gridΛ P b N := by
  unfold gridΛ
  exact le_max_left _ _

theorem gridΛ_sq (P : M.Par) (b : ℝ) (N : ℕ) (hb : 0 ≤ b) (hTT : 0 < P.T * P.T') :
    (4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T')) ≤ gridΛ P b N ^ 2 := by
  unfold gridΛ
  have hX : 0 ≤ (4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T')) :=
    mul_nonneg (pow_nonneg (by norm_num) _) (div_nonneg (pow_nonneg hb _) hTT.le)
  calc (4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T'))
      = Real.sqrt ((4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T'))) ^ 2 := (Real.sq_sqrt hX).symm
    _ ≤ max 1 (Real.sqrt ((4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T')))) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right _ _) 2

theorem gridΛ_le (P : M.Par) (b CT : ℝ) (N : ℕ) (hN : N ≤ 3 * (P.r + 1)) (hb : 3 ≤ b) (hCT : 0 ≤ CT)
    (hTT0 : 0 < P.T * P.T') (hTT : b ^ (-(CT * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T * P.T') :
    gridΛ P b N ≤ b ^ ((6 + CT) * ((2 * P.r + 2 : ℕ) : ℝ)) := by
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hr0 : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
  have hm' : (((2 * P.r + 2 : ℕ) : ℝ)) = 2 * (P.r : ℝ) + 2 := by push_cast; ring
  set m : ℝ := (((2 * P.r + 2 : ℕ) : ℝ)) with hm
  have hm0 : 0 ≤ m := by rw [hm']; linarith
  have hCm : 0 ≤ CT * m := mul_nonneg hCT hm0
  have hinv : (P.T * P.T')⁻¹ ≤ b ^ (CT * m) := by
    have h1 : 0 < b ^ (CT * m) := Real.rpow_pos_of_pos hb0 _
    rw [Real.rpow_neg hb0.le] at hTT
    exact (inv_le_comm₀ h1 hTT0).mp hTT
  have h43 : (4 / 3 : ℝ) ^ N ≤ b ^ (3 * (P.r + 1)) :=
    le_trans (pow_le_pow_left₀ (by norm_num) (by linarith) N) (pow_le_pow_right₀ hb1 hN)
  have hpow : b ^ (3 * (P.r + 1)) * b ^ (8 * P.r + 20) ≤ b ^ (12 * m) := by
    rw [← pow_add, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hb1
    rw [hm']
    push_cast
    linarith
  have hX : (4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T')) ≤ b ^ (12 * m) * b ^ (CT * m) := by
    rw [div_eq_mul_inv]
    calc (4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) * (P.T * P.T')⁻¹)
        ≤ b ^ (3 * (P.r + 1)) * (b ^ (8 * P.r + 20) * b ^ (CT * m)) :=
          mul_le_mul h43 (mul_le_mul_of_nonneg_left hinv (pow_nonneg hb0.le _))
            (mul_nonneg (pow_nonneg hb0.le _) (inv_nonneg.mpr hTT0.le)) (pow_nonneg hb0.le _)
      _ = (b ^ (3 * (P.r + 1)) * b ^ (8 * P.r + 20)) * b ^ (CT * m) := by ring
      _ ≤ b ^ (12 * m) * b ^ (CT * m) := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hb0.le _)
  have hy : (b ^ ((6 + CT) * m)) ^ 2 = b ^ (12 * m) * b ^ (2 * (CT * m)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb0.le, ← Real.rpow_add hb0]
    congr 1
    push_cast
    ring
  have hX' : (4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T')) ≤ (b ^ ((6 + CT) * m)) ^ 2 := by
    rw [hy]
    refine le_trans hX (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hb0.le _))
    exact Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
  unfold gridΛ
  refine max_le (Real.one_le_rpow hb1 (mul_nonneg (by linarith) hm0)) ?_
  calc Real.sqrt ((4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T')))
      ≤ Real.sqrt ((b ^ ((6 + CT) * m)) ^ 2) := Real.sqrt_le_sqrt hX'
    _ = b ^ ((6 + CT) * m) := Real.sqrt_sq (Real.rpow_nonneg hb0.le _)

theorem onCut_of_minmax (u u' : ℕ → ℝ) (l : ℕ) (Y : ℝ) (h1 : min (u l) (u' l) + 2 ≤ -Y)
    (h2 : -Y ≤ max (u l) (u' l) - 2) : I.OnCut u u' l Y := by
  unfold Formalism.FourierDecayAlt.I.OnCut
  rcases le_total (u l) (u' l) with h | h
  · left
    rw [min_eq_left h] at h1
    rw [max_eq_right h] at h2
    exact ⟨h1, h2⟩
  · right
    rw [min_eq_right h] at h1
    rw [max_eq_left h] at h2
    exact ⟨h1, h2⟩

section grid

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem gridY_cut (P : M.Par) (l N : ℕ) (hlen : 5 * ((N * (2 * P.r + 1) : ℕ) : ℝ) ≤ |P.u l - P.u' l|) :
    ∀ y ∈ gridY P l N, I.OnCut P.u P.u' l y ∧ I.OnCut P.u P.u' l (y + 1) := by
  intro y hy
  have hlen' : 5 * ((N * (2 * P.r + 1) : ℕ) : ℝ) ≤ max (P.u l) (P.u' l) - min (P.u l) (P.u' l) := by
    rw [max_sub_min_eq_abs, abs_sub_comm]
    exact hlen
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := progY_cut (min (P.u l) (P.u' l)) (max (P.u l) (P.u' l)) _ hlen' y hy
  exact ⟨onCut_of_minmax _ _ _ _ h1 h2, onCut_of_minmax _ _ _ _ h3 h4⟩

private theorem exists_ge_four_fifths_pow_qw_eq_mul_of_far_letters {S : Type} (q : ℂ → ℂ) (y : ℝ) :
    ∀ L : List (Formalism.FourierDecayAlt.Wd.Letter ℂ S),
      (∀ l ∈ L, ∃ d : ℝ, 5 ≤ |d| ∧ ((l.plus = true ∧ l.pt = ((y - d : ℝ) : ℂ)) ∨
        (l.plus = false ∧ l.pt = ((y - d + 1 : ℝ) : ℂ)))) →
      ∃ t : ℝ, (4 / 5 : ℝ) ^ L.length ≤ t ∧ Formalism.FourierDecayAlt.Wd.qw q L (y : ℂ) = (t : ℂ) * q (y : ℂ) := by
  intro L
  induction L with
  | nil =>
    intro _
    exact ⟨1, by simp, by simp [Formalism.FourierDecayAlt.Wd.qw]⟩
  | cons l L ih =>
    intro h
    obtain ⟨t, ht, heq⟩ := ih (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    obtain ⟨d, hd, hcase⟩ := h l (by simp)
    have ht0 : 0 ≤ t := le_trans (pow_nonneg (by norm_num) _) ht
    rcases hcase with ⟨hp, hpt⟩ | ⟨hp, hpt⟩
    · refine ⟨t * ((y - (y - d) + 1) / (y - (y - d))), ?_, ?_⟩
      · have e : (y - (y - d) + 1) / (y - (y - d)) = (d + 1) / d := by congr 1 <;> ring
        have hf : (4 / 5 : ℝ) ≤ (d + 1) / d := by
          rcases le_abs.mp hd with h5 | h5
          · rw [le_div_iff₀ (by linarith)]
            linarith
          · rw [le_div_iff_of_neg (by linarith)]
            linarith
        rw [e, List.length_cons, pow_succ]
        exact mul_le_mul ht hf (by norm_num) ht0
      · simp only [Formalism.FourierDecayAlt.Wd.qw, hp, if_true, heq, hpt]
        push_cast
        ring
    · refine ⟨t * ((y - d + 1 - y) / (y - d + 1 - y - 1)), ?_, ?_⟩
      · have e : (y - d + 1 - y) / (y - d + 1 - y - 1) = (1 - d) / (-d) := by congr 1 <;> ring
        have hf : (4 / 5 : ℝ) ≤ (1 - d) / (-d) := by
          rcases le_abs.mp hd with h5 | h5
          · rw [le_div_iff_of_neg (by linarith)]
            linarith
          · rw [le_div_iff₀ (by linarith)]
            linarith
        rw [e, List.length_cons, pow_succ]
        exact mul_le_mul ht hf (by norm_num) ht0
      · simp only [Formalism.FourierDecayAlt.Wd.qw, hp, Bool.false_eq_true, ↓reduceIte, heq, hpt]
        push_cast
        ring

theorem freeBound_text (p : KB.Pl P Wp Wq) (K N : ℕ) (lam : ℕ → ℝ) (c g b : ℝ) (hL : PairData P p.l0 lam c g b)
    (hlen : 5 * ((N * (2 * P.r + 1) : ℕ) : ℝ) ≤ |P.u p.l0 - P.u' p.l0|) :
    FreeBound p (Pst P.k P.r lam c) (gridY P p.l0 N) (gridΛ P b N) K N := by
  have hOK : P.OK := p.hP.1
  obtain ⟨hl1, hl2, hk2⟩ := p.hl
  have hTT : 0 < P.T * P.T' := mul_pos hOK.T_pos hOK.T'_pos
  have hb : 0 ≤ b := by linarith [hL.b_ge_three]
  have hc := hL.c_pos
  have hPst : ∀ Y : ℝ, 0 < GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst P.k P.r lam c Y := by
    intro Y
    unfold GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst
    exact Finset.prod_pos (fun s _ => add_pos_of_nonneg_of_pos (abs_nonneg _) hc)
  have hY := gridY_cut P p.l0 N hlen
  have hsep := progY_sep (2 - max (P.u p.l0) (P.u' p.l0)) (N * (2 * P.r + 1))
  intro w _ hwlen y hy hlet
  have hlet' : ∀ l ∈ Formalism.FourierDecayAlt.D.positionted w, ∃ d : ℝ, 5 ≤ |d| ∧ ((l.plus = true ∧ l.pt = ((y - d : ℝ) : ℂ)) ∨
      (l.plus = false ∧ l.pt = ((y - d + 1 : ℝ) : ℂ))) := by
    intro l hl
    unfold Formalism.FourierDecayAlt.D.positionted at hl
    rw [List.mem_ofFn] at hl
    obtain ⟨a, rfl⟩ := hl
    obtain ⟨y', hy', hne, hcase⟩ := hlet (w.get a) (by simp [List.get_eq_getElem])
    refine ⟨y - y', hsep y hy y' hy' (Ne.symm hne), ?_⟩
    rcases hcase with h | h
    · left
      refine ⟨by show (w.get a).1 = true; rw [h], ?_⟩
      simp only [h]
      push_cast
      ring
    · right
      refine ⟨by show (w.get a).1 = false; rw [h], ?_⟩
      simp only [h]
      push_cast
      ring
  obtain ⟨t, ht, heq⟩ := exists_ge_four_fifths_pow_qw_eq_mul_of_far_letters (Formalism.FourierDecayAlt.M.qC P) y _ hlet'
  have hls : (Formalism.FourierDecayAlt.D.positionted w).length = w.length := by
    unfold Formalism.FourierDecayAlt.D.positionted
    simp
  rw [hls] at ht
  have hq := nq_onCut_pair P hOK p.l0 hl1 hl2 hk2 lam c g b hL y (hY y hy).1
  have hre : (Formalism.FourierDecayAlt.Wd.qw (Formalism.FourierDecayAlt.M.qC P) (Formalism.FourierDecayAlt.D.positionted w) (y : ℂ)).re
      = t * (Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re := by
    rw [heq, Complex.re_ofReal_mul]
  have ht0 : 0 < t := lt_of_lt_of_le (pow_pos (by norm_num) _) ht
  refine ⟨⟨hPst y, hPst (y + 1), by rw [hre]; exact mul_pos ht0 hq.1⟩, ?_⟩
  rw [hre]
  have hsq := gridΛ_sq P b N hb hTT
  have h1 : 1 ≤ (4 / 3 : ℝ) ^ N * t := by
    calc (1 : ℝ) ≤ ((4 / 3 : ℝ) * (4 / 5)) ^ w.length := one_le_pow₀ (by norm_num)
      _ = (4 / 3 : ℝ) ^ w.length * (4 / 5) ^ w.length := mul_pow _ _ _
      _ ≤ (4 / 3 : ℝ) ^ N * t :=
        mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega)) ht (by positivity) (by positivity)
  have hR0 : 0 ≤ b ^ (8 * P.r + 20) / (P.T * P.T') * (Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re :=
    mul_nonneg (div_nonneg (pow_nonneg hb _) hTT.le) hq.1.le
  calc GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst P.k P.r lam c y
        * GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid.Pst P.k P.r lam c (y + 1)
      ≤ b ^ (8 * P.r + 20) / (P.T * P.T') * (Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re := hq.2
    _ ≤ b ^ (8 * P.r + 20) / (P.T * P.T') * (Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re * ((4 / 3 : ℝ) ^ N * t) :=
        le_mul_of_one_le_right hR0 h1
    _ = ((4 / 3 : ℝ) ^ N * (b ^ (8 * P.r + 20) / (P.T * P.T'))) * (t * (Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re) := by ring
    _ ≤ gridΛ P b N ^ 2 * (t * (Formalism.FourierDecayAlt.M.qC P (y : ℂ)).re) :=
        mul_le_mul_of_nonneg_right hsq (mul_pos ht0 hq.1).le

theorem grids_text (p : KB.Pl P Wp Wq) (K N : ℕ) (hKN : K ≤ N) (lam : ℕ → ℝ) (c g b : ℝ)
    (hL : PairData P p.l0 lam c g b) (hlen : 5 * ((N * (2 * P.r + 1) : ℕ) : ℝ) ≤ |P.u p.l0 - P.u' p.l0|) :
    TBBx5.WaveGrid p (Pst P.k P.r lam c) (gridY P p.l0 N) (gridΛ P b N) K N ∧
      TBBx5.LiftGrid p (Pst P.k P.r lam c) (gridY P p.l0 N) (gridΛ P b N) K N := by
  have hY := gridY_cut P p.l0 N hlen
  have hsep := progY_sep (2 - max (P.u p.l0) (P.u' p.l0)) (N * (2 * P.r + 1))
  have hcard : N - K + K * (2 * P.r + 1) ≤ (gridY P p.l0 N).card := by
    unfold gridY
    rw [progY_card]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hKN
    rw [Nat.add_sub_cancel_left]
    nlinarith [Nat.zero_le (j * P.r)]
  have hF := freeBound_text p K N lam c g b hL hlen
  have hB : 0 ≤ gridΛ P b N := le_trans zero_le_one (one_le_gridΛ P b N)
  exact ⟨waveGrid_of_sep p _ _ _ K N hB hY hsep hcard hF, liftGrid_of_sep p _ _ _ K N hB hY hsep hcard hF⟩

end grid

end CompanionTheory.WaveGrid
