import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.DataParamsT
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.Columns.LocWLemmas

noncomputable section

namespace Formalism.BasicNotions

namespace RowWeightLemmas

theorem nuRow_head (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r : ℕ) (hr : r < D.R.k) :
    DV.nuRow D u (i + 1) τ r = (((D.hcW u τ).u ⟨r, hr⟩ + (D.hcW u τ).e ⟨i, hi⟩ -
      (2 * (D.R.N i : ℚ) + D.R.t - 2 * r) / 2 : ℚ) : ℝ) := by
  have hw : 1 ≤ i + 1 ∧ i + 1 ≤ D.R.m := ⟨by omega, by omega⟩
  unfold DV.nuRow DV.srcPar DV.wSz
  rw [dif_pos hr, dif_pos hw, ← D.hcW_e u τ]
  simp only [Nat.add_sub_cancel, Ranks.N]
  push_cast
  ring

theorem nuRow_block (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (q s : ℕ) (hq : q < i)
    (hs : s < D.R.t + 1) :
    DV.nuRow D u (i + 1) τ (D.R.k + q * (D.R.t + 1) + s) = (((D.hcW u τ).e ⟨i, hi⟩ - (D.hcW u τ).e ⟨q, by omega⟩ -
      ((i : ℚ) - q) * ((D.R.t : ℚ) + 1) : ℚ) : ℝ) := by
  have hw : 1 ≤ i + 1 ∧ i + 1 ≤ D.R.m := ⟨by omega, by omega⟩
  have hk : ¬ D.R.k + q * (D.R.t + 1) + s < D.R.k := by omega
  have h1 : D.R.k + q * (D.R.t + 1) + s - D.R.k = s + (D.R.t + 1) * q := by
    rw [Nat.mul_comm]; omega
  have hdiv : (D.R.k + q * (D.R.t + 1) + s - D.R.k) / (D.R.t + 1) = q := by
    rw [h1, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hs, Nat.zero_add]
  have hmod : (D.R.k + q * (D.R.t + 1) + s - D.R.k) % (D.R.t + 1) = s := by
    rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  unfold DV.nuRow DV.srcPar DV.wSz
  rw [dif_neg hk, dif_pos hw, ← D.hcW_e u τ]
  simp only [hdiv, hmod, Nat.add_sub_cancel, Ranks.N]
  rw [dif_pos (by omega : q < D.R.m)]
  push_cast
  ring

theorem block_decomp (R : Ranks) (i r : ℕ) (hk : R.k ≤ r) (hr : r < R.N i) :
    ∃ q s, q < i ∧ s < R.t + 1 ∧ r = R.k + q * (R.t + 1) + s := by
  refine ⟨(r - R.k) / (R.t + 1), (r - R.k) % (R.t + 1), ?_, Nat.mod_lt _ (by omega), ?_⟩
  · rw [Nat.div_lt_iff_lt_mul (by omega)]
    unfold Ranks.N at hr
    omega
  · have := Nat.div_add_mod (r - R.k) (R.t + 1)
    rw [Nat.mul_comm] at this
    omega

theorem e_step {R : Ranks} (P : HCParam R) (q : ℕ) (h : q + 1 < R.m) :
    (R.t : ℚ) + 3 ≤ P.e ⟨q + 1, h⟩ - P.e ⟨q, by omega⟩ := by
  have h1 := P.gap_eb ⟨q, by omega⟩ h
  have h2 := P.gap_be ⟨q + 1, h⟩
  linarith

theorem u_step {R : Ranks} (P : HCParam R) (r : ℕ) (h : r + 1 < R.k) :
    1 ≤ P.u ⟨r, by omega⟩ - P.u ⟨r + 1, h⟩ := by
  have h1 := P.u_gt_v ⟨r, by omega⟩
  have h2 := P.v_gt_u ⟨r, by omega⟩
  obtain ⟨a, ha⟩ := P.u_half ⟨r, by omega⟩
  obtain ⟨b, hb⟩ := P.u_half ⟨r + 1, h⟩
  simp only at h1 h2
  have hlt : P.u ⟨r + 1, h⟩ < P.u ⟨r, by omega⟩ := lt_trans h2 h1
  rw [ha, hb] at hlt ⊢
  have hab : (b : ℚ) < a := by linarith
  have hab' : b + 1 ≤ a := by exact_mod_cast hab
  have : (b : ℚ) + 1 ≤ a := by exact_mod_cast hab'
  linarith

theorem nuRow_int (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r : ℕ) (hr : r < D.R.N i) :
    ∃ z : ℤ, DV.nuRow D u (i + 1) τ r = z := by
  by_cases hk : r < D.R.k
  · obtain ⟨a, ha⟩ := (D.hcW u τ).u_half ⟨r, hk⟩
    obtain ⟨b, hb⟩ := (D.hcW u τ).e_int ⟨i, hi⟩
    obtain ⟨c, hc⟩ := D.R.t_odd
    refine ⟨a + b - (D.R.N i + c - r), ?_⟩
    rw [nuRow_head D u i hi τ r hk, ha, hb, hc]
    push_cast
    ring
  · obtain ⟨q, s, hq, hs, rfl⟩ := block_decomp D.R i r (by omega) hr
    obtain ⟨a, ha⟩ := (D.hcW u τ).e_int ⟨q, by omega⟩
    obtain ⟨b, hb⟩ := (D.hcW u τ).e_int ⟨i, hi⟩
    refine ⟨b - a - ((i : ℤ) - q) * ((D.R.t : ℤ) + 1), ?_⟩
    rw [nuRow_block D u i hi τ q s hq hs, ha, hb]
    push_cast
    ring

theorem nuRow_anti (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r : ℕ) (hr : r + 1 < D.R.N i) :
    DV.nuRow D u (i + 1) τ (r + 1) ≤ DV.nuRow D u (i + 1) τ r := by
  by_cases hk : r + 1 < D.R.k
  · rw [nuRow_head D u i hi τ r (by omega), nuRow_head D u i hi τ (r + 1) hk]
    have := u_step (D.hcW u τ) r hk
    have h2 : (D.hcW u τ).u ⟨r + 1, hk⟩ + (D.hcW u τ).e ⟨i, hi⟩ - (2 * (D.R.N i : ℚ) + D.R.t - 2 * ((r + 1 : ℕ) : ℚ)) / 2 ≤
        (D.hcW u τ).u ⟨r, by omega⟩ + (D.hcW u τ).e ⟨i, hi⟩ - (2 * (D.R.N i : ℚ) + D.R.t - 2 * (r : ℚ)) / 2 := by
      push_cast
      linarith
    exact_mod_cast h2
  · by_cases hk' : r < D.R.k
    ·
      have hrk : r = D.R.k - 1 := by omega
      have hi0 : 0 < i := by
        rcases Nat.eq_zero_or_pos i with h | h
        · subst h; unfold Ranks.N at hr; omega
        · exact h
      have hr1 : r + 1 = D.R.k + 0 * (D.R.t + 1) + 0 := by omega
      rw [hr1, nuRow_block D u i hi τ 0 0 hi0 (by omega), nuRow_head D u i hi τ r hk']
      have h1 := (D.hcW u τ).u_last_gt (by omega) (by omega)
      have h2 := (D.hcW u τ).gap_be ⟨0, by omega⟩
      have hu : (D.hcW u τ).u ⟨r, hk'⟩ = (D.hcW u τ).u ⟨D.R.k - 1, by omega⟩ := by
        congr 1; exact Fin.ext hrk
      have hrq : (r : ℚ) = (D.R.k : ℚ) - 1 := by
        have : r + 1 = D.R.k := by omega
        have h' : ((r + 1 : ℕ) : ℚ) = D.R.k := by rw [this]
        push_cast at h'
        linarith
      have h3 : (D.hcW u τ).e ⟨i, hi⟩ - (D.hcW u τ).e ⟨0, by omega⟩ - ((i : ℚ) - (0 : ℕ)) * ((D.R.t : ℚ) + 1) ≤
          (D.hcW u τ).u ⟨r, hk'⟩ + (D.hcW u τ).e ⟨i, hi⟩ - (2 * (D.R.N i : ℚ) + D.R.t - 2 * (r : ℚ)) / 2 := by
        rw [hu, hrq]
        unfold Ranks.N
        push_cast
        linarith
      exact_mod_cast h3
    · obtain ⟨q, s, hq, hs, rfl⟩ := block_decomp D.R i r (by omega) (by omega)
      by_cases hs' : s + 1 < D.R.t + 1
      · rw [Nat.add_assoc, nuRow_block D u i hi τ q (s + 1) hq hs', nuRow_block D u i hi τ q s hq hs]
      · have hs1 : s = D.R.t := by omega
        have hq1 : q + 1 < i := by
          by_contra hcon
          have : q + 1 = i := by omega
          subst this
          unfold Ranks.N at hr
          rw [Nat.add_mul] at hr
          omega
        have hr1 : D.R.k + q * (D.R.t + 1) + s + 1 = D.R.k + (q + 1) * (D.R.t + 1) + 0 := by
          rw [Nat.add_mul]; omega
        rw [hr1, nuRow_block D u i hi τ (q + 1) 0 hq1 (by omega), nuRow_block D u i hi τ q s hq hs]
        have h1 := e_step (D.hcW u τ) q (by omega)
        have h3 : (D.hcW u τ).e ⟨i, hi⟩ - (D.hcW u τ).e ⟨q + 1, by omega⟩ - ((i : ℚ) - ((q + 1 : ℕ) : ℚ)) * ((D.R.t : ℚ) + 1) ≤
            (D.hcW u τ).e ⟨i, hi⟩ - (D.hcW u τ).e ⟨q, by omega⟩ - ((i : ℚ) - (q : ℚ)) * ((D.R.t : ℚ) + 1) := by
          push_cast
          linarith
        exact_mod_cast h3

theorem nuRow_last_pos (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) :
    0 < DV.nuRow D u (i + 1) τ (D.R.N i - 1) := by
  have hkpos : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    have hN : D.R.N 0 - 1 = D.R.k - 1 := by unfold Ranks.N; omega
    rw [hN, nuRow_head D u 0 hi τ (D.R.k - 1) (by omega)]
    have h1 := (D.hcW u τ).u_last_gt (by omega) (by omega)
    have h2 := (D.hcW u τ).gap_be ⟨0, by omega⟩
    have hrq : ((D.R.k - 1 : ℕ) : ℚ) = (D.R.k : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have h3 : (0 : ℚ) < (D.hcW u τ).u ⟨D.R.k - 1, by omega⟩ + (D.hcW u τ).e ⟨0, hi⟩ -
        (2 * (D.R.N 0 : ℚ) + D.R.t - 2 * ((D.R.k - 1 : ℕ) : ℚ)) / 2 := by
      rw [hrq]
      unfold Ranks.N
      push_cast
      linarith
    exact_mod_cast h3
  · obtain ⟨q, rfl⟩ : ∃ q, i = q + 1 := ⟨i - 1, by omega⟩
    have hN : D.R.N (q + 1) - 1 = D.R.k + q * (D.R.t + 1) + D.R.t := by
      unfold Ranks.N; rw [Nat.add_mul]; omega
    rw [hN, nuRow_block D u (q + 1) hi τ q D.R.t (by omega) (by omega)]
    have h1 := e_step (D.hcW u τ) q hi
    have h3 : (0 : ℚ) < (D.hcW u τ).e ⟨q + 1, hi⟩ - (D.hcW u τ).e ⟨q, by omega⟩ -
        (((q + 1 : ℕ) : ℚ) - (q : ℚ)) * ((D.R.t : ℚ) + 1) := by
      push_cast
      linarith
    exact_mod_cast h3

theorem nuRow_anti' (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r r' : ℕ) (h : r' ≤ r)
    (hr : r < D.R.N i) : DV.nuRow D u (i + 1) τ r ≤ DV.nuRow D u (i + 1) τ r' := by
  induction r, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih => exact le_trans (nuRow_anti D u i hi τ n hr) (ih (by omega))

theorem nuRow_pos (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r : ℕ) (hr : r < D.R.N i) :
    0 < DV.nuRow D u (i + 1) τ r :=
  lt_of_lt_of_le (nuRow_last_pos D u i hi τ) (nuRow_anti' D u i hi τ (D.R.N i - 1) r (by omega) (by omega))

end RowWeightLemmas

theorem nuRow_nat (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i < D.R.m) (τ : D.what₂.Tau) (r : ℕ) (hr : r < D.R.N i) :
    ∃ n : ℕ, 1 ≤ n ∧ DV.nuRow D u (i + 1) τ r = n := by
  obtain ⟨z, hz⟩ := RowWeightLemmas.nuRow_int D u i hi τ r hr
  have hpos := RowWeightLemmas.nuRow_pos D u i hi τ r hr
  rw [hz] at hpos
  have hz0 : 0 < z := by exact_mod_cast hpos
  refine ⟨z.toNat, by omega, ?_⟩
  rw [hz]
  have : ((z.toNat : ℤ) : ℝ) = (z : ℝ) := by rw [Int.toNat_of_nonneg hz0.le]
  exact_mod_cast this.symm

theorem nuRowOK (D : D7) : NuRowOK D := by
  intro u i hi z r
  by_cases hr : r < D.R.N i
  · rw [if_pos hr]
    obtain ⟨n, _, hn⟩ := nuRow_nat D u i hi (tauPl D z) r hr
    rw [hn]
    have key : ∀ c : ℕ, c < (nuD D u i z).rowLen r ↔ c < n := by
      intro c
      rw [← YoungDiagram.mem_iff_lt_rowLen, ← YoungDiagram.mem_cells]
      simp only [nuD, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      constructor
      · rintro ⟨_, h⟩
        have := h r le_rfl
        rw [hn] at this
        exact_mod_cast this
      · intro hc
        have hc' : (c : ℝ) < DV.nuRow D u (i + 1) (tauPl D z) r := by rw [hn]; exact_mod_cast hc
        have hall : ∀ r' ≤ r, (c : ℝ) < DV.nuRow D u (i + 1) (tauPl D z) r' := fun r' hr' =>
          lt_of_lt_of_le hc' (RowWeightLemmas.nuRow_anti' D u i hi (tauPl D z) r r' hr' hr)
        exact ⟨⟨hr, Nat.lt_ceil.2 (hall 0 (Nat.zero_le _))⟩, hall⟩
    have : (nuD D u i z).rowLen r = n :=
      le_antisymm (not_lt.1 fun h => lt_irrefl _ ((key n).1 h)) (not_lt.1 fun h => lt_irrefl _ ((key _).2 h))
    rw [this]
  · rw [if_neg hr]
    have : (nuD D u i z).rowLen r = 0 := by
      by_contra hne
      have hmem : (r, 0) ∈ nuD D u i z := YoungDiagram.mem_iff_lt_rowLen.2 (Nat.pos_of_ne_zero hne)
      have h2 : (r, 0) ∈ (nuD D u i z).cells := hmem
      simp only [nuD, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at h2
      exact hr h2.1.1
    rw [this]; simp

end Formalism.BasicNotions

namespace Formalism.BasicNotions

open NumberField LevelStarExponents

theorem logdE_eq_rd (D : D7) : logdE D = 2 * (D.R.f : ℝ) * Real.log D.host.rdE := by
  have h0 : (0 : ℝ) < |((discr D.host.E : ℤ) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero D.host.E)
  have hfr : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    push_cast
    ring
  have hf : (0 : ℝ) < 2 * (D.R.f : ℝ) := by
    rw [← hfr]; exact_mod_cast Module.finrank_pos
  unfold logdE Host.rdE
  rw [Real.log_rpow h0, hfr]
  have hf' : (D.R.f : ℝ) ≠ 0 := by intro h; rw [h] at hf; simp at hf
  field_simp

theorem rdE_pos_le (D : D7) :
    0 < D.host.rdE ∧ D.host.rdE ≤ (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) := by
  have hd : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  obtain ⟨h1, h2, -⟩ := factRd D.R D.host
  exact ⟨lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.sqrt_pos.2 hd)) h1, h2⟩

theorem log_rdE_le_scL {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) : Real.log D.host.rdE ≤ L.sc.L := by
  have hL0 : 0 < L.sc.L := by unfold Scale.L; exact Real.rpow_pos_of_pos (by linarith [L.sc.one_lt_alt]) _
  have hq : (2 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.two_le
  have hd : (2 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.two_le
  have ht1 : (1 : ℝ) ≤ D.R.t := by
    have : 1 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
    exact_mod_cast this
  have hb1 : 1 ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp hL0.le
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d :=
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  obtain ⟨hpos, hle⟩ := rdE_pos_le D
  have hcE : ((condE D : ℕ) : ℝ) = (D.host.QS : ℝ) * D.host.q * D.host.d := by unfold condE; push_cast; ring
  have hc : D.host.rdE ≤ (condE D : ℝ) := by
    refine hle.trans ?_
    rw [hcE]
    have hQ : (0 : ℝ) ≤ D.host.QS := Nat.cast_nonneg _
    have h1 : (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
        (D.host.QS : ℝ) / 2 * ((D.host.q : ℝ) * D.host.d) := mul_le_mul_of_nonneg_left hs (by linarith)
    have h2 : 0 ≤ (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := mul_nonneg hQ (by linarith)
    nlinarith
  have hc1 : (1 : ℝ) ≤ (condE D : ℝ) := by
    have h0 : (0 : ℝ) < (condE D : ℝ) := hpos.trans_le hc
    have h1 : 0 < condE D := by exact_mod_cast h0
    exact_mod_cast h1
  have h36 : (condE D : ℝ) ≤ (condE D : ℝ) ^ 36 := le_self_pow₀ hc1 (by norm_num)
  have h150 : (condE D : ℝ) ^ 36 ≤ (condE D : ℝ) ^ 36 * (D.R.t : ℝ) ^ 150 :=
    le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1)
  have hsb : L.sc.b ^ ((1 : ℝ) / 2) ≤ L.sc.b := by
    calc L.sc.b ^ ((1 : ℝ) / 2) ≤ L.sc.b ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num)
      _ = L.sc.b := Real.rpow_one _
  have hfin : D.host.rdE ≤ L.sc.b := hc.trans (h36.trans (h150.trans (P.condE_le.trans hsb)))
  have := Real.log_le_log hpos hfin
  rwa [show Real.log L.sc.b = L.sc.L by unfold Scale.b; exact Real.log_exp _] at this

theorem logdE_le_two_f_L {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) :
    logdE D ≤ 2 * (D.R.f : ℝ) * L.sc.L := by
  rw [logdE_eq_rd]
  exact mul_le_mul_of_nonneg_left (log_rdE_le_scL P) (by positivity)

end Formalism.BasicNotions

namespace Formalism.BasicNotions.SkeletonIndexLemmas

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Formalism.L2.Col

section Gen

variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

theorem coe_ne_zero_of_not_mem (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) : (s : K) ≠ 0 := by
  intro h
  have : s = 0 := by exact_mod_cast h
  exact hs (this ▸ w.asIdeal.zero_mem)

theorem lidx_congr (w : HeightOneSpectrum (𝓞 K)) {A A' B B' : Submodule (𝓞 K) V}
    (hA : localization₂ w.asIdeal A = localization₂ w.asIdeal A') (hB : localization₂ w.asIdeal B = localization₂ w.asIdeal B') :
    lidx w.asIdeal A B = lidx w.asIdeal A' B' := by
  have h1 : localization₂ w.asIdeal (A ⊓ B) = localization₂ w.asIdeal (A' ⊓ B') := by
    unfold localization₂ at *
    rw [locBasic_locS_inf, locBasic_locS_inf, hA, hB]
  unfold lidx locLen
  rw [hA, hB, h1]

theorem localization_map₂ (w : HeightOneSpectrum (𝓞 K)) (f : V →ₗ[K] V') (L : Submodule (𝓞 K) V) :
    localization₂ w.asIdeal (L.map (f.restrictScalars (𝓞 K))) = (localization₂ w.asIdeal L).map (f.restrictScalars (𝓞 K)) := by
  ext y
  constructor
  · rintro ⟨s, hs, x, hx, hxy⟩
    have hs0 : (s : K) ≠ 0 := coe_ne_zero_of_not_mem w hs
    refine ⟨(s : K)⁻¹ • x, ⟨s, hs, ?_⟩, ?_⟩
    · rw [← algebraMap_smul K s, smul_smul]
      change ((s : K) * (s : K)⁻¹) • x ∈ L
      rw [mul_inv_cancel₀ hs0, one_smul]; exact hx
    · have h2 : f x = (s : K) • y := by
        have : f x = s • y := hxy
        rw [this, ← algebraMap_smul K s]
      change f ((s : K)⁻¹ • x) = y
      rw [map_smul, h2, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  · rintro ⟨x, ⟨s, hs, hx⟩, rfl⟩
    exact ⟨s, hs, s • x, hx, by simp⟩

theorem locLen_map (w : HeightOneSpectrum (𝓞 K)) (f : V →ₗ[K] V') (hf : Function.Injective f)
    (A C : Submodule (𝓞 K) V) :
    locLen w.asIdeal (A.map (f.restrictScalars (𝓞 K))) (C.map (f.restrictScalars (𝓞 K))) = locLen w.asIdeal A C := by
  unfold locLen
  rw [localization_map₂, localization_map₂]
  congr 1
  refine (LinearEquiv.length_eq (Submodule.Quotient.equiv _ _
    (Submodule.equivMapOfInjective (f.restrictScalars (𝓞 K)) hf (localization₂ w.asIdeal A)) ?_)).symm
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, hx, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    obtain ⟨x, hx, hxy⟩ := y.2
    have hxz : z = x := hf (hzy.trans hxy.symm)
    subst hxz
    exact ⟨⟨z, hx⟩, hz, Subtype.ext hzy⟩

theorem lidx_map (w : HeightOneSpectrum (𝓞 K)) (f : V →ₗ[K] V') (hf : Function.Injective f)
    (A B : Submodule (𝓞 K) V) :
    lidx w.asIdeal (A.map (f.restrictScalars (𝓞 K))) (B.map (f.restrictScalars (𝓞 K))) = lidx w.asIdeal A B := by
  unfold lidx
  rw [← Submodule.map_inf (f.restrictScalars (𝓞 K)) hf, locLen_map w f hf, locLen_map w f hf]

abbrev latOf {ι : Type} (b : ι → V) : Submodule (𝓞 K) V := Submodule.span (𝓞 K) (Set.range b)

theorem span_latOf {ι : Type} (b : ι → V) :
    Submodule.span K ((latOf (K := K) b : Submodule (𝓞 K) V) : Set V) = Submodule.span K (Set.range b) :=
  Submodule.span_span_of_tower _ _ _

def famOf {ι : Type} [Fintype ι] (b : ι → V) (M : Matrix ι ι K) : ι → V := fun i => ∑ k, M k i • b k

theorem lidx_latOf (w : HeightOneSpectrum (𝓞 K)) {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → V)
    (hb : LinearIndependent K b) (M : Matrix ι ι K) (hM : M.det ≠ 0) :
    lidx w.asIdeal (latOf (K := K) b) (latOf (K := K) (famOf b M)) = vAdd w M.det := by
  have hinj : Function.Injective (Fintype.linearCombination K b) :=
    linearIndependent_iff_injective_fintypeLinearCombination.1 hb
  let e : ι → (ι → K) := fun i => Pi.single i 1
  have hfe : ∀ v : ι → K, Fintype.linearCombination K b v = ∑ k, v k • b k := fun v => rfl
  have hMu : IsUnit M.det := isUnit_iff_ne_zero.2 hM
  let γ : (ι → K) ≃ₗ[K] (ι → K) := Matrix.toLinearEquiv' M (Matrix.invertibleOfIsUnitDet M hMu)
  have hγ : ∀ v, γ v = M.mulVec v := fun v => rfl
  have h1 : (latOf (K := K) e).map ((Fintype.linearCombination K b).restrictScalars (𝓞 K)) = latOf (K := K) b := by
    unfold latOf
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    change Fintype.linearCombination K b (Pi.single i 1) = b i
    rw [hfe]
    simp [Pi.single_apply]
  have h2 : ((latOf (K := K) e).map ((γ : (ι → K) →ₗ[K] (ι → K)).restrictScalars (𝓞 K))).map
      ((Fintype.linearCombination K b).restrictScalars (𝓞 K)) = latOf (K := K) (famOf b M) := by
    unfold latOf
    rw [Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
    congr 2
    funext i
    change Fintype.linearCombination K b (γ (Pi.single i 1)) = famOf b M i
    rw [hfe, hγ]
    unfold famOf
    simp
  have hlat : Submodule.IsLattice K (latOf (K := K) e) :=
    { fg := Submodule.fg_span (Set.finite_range e)
      span_eq_top := by
        rw [span_latOf]
        have := (Pi.basisFun K ι).span_eq
        have he : (⇑(Pi.basisFun K ι)) = e := by funext i; simp [e]
        rwa [he] at this }
  rw [← h1, ← h2, lidx_map w _ hinj,
    Formalism.L2.Col.bridge_lidx_det_holds K (ι → K) w (latOf (K := K) e) _ γ hlat rfl]
  congr 1
  change LinearMap.det (Matrix.toLin' M) = M.det
  exact LinearMap.det_toLin' M

theorem exists_basis_locP (w : HeightOneSpectrum (𝓞 K)) {A : Submodule (𝓞 K) V} (hfg : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) {n : ℕ} (hn : Module.finrank K V = n) :
    ∃ bK : Module.Basis (Fin n) K V, localization₂ w.asIdeal (latOf (K := K) bK) = localization₂ w.asIdeal A := by
  obtain ⟨ι, _, b, bK, hb⟩ := Formalism.L2.Col.exists_basis_atW w hfg hsp
  have hcard : Fintype.card ι = n := by rw [← hn]; exact (Module.finrank_eq_card_basis bK).symm
  refine ⟨bK.reindex (Fintype.equivFinOfCardEq hcard), ?_⟩
  have hr : Set.range (bK.reindex (Fintype.equivFinOfCardEq hcard)) = Set.range bK := Module.Basis.range_reindex _ _
  unfold latOf
  rw [hr, ← Formalism.L2.Col.atW_restrictScalars, ← Formalism.L2.Col.atW_restrictScalars]
  congr 1
  unfold Formalism.L2.Col.atW
  rw [Submodule.span_span_of_tower]
  have h1 : Set.range bK = (Formalism.L2.Col.atW w A).subtype '' Set.range b := by
    rw [← Set.range_comp]; congr 1; funext i; exact hb i
  rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  rfl

theorem exists_fam_locP (w : HeightOneSpectrum (𝓞 K)) {A : Submodule (𝓞 K) V} (hfg : A.FG) :
    ∃ a : Fin (Module.finrank K (Submodule.span K (A : Set V))) → V,
      LinearIndependent K a ∧ localization₂ w.asIdeal (latOf (K := K) a) = localization₂ w.asIdeal A := by
  set W : Submodule K V := Submodule.span K (A : Set V) with hW
  let A' : Submodule (𝓞 K) W := A.comap (W.subtype.restrictScalars (𝓞 K))
  have hmap : A'.map (W.subtype.restrictScalars (𝓞 K)) = A := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩; exact hx
    · intro x hx; exact ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩
  have hfg' : A'.FG :=
    Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars (𝓞 K)) Subtype.val_injective (hmap ▸ hfg)
  have hsp' : Submodule.span K (A' : Set W) = ⊤ := by
    apply Submodule.map_injective_of_injective (f := W.subtype) Subtype.val_injective
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    have : (W.subtype '' (A' : Set W)) = (A : Set V) := by
      have := congrArg (fun S : Submodule (𝓞 K) V => (S : Set V)) hmap
      simpa using this
    rw [this]
  obtain ⟨bK, hbK⟩ := exists_basis_locP w hfg' hsp' rfl
  refine ⟨fun i => (bK i : V), bK.linearIndependent.map' W.subtype (Submodule.ker_subtype _), ?_⟩
  have h1 : latOf (K := K) (fun i => (bK i : V)) = (latOf (K := K) bK).map (W.subtype.restrictScalars (𝓞 K)) := by
    unfold latOf
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [h1, localization_map₂, hbK, ← localization_map₂, hmap]

theorem famOf_famOf {ι : Type} [Fintype ι] (b : ι → V) (Q Z : Matrix ι ι K) :
    famOf (famOf b Q) Z = famOf b (Q * Z) := by
  funext i
  unfold famOf
  simp only [Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

theorem det_ne_zero_of_li {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → V) (M : Matrix ι ι K)
    (h : LinearIndependent K (famOf b M)) : M.det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hy : ∑ i, v i • famOf b M i = 0 := by
    unfold famOf
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.sum_smul]
    have : ∑ i, v i * M k i = (M.mulVec v) k := by
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [this, hMv]; simp
  exact hv (funext fun i => Fintype.linearIndependent_iff.1 h v hy i)

theorem vAdd_mul (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul ((map_ne_zero _).2 hx) ((map_ne_zero _).2 hy)]
  ring

theorem li_of_semilinear {M : Type} [AddCommGroup M] [Module ℂ M] {σ : K →+* ℂ} (e : V →ₛₗ[σ] M) {ι : Type}
    [Fintype ι] (v : ι → V) (h : LinearIndependent ℂ (fun i => e (v i))) : LinearIndependent K v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h1 : ∑ i, σ (g i) • e (v i) = 0 := by
    have := congrArg e hg
    rw [map_sum, map_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ]
  have := Fintype.linearIndependent_iff.1 h _ h1 i
  exact (map_eq_zero σ).1 this

end Gen

end Formalism.BasicNotions.SkeletonIndexLemmas

namespace Formalism.BasicNotions.SkeletonIndexLemmas

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory

section Herm

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def IsStarPl (w w' : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ x y : 𝓞 K, (y : K) = star (x : K) → (x ∈ w'.asIdeal ↔ y ∈ w.asIdeal)

theorem IsStarPl.symm {w w' : HeightOneSpectrum (𝓞 K)} (h : IsStarPl w w') : IsStarPl w' w :=
  fun x y hxy => (h y x (by rw [hxy, star_star])).symm

theorem h_smul_left (h : V →ₗ⋆[K] V →ₗ[K] K) (t : 𝓞 K) (x y : V) : h (t • x) y = star (t : K) * h x y := by
  rw [← algebraMap_smul K t x, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]; rfl

theorem h_smul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (t : 𝓞 K) (x y : V) : h x (t • y) = (t : K) * h x y := by
  rw [← algebraMap_smul K t y, map_smul, smul_eq_mul]

theorem vAdd_inv (w : HeightOneSpectrum (𝓞 K)) (x : K) : vAdd w x⁻¹ = - vAdd w x := by
  unfold vAdd
  rw [map_inv₀, WithZero.log_inv]

theorem localization_eq_of_semilocalization_eq (w : HeightOneSpectrum (𝓞 K)) {X Y : Submodule (𝓞 K) V}
    (h : loc (K := K) w.asIdeal X = loc (K := K) w.asIdeal Y) : localization₂ w.asIdeal X = localization₂ w.asIdeal Y := by
  have key : ∀ Z : Submodule (𝓞 K) V, localization₂ w.asIdeal (loc (K := K) w.asIdeal Z) = localization₂ w.asIdeal Z := by
    intro Z
    apply le_antisymm
    · rintro x ⟨t, ht, s, hs, hx⟩
      exact ⟨s * t, w.asIdeal.primeCompl.mul_mem (locBasic_hcompl_le (K := K) w.asIdeal hs) ht, by rwa [mul_smul]⟩
    · exact locBasic_locS_mono _ (locBasic_le_locS _ _)
  rw [← key X, h, key Y]

end Herm

end Formalism.BasicNotions.SkeletonIndexLemmas

namespace Formalism.BasicNotions.Idx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory SkeletonIndexLemmas

theorem jMt_inj (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Function.Injective (D.what₂.jMt μ j) := by
  have hli := (D.what₂.jMt_basis μ j (Module.Free.chooseBasis _ _)).1
  have : Fintype (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j)) := @Fintype.ofFinite _ hli.finite
  exact inj_of_li D.what₂.embLL (D.what₂.jMt μ j) (Module.Free.chooseBasis _ _) hli

def hSes (D : D7) (h : HermRat D) (μ : D.what₂.Tup) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    D.what₂.MtL μ j →ₗ⋆[D.what₂.LL] D.what₂.MtL μ j →ₗ[D.what₂.LL] D.what₂.LL :=
  LinearMap.mk₂'ₛₗ (starRingEnd D.what₂.LL) (RingHom.id D.what₂.LL) (hLL D μ j)
    (fun x y z => D.what₂.embLL.injective (by
      simp only [map_add, hLL_spec D h μ j h1 h2, inner_add_left]))
    (fun c x y => D.what₂.embLL.injective (by
      rw [smul_eq_mul, map_mul, hLL_spec D h μ j h1 h2, hLL_spec D h μ j h1 h2, LinearMap.map_smulₛₗ,
        inner_smul_left]
      exact congrArg (· * _) (D.starLL_cx c).symm))
    (fun x y z => D.what₂.embLL.injective (by
      simp only [map_add, hLL_spec D h μ j h1 h2, inner_add_right]))
    (fun c x y => D.what₂.embLL.injective (by
      rw [RingHom.id_apply, smul_eq_mul, map_mul, hLL_spec D h μ j h1 h2, hLL_spec D h μ j h1 h2,
        LinearMap.map_smulₛₗ, inner_smul_right]))

theorem factStepBz {D : D7} (X : DivX D) : FactStepBz X := by
  intro hθ μ j w h1 h2 n b b0 Z hb hb0 hli0 hsp0 hli hZ
  set θ := thetaL X μ j (hθ μ j h1 h2) with hθd
  set θ0 := thetaL X D.what₂.mu0 j (hθ D.what₂.mu0 j h1 h2) with hθ0d
  have hs : ∀ x, X.jM j (θ x) = D.what₂.thetaP μ j (D.what₂.jMt μ j x) := thetaL_spec X μ j (hθ μ j h1 h2)
  have hs0 : ∀ x, X.jM j (θ0 x) = D.what₂.thetaP D.what₂.mu0 j (D.what₂.jMt D.what₂.mu0 j x) :=
    thetaL_spec X D.what₂.mu0 j (hθ D.what₂.mu0 j h1 h2)
  have hc0 : LinearIndependent D.what₂.LL (fun k => θ0 (b0 k)) :=
    li_of_semilinear (X.jM j) _ (by simpa only [hs0] using hli0)
  have hc : LinearIndependent D.what₂.LL (fun i => θ (b i)) :=
    li_of_semilinear (X.jM j) _ (by simpa only [hs] using hli)
  have hcZ : (fun i => θ (b i)) = famOf (fun k => θ0 (b0 k)) Z := by
    funext i
    apply jM_inj X j
    unfold famOf
    rw [hs, hZ i, map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smulₛₗ, hs0]
  have hdZ : Z.det ≠ 0 := det_ne_zero_of_li _ Z (hcZ ▸ hc)

  have hn : Module.finrank D.what₂.LL (X.MjH j).V = n := by
    rw [Module.finrank_eq_card_basis (X.MjH j).b,
      ← Module.finrank_eq_card_basis (Module.Basis.mk (X.jM_basis j).1 (ge_of_eq (X.jM_basis j).2)),
      Module.finrank_eq_card_basis (Module.Basis.mk hli0 (ge_of_eq hsp0)), Fintype.card_fin]
  obtain ⟨-, hMfg, hMsp⟩ := X.MjH_good j
  obtain ⟨m, hm⟩ := exists_basis_locP (D.plEq w) hMfg hMsp hn
  let Q : Matrix (Fin n) (Fin n) D.what₂.LL := Matrix.of fun k i => m.repr (θ0 (b0 i)) k
  have hc0Q : (fun k => θ0 (b0 k)) = famOf m Q := by
    funext i
    unfold famOf
    exact (m.sum_repr _).symm
  have hdQ : Q.det ≠ 0 := det_ne_zero_of_li _ Q (hc0Q ▸ hc0)
  have hcQ : (fun i => θ (b i)) = famOf m (Q * Z) := by rw [hcZ, hc0Q, famOf_famOf]
  have hT : localization₂ (D.plEq w).asIdeal (thTj X μ j) = localization₂ (D.plEq w).asIdeal (latOf (K := D.what₂.LL) (fun i => θ (b i))) := by
    unfold thTj
    rw [thImg_eq_map X μ j (hθ μ j h1 h2), localization_map₂, ← localization_eq_of_semilocalization_eq _ hb.2, ← localization_map₂]
    congr 1
    unfold latOf
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hT0 : localization₂ (D.plEq w).asIdeal (thTj X D.what₂.mu0 j) =
      localization₂ (D.plEq w).asIdeal (latOf (K := D.what₂.LL) (fun i => θ0 (b0 i))) := by
    unfold thTj
    rw [thImg_eq_map X D.what₂.mu0 j (hθ D.what₂.mu0 j h1 h2), localization_map₂, ← localization_eq_of_semilocalization_eq _ hb0.2, ← localization_map₂]
    congr 1
    unfold latOf
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  unfold IjIdx
  rw [lidx_congr _ hm.symm hT, lidx_congr _ hm.symm hT0, hcQ, hc0Q,
    lidx_latOf _ m m.linearIndependent _ (by rw [Matrix.det_mul]; exact mul_ne_zero hdQ hdZ),
    lidx_latOf _ m m.linearIndependent _ hdQ, Matrix.det_mul, vAdd_mul _ hdQ hdZ]
  ring

end Formalism.BasicNotions.Idx

end
