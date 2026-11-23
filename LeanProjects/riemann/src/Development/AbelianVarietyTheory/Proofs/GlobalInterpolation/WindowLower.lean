import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HostBoundsTwoMulRpowLogSqLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodTopCountLeConstMulLog
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DimVRowPos
import Development.AutomorphicArithmetic.WeightCongruences.TorsionOrderLeTwoMulFinrankSq

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

noncomputable section

namespace GlobalTheory.EX.WinLow

open Formalism.MainNotions.StandardLattice Finset

private theorem roots_le {R : Ranks} (H : Host R) : NumberField.Units.torsionOrder H.E ≤ 8 * R.f ^ 2 := by
  have h := UpperTheory.torsionOrder_le_two_mul_finrank_sq H.E
  rw [finrank_E H] at h
  linarith

private theorem span_roots (eps cD ch : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hcD : 0 ≤ cD) (hch : 0 ≤ ch) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R →
      R.m * (h0v s ch : ℝ) + 8 * (R.f : ℝ) ^ 2 + 2 ≤ s.b := by
  obtain ⟨x1, hx1⟩ := rank_basic_bounds eps h0 h1
  obtain ⟨x2, hx2⟩ := scale_sizes eps cD (ch + 7) h0 h1 hcD (by linarith)
  refine ⟨max 8 (max x1 x2), fun s R he hx hR => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨h8, hxa, hxb⟩ := hx
  obtain ⟨hf, -⟩ := hx1 s R he hxa hR
  obtain ⟨-, -, -, -, s5, -⟩ := hx2 s R he hxb hR
  have hxp : 0 < s.x := by linarith
  have hf' : (R.f : ℝ) ≤ s.x ^ (3 : ℕ) := by exact_mod_cast hf
  have o3 : 1 ≤ s.x ^ ch := Real.one_le_rpow (by linarith) hch
  have hH : (h0v s ch : ℝ) ≤ 4 * s.x ^ ch := by
    have := (Nat.ceil_lt_add_one (show 0 ≤ s.x ^ ch by positivity)).le
    unfold h0v; push_cast; linarith
  have hH' : 2 * (s.x ^ ch * s.x ^ (7 : ℕ)) ≤ (h0v s (ch + 7) : ℝ) := by
    have := Nat.le_ceil (s.x ^ (ch + 7))
    have e : s.x ^ (ch + 7) = s.x ^ ch * s.x ^ (7 : ℕ) := by
      rw [Real.rpow_add hxp]; norm_cast
    unfold h0v; push_cast; linarith
  have hm : (1 : ℝ) ≤ R.m := by exact_mod_cast (by have := R.two_le_m; omega : 1 ≤ R.m)
  have hf2 : (R.f : ℝ) ^ 2 ≤ s.x ^ (6 : ℕ) := by
    calc (R.f : ℝ) ^ 2 ≤ (s.x ^ (3 : ℕ)) ^ 2 := pow_le_pow_left₀ (by positivity) hf' 2
      _ = _ := by ring
  have p6 : 1 ≤ s.x ^ (6 : ℕ) := one_le_pow₀ (by linarith)
  have p7 : 8 * s.x ^ (6 : ℕ) ≤ s.x ^ (7 : ℕ) := by
    rw [pow_succ' s.x 6]; exact mul_le_mul_of_nonneg_right h8 (by positivity)
  have hz : 1 ≤ (R.m : ℝ) * s.x ^ ch := one_le_mul_of_one_le_of_one_le hm o3
  have a1 := mul_le_mul_of_nonneg_left hH (by linarith : (0 : ℝ) ≤ R.m)
  have a2 := mul_le_mul_of_nonneg_left hH' (by linarith : (0 : ℝ) ≤ R.m)
  have a3 : (R.m : ℝ) * s.x ^ ch * 4 ≤ (R.m : ℝ) * s.x ^ ch * s.x ^ (7 : ℕ) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have a4 : s.x ^ (7 : ℕ) ≤ (R.m : ℝ) * s.x ^ ch * s.x ^ (7 : ℕ) := le_mul_of_one_le_left (by linarith) hz
  linarith

theorem places_ok (eps : ℝ) (C : FC) (cD ch : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hC : Std C) (hcD : 0 ≤ cD)
    (hch : 0 ≤ ch) : ∃ x0 : ℝ, ∀ (s : Scale) (P : PreCh) (q1 : ℕ) (a b : P.R.A → ℤ)
      (c : P.Word → Fin (P.R.k - 2) → Bool), s.eps = eps → x0 ≤ s.x → ChOK s C cD ch P q1 a b c →
      ∀ u τ, Formalism.LogVandermondeBounds.StandardLattice.PlaceData s.x (Delv s cD) s.a s.b P.R.k P.R.m (seqOf (P.hcW u τ).u) (seqOf (P.hcW u τ).v)
        (seqOf (P.hcW u τ).b) (seqOf (P.hcW u τ).e) ∧ ∀ j < P.R.m, 1 ≤ seqOf (P.hcW u τ).e j := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hmid, -⟩ := hC
  have hLa : 1 ≤ C.GK.La := hmid _ (by simp [FC.cMid])
  obtain ⟨x1, hx1⟩ := bottom_len eps C.GK h0 h1 hLa
  obtain ⟨x2, hx2⟩ := scale_sizes eps cD ch h0 h1 hcD hch
  obtain ⟨x3, hx3⟩ := span_roots eps cD ch h0 h1 hcD hch
  refine ⟨max (max x1 x2) x3, fun s P q1 a b c he hx h u τ => ?_⟩
  simp only [max_le_iff] at hx
  have hbl := hx1 s P.R he hx.1.1 h.rank
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, -⟩ := hx2 s P.R he hx.1.2 h.rank
  have s8 := hx3 s P.R he hx.2 h.rank
  have hf0 : (0 : ℝ) ≤ (P.R.f : ℝ) ^ 2 := by positivity
  obtain ⟨v1, v2, ⟨b1, v3, v4, v5, v6⟩, -⟩ := h.hc u
  have hx1' := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have hk := P.R.m_add_three_le_k
  have hk2 : (2 : ℝ) ≤ P.R.k := by exact_mod_cast (by omega : 2 ≤ P.R.k)
  have hD : (1 : ℝ) ≤ (Delv s cD : ℝ) := by
    have : 0 < ⌈s.x ^ cD⌉₊ := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hxp _)
    exact_mod_cast this
  have htop : (τ : P.R.GG) ∈ P.H.topPlaces → ∃ t : P.H.TT, (τ : P.R.GG) = P.R.tau1 t := by
    intro h1
    unfold Host.topPlaces at h1
    obtain ⟨t, ht, e⟩ := Finset.mem_image.1 h1
    exact ⟨⟨t, ht⟩, e.symm⟩
  have hb1 : s.w'' P.R.n ≤ (b1 τ : ℝ) ∧ (b1 τ : ℝ) ≤ s.b + 8 * (P.R.f : ℝ) ^ 2 + 2 := by
    by_cases c1 : (τ : P.R.GG) ∈ P.H.topPlaces
    · obtain ⟨t, ht⟩ := htop c1
      obtain ⟨-, w1, w2⟩ := h.win t t.2
      have f1 : (0 : ℝ) ≤ (⌊s.b' / s.x⌋ : ℤ) := by exact_mod_cast Int.floor_nonneg.2 (by positivity)
      have f2 : ((⌊s.b' / s.x⌋ : ℤ) : ℝ) ≤ s.b' := (Int.floor_le _).trans (div_le_self s3 hx1'.le)
      rw [v4 τ t ht]
      push_cast
      constructor <;> linarith
    · by_cases c2 : (τ : P.R.GG) ∈ P.H.thickPlaces
      · have f1 := Int.le_ceil s.b
        have f2 := Int.ceil_lt_add_one s.b
        obtain ⟨e1, e2⟩ := v5 τ c2
        have e3 : ((⌈s.b⌉ : ℤ) : ℝ) ≤ (b1 τ : ℝ) := by exact_mod_cast e1
        have e4 : (b1 τ : ℝ) < ((⌈s.b⌉ : ℤ) : ℝ) + (NumberField.Units.torsionOrder P.H.E : ℝ) := by exact_mod_cast e2
        have e5 : (NumberField.Units.torsionOrder P.H.E : ℝ) ≤ 8 * (P.R.f : ℝ) ^ 2 := by exact_mod_cast roots_le P.H
        constructor <;> linarith
      · have f1 := Int.le_ceil (s.w'' P.R.n)
        have f2 := Int.ceil_lt_add_one (s.w'' P.R.n)
        rw [v6 τ ⟨τ.2, c1, c2⟩]
        constructor <;> linarith
  refine place_data (P.hcW u τ) s.x (Delv s cD) s.a s.b (h0v s ch) (b1 τ) hx1'.le hD (by positivity)
    (fun i => ?_) (fun hp hp' => ?_) (fun j => ?_) (s1.trans hb1.1) (by linarith [hb1.2])
  · rw [v1 τ i]; push_cast; rfl
  · by_cases c1 : (τ : P.R.GG) ∈ P.H.topPlaces
    · left
      obtain ⟨t, ht⟩ := htop c1
      obtain ⟨⟨-, w0⟩, w1, w2⟩ := h.win t t.2
      obtain ⟨e1, e2⟩ := h.top u τ t hp ht
      have ha : 0 ≤ s.a := by linarith
      have o1 : 1 ≤ s.x ^ (Scale.A / 2) := Real.one_le_rpow hx1'.le (by norm_num [Scale.A])
      have o2 : s.a / ((P.R.k : ℝ) * s.x ^ (Scale.A / 2)) ≤ s.a / 2 :=
        div_le_div_of_nonneg_left ha (by norm_num) (by nlinarith)
      rw [e1, e2]
      push_cast
      constructor <;> linarith
    · right
      obtain ⟨e1, e2⟩ := v2 τ hp c1
      rw [e1, e2]
      push_cast
      exact ⟨rfl, rfl⟩
  · obtain ⟨e1, e2⟩ := v3 τ j
    refine ⟨?_, ?_⟩
    · rw [e1]; push_cast; rfl
    · rw [e2]; push_cast; rfl

theorem rank_consts (eps c g : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R →
      2 * |c| ≤ R.m ∧ (R.m : ℝ) ^ 2 ≤ R.k ∧ 2 * g * (R.m : ℝ) ^ 4 ≤ R.k ∧ 1 ≤ s.L := by
  obtain ⟨x1, hx1⟩ := rank_basic_bounds eps h0 h1
  refine ⟨max x1 (max ((2 * |c|) ^ 4) ((2 * |g|) ^ 4)), fun s R he hx hR => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨hxa, hxc, hxg⟩ := hx
  obtain ⟨-, hm, -, -, -, -, hL, -, -, -, -, -, -, -, -, hm1, -⟩ := hx1 s R he hxa hR
  obtain ⟨-, -, ⟨hk, -⟩, -⟩ := hR
  have hx1' := s.one_lt_alt
  have hxp : 0 < s.x := by linarith
  have e0 := s.eps_pos
  have e1 := s.eps_lt
  have root : ∀ y : ℝ, 0 ≤ y → y ^ 4 ≤ s.x → y ≤ s.x ^ ((1 : ℝ) / 4) := fun y hy h => by
    have := Real.rpow_le_rpow (by positivity) h (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hy, show ((4 : ℕ) : ℝ) * (1 / 4) = 1 by norm_num,
      Real.rpow_one] at this
  have m0 : (0 : ℝ) ≤ R.m := by positivity
  have m4 : (R.m : ℝ) ^ 4 ≤ s.x ^ 4 := pow_le_pow_left₀ m0 hm 4
  have m2 : (R.m : ℝ) ^ 2 ≤ s.x ^ 2 := pow_le_pow_left₀ m0 hm 2
  refine ⟨(root _ (by positivity) hxc).trans
    ((Real.rpow_le_rpow_of_exponent_le hx1'.le (by linarith)).trans hm1), ?_, ?_, hL⟩
  · refine m2.trans (le_trans ?_ hk)
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hx1'.le (by linarith)
  · calc 2 * g * (R.m : ℝ) ^ 4 ≤ 2 * |g| * (R.m : ℝ) ^ 4 := by gcongr; exact le_abs_self g
      _ ≤ s.x ^ ((1 : ℝ) / 4) * s.x ^ 4 :=
          mul_le_mul (root _ (by positivity) hxg) m4 (by positivity) (by positivity)
      _ = s.x ^ ((1 : ℝ) / 4 + 4) := by
          rw [Real.rpow_add hxp, ← Real.rpow_natCast]; norm_num
      _ ≤ s.x ^ (9 / 2 + 10 * s.eps) := Real.rpow_le_rpow_of_exponent_le hx1'.le (by linarith)
      _ ≤ R.k := hk

theorem window_lower : Formalism.MainNotions.StandardLattice.SiegelMassRatioCM → ∀ (eps : ℝ) (C : FC), 0 < eps → eps < 1 / 52 → Std C → ∀ cD : ℝ, 0 ≤ cD → ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ x0 : ℝ, ∀ (s : Scale) (P : PreCh) (q1 : ℕ) (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool) (du : P.Word → ℕ) (Ds : ℝ), s.eps = eps → x0 ≤ s.x → ChOK s C cD ch P q1 a b c → (∀ u, (du u : ℝ) = (letI := P.H.cmStar; Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm P.H.E P.R.k) (Formalism.MainNotions.StandardLattice.stdLat P.H.E P.R.k)) * (Formalism.MainNotions.StandardLattice.idxColLoc (P.H.g 0) P.R.k ^ P.R.f * Formalism.MainNotions.StandardLattice.idxColLoc (P.H.g 1) P.R.k ^ P.R.f) * ∏ τ : Tau P.R, Formalism.MainNotions.StandardLattice.dimV (fun i : Fin P.R.k => (((P.hcW u τ).u i : ℚ) : ℝ))) → (2 / 3 : ℝ) ^ P.R.f * (letI := P.H.cmStar; Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm P.H.E P.R.r) (Formalism.MainNotions.StandardLattice.stdLat P.H.E P.R.r)) * (Formalism.MainNotions.StandardLattice.idxRowLoc (P.H.g 0) P.R.k P.R.m ^ P.R.f * Formalism.MainNotions.StandardLattice.idxRowLoc (P.H.g 1) P.R.k P.R.m ^ P.R.f) * ∏ τ : Tau P.R, Formalism.MainNotions.StandardLattice.dimV (Fin.append (fun i => (((P.hcW P.u₀ τ).v i : ℚ) : ℝ)) (fun j => -(((P.hcW P.u₀ τ).b j : ℚ) : ℝ))) ≤ Ds → ∀ u, (P.R.m : ℝ) * s.L ≤ Real.log ((Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * GamS C s P.R ^ (-(2 : ℝ) / (P.R.f * P.R.k))) := by
  intro h2b eps C h0 h1 hC cD hcD
  refine ⟨0, fun ch hch => ?_⟩
  obtain ⟨C1, hC1⟩ := Formalism.LogVandermondeBounds.vandermonde_place_lower_bound eps 5 h0 h1 (by norm_num)
  obtain ⟨x1, hx1⟩ := places_ok eps C cD ch h0 h1 hC hcD hch
  obtain ⟨x2, hx2⟩ := scale_sizes eps cD ch h0 h1 hcD hch
  obtain ⟨x3, hx3⟩ := rank_consts eps C1 C.CGam h0 h1
  obtain ⟨x4, hx4⟩ := hostBounds eps C.P.Cpde h0 h1 hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨max (max x1 x2) (max x3 x4), fun s P q1 a b c du Ds he hx h hdu hDs u => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hx
  have hpl := hx1 s P q1 a b c he a1 h u
  obtain ⟨-, -, -, -, -, -, -, hk5⟩ := hx2 s P.R he a2 h.rank
  obtain ⟨r1, r2, r3, hL⟩ := hx3 s P.R he a3 h.rank
  obtain ⟨-, -, -, -, -, rd1, -, rd2, -⟩ := hx4 s P.R P.H he a4 h.rank h.val
  subst he
  let _ := P.H.cmStar
  have hcm := host_cm P.H
  have hk := P.R.m_add_three_le_k
  have hm := P.R.two_le_m
  have hxp : 0 < s.x := by linarith [s.one_lt_alt]
  have hk1 : (1 : ℝ) ≤ P.R.k := by exact_mod_cast (by omega : 1 ≤ P.R.k)
  have hf1 : (1 : ℝ) ≤ P.R.f := by exact_mod_cast f_pos P.R
  have hm0 : (0 : ℝ) ≤ P.R.m := by positivity
  have hv := pi_le_v P.H
  have hv0 : 0 < P.H.v := lt_of_lt_of_le Real.pi_pos hv
  have hlv : Real.log P.H.v ≤ s.L :=
    (Real.log_le_log hv0 (by unfold Host.v; linarith)).trans rd2
  have hD : (1 : ℝ) ≤ (Delv s cD : ℝ) := by
    have : 0 < ⌈s.x ^ cD⌉₊ := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hxp _)
    exact_mod_cast this
  have hbp : 0 < s.b := Real.exp_pos _
  have hgb : ∀ i, s.b ^ 8 ≤ (P.H.g i : ℝ) := fun i =>
    (pow_le_pow_left₀ hbp.le (le_mul_of_one_le_left hbp.le hk1) 8).trans (h.val.2.2.2.2.1 i).1
  have hlg : ∀ i, 8 * s.L ≤ Real.log (P.H.g i) := fun i => by
    have := Real.log_le_log (by positivity) (hgb i)
    rw [Real.log_pow] at this
    unfold Scale.b at this
    rw [Real.log_exp] at this
    exact_mod_cast this
  have hg3 : ∀ i, 3 ≤ P.H.g i := fun i => by
    have h2 : 2 ≤ s.b := by have := Real.add_one_le_exp s.L; unfold Scale.b; linarith
    have h3 : (2 : ℝ) ^ 8 ≤ s.b ^ 8 := pow_le_pow_left₀ (by norm_num) h2 8
    have : (3 : ℝ) ≤ P.H.g i := by linarith [hgb i]
    exact_mod_cast this
  have hg1 : ∀ i, (1 : ℝ) ≤ (P.H.g i : ℝ) := fun i => by exact_mod_cast (P.H.g_prime i).one_lt.le
  obtain ⟨i1, i2, i3⟩ := idx_ratio P.R P.H.g P.H.g_prime hg3
  have hDpos : 0 < Ds := by
    refine lt_of_lt_of_le ?_ hDs
    have := mass_pos P.H.E hcm P.R.r
    exact mul_pos (by positivity) (Finset.prod_pos fun τ _ => dimV_row_pos _)
  have hmass := mass_tel h2b P.H.E hcm P.R.k (by omega) (P.R.m - 1)
  have e1 : P.R.k + (P.R.m - 1) = P.R.r := by unfold Ranks.r; omega
  have e2 : P.R.r + 1 = P.R.k - 1 + P.R.m + 1 := by unfold Ranks.r; omega
  rw [e1, e2] at hmass
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide at hmass
  rw [vInv_E, fDeg_E] at hmass
  have key := hC1 s.x s.one_lt_alt.le P.R.f P.R.m P.R.k P.H.v (Delv s cD) (P.H.g 0 : ℝ) (P.H.g 1 : ℝ)
    (fun n => seqOf (P.hcW u (placeNo P.H n)).u) (fun n => seqOf (P.hcW u (placeNo P.H n)).v)
    (fun n => seqOf (P.hcW u (placeNo P.H n)).b) (fun n => seqOf (P.hcW u (placeNo P.H n)).e)
    Ds (du u) _ _ _ _ (fun M => Formalism.HermitianLatticesTheory.lValEta P.H.E M)
    (f_pos P.R) (by omega) (by omega) hk5 hv hlv hD (hg1 0) (hg1 1) (fun n _ => (hpl _).1)
    (mass_pos P.H.E hcm P.R.k) (mass_pos P.H.E hcm P.R.r) i2 i1
    (fun M hM => by
      have hM2 : 2 ≤ M := by have := (Finset.mem_Ico.1 hM).1; omega
      refine ⟨(Formalism.HermitianLattices.GlobalBoundRefinements.log_l_value_field_bound P.H.E hcm M hM2).2.1, ?_⟩
      have := cmField_unramified_massIdentity P.H.E hcm M hM2
      rwa [fDeg_E] at this)
    hmass i3
    (by
      rw [prod_places P.H] at hDs
      simp only [dimV_row] at hDs
      simp only [P.hcW_v u, P.hcW_b u]
      exact hDs)
    (by
      have := hdu u
      rw [prod_places P.H] at this
      simp only [dimV_col] at this
      exact this)
  have hsum : 0 ≤ ∑ j ∈ range P.R.m, (1 / (P.R.f : ℝ)) *
      ∑ ρ ∈ range P.R.f, Real.log (seqOf (P.hcW u (placeNo P.H ρ)).e j * P.H.v / Real.pi) := by
    refine Finset.sum_nonneg fun j hj => mul_nonneg (by positivity) (Finset.sum_nonneg fun ρ _ => Real.log_nonneg ?_)
    rw [one_le_div Real.pi_pos]
    exact hv.trans (le_mul_of_one_le_left hv0.le ((hpl _).2 j (Finset.mem_range.1 hj)))
  have hq : (P.R.m : ℝ) ^ 2 * s.L / P.R.k ≤ s.L := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hq0 : 0 ≤ (P.R.m : ℝ) ^ 2 * s.L / P.R.k := by positivity
  have hC2 : C1 * (s.L + (P.R.m : ℝ) ^ 2 * s.L / P.R.k) ≤ P.R.m * s.L :=
    calc _ ≤ |C1| * (s.L + (P.R.m : ℝ) ^ 2 * s.L / P.R.k) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ |C1| * (2 * s.L) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = 2 * |C1| * s.L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right r1 (by linarith)
  have hg : (P.R.m : ℝ) * (16 * s.L) ≤ P.R.m * (Real.log (P.H.g 0) + Real.log (P.H.g 1)) :=
    mul_le_mul_of_nonneg_left (by linarith [hlg 0, hlg 1]) hm0
  have hmain : 15 * (P.R.m * s.L) ≤ 1 / ((P.R.f : ℝ) * P.R.k) * Real.log (Ds / du u) := by
    have key' : _ + _ - C1 * (s.L + (P.R.m : ℝ) ^ 2 * s.L / P.R.k) ≤ _ := key
    linarith
  have hmL : 0 < (P.R.m : ℝ) * s.L := by
    have : (2 : ℝ) ≤ P.R.m := by exact_mod_cast hm
    nlinarith
  have hdu0 : (0 : ℝ) < du u := by
    rcases (Nat.cast_nonneg (α := ℝ) (du u)).lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at hmain
      simp only [div_zero, Real.log_zero, mul_zero] at hmain
      linarith
  have hG : 0 < GamS C s P.R := Real.exp_pos _
  rw [Real.log_mul (Real.rpow_pos_of_pos (div_pos hDpos hdu0) _).ne' (Real.rpow_pos_of_pos hG _).ne',
    Real.log_rpow (div_pos hDpos hdu0), Real.log_rpow hG]
  unfold GamS
  rw [Real.log_exp]
  have e3 : -(2 : ℝ) / (P.R.f * P.R.k) * (C.CGam * (P.R.m : ℝ) ^ 5 * P.R.f * s.L) =
      -((2 * C.CGam * (P.R.m : ℝ) ^ 4 / P.R.k) * (P.R.m * s.L)) := by
    field_simp
  have e4 : 2 * C.CGam * (P.R.m : ℝ) ^ 4 / P.R.k ≤ 1 := (div_le_one (by linarith)).2 r3
  have e5 := mul_le_mul_of_nonneg_right e4 hmL.le
  rw [e3]
  linarith

end GlobalTheory.EX.WinLow

end
