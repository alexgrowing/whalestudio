import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.MemLpFrobCoef

noncomputable section

namespace Formalism.MainNotions.S.Pv.DegI

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma Formalism.MainNotions.BridgeLemma₂ Formalism.MainNotions.PlaceDegreeData MeasureTheory
open scoped InnerProductSpace ENNReal

theorem size_gap (D : D7) (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT ρ : ℝ} (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) (hρ : 2 * ρ + 2 ≤ (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10) :
    200 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L - 2 * ρ := by
  rw [nS_cast D]
  have hN6 : (6 : ℝ) ≤ (D.R.r : ℝ) := six_le_n D
  set N : ℝ := (D.R.r : ℝ) with hN
  have hmf : D.R.m ^ 4 ≤ D.R.f := by unfold StandingHypotheses at hH; exact hH.2.2.1
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have h2 := D.R.two_le_m
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast le_trans this hmf
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hf
  have hmn : (D.R.m : ℝ) ≤ N := by
    have : D.R.m ≤ D.R.r := by
      have := D.R.m_add_three_le_k
      simp only [Ranks.r]; omega
    rw [hN]; exact_mod_cast this
  have hm0 : (0 : ℝ) ≤ (D.R.m : ℝ) := Nat.cast_nonneg _
  have hm10 : (D.R.m : ℝ) ^ 10 ≤ N ^ 10 := pow_le_pow_left₀ hm0 hmn 10
  have hG : N ^ 19 ≤ Cl * N ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have e6 : N ^ 19 ≤ N ^ 19 * (D.R.f : ℝ) ^ 5 := le_mul_of_one_le_right (by positivity) hf5
    have e7 : N ^ 19 * (D.R.f : ℝ) ^ 5 ≤ (Cl * large₂.sc.L) * (N ^ 19 * (D.R.f : ℝ) ^ 5) :=
      le_mul_of_one_le_left (by positivity) hCL
    have e8 : Cl * N ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L = (Cl * large₂.sc.L) * (N ^ 19 * (D.R.f : ℝ) ^ 5) := by ring
    rw [e8]; linarith
  have h8 : (200 : ℝ) ≤ N ^ 8 := by
    have : (6 : ℝ) ^ 8 ≤ N ^ 8 := pow_le_pow_left₀ (by norm_num) hN6 8
    norm_num at this
    linarith
  have hX : (1 : ℝ) ≤ N ^ 3 := one_le_pow₀ (by linarith)
  have e1 : N * (D.R.m : ℝ) ^ 10 ≤ N ^ 3 * N ^ 8 := by
    calc N * (D.R.m : ℝ) ^ 10 ≤ N * N ^ 10 := mul_le_mul_of_nonneg_left hm10 (by linarith)
      _ = N ^ 3 * N ^ 8 := by ring
  have e2 : N ^ 19 = N ^ 3 * N ^ 8 * N ^ 8 := by ring
  have e4 : N ^ 3 * N ^ 8 * 200 ≤ N ^ 3 * N ^ 8 * N ^ 8 := mul_le_mul_of_nonneg_left h8 (by positivity)
  have e5 : 200 * N ^ 3 ≤ 199 * (N ^ 3 * N ^ 8) := by nlinarith
  linarith

theorem minpq_pos (D : D7) : 1 ≤ min (pOf (epsSH D.R)) (qOf (epsSH D.R)) := by
  have hk1 : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hq : min (PlaceDegreeData.pOf (epsSH D.R)) (PlaceDegreeData.qOf (epsSH D.R)) = D.R.rS + 1 := by
    rw [← epsilon_signature_eq D, negative_count_of_sign_pattern _ _ hk1]
    exact min_eq_right (positive_count_of_sign_pattern _ _ hk1)
  rw [hq]; omega

variable [Fact Formalism.MainNotions.BridgeCPX.HCMultDSG] [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOneG] in

theorem degree_L2_of_decay (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) (hCL : 1 ≤ Cl * large₂.sc.L)
    (hm : 2 * max Cn 0 + 8 ≤ (D.R.m : ℝ)) (h30 : PlaceDegreeData.DiscreteSeriesDecayBound D) : DegreeL2RangeHypothesis D large₂ C' Cl Cg cb Cu cT CT C0 Cn := by
  intro hH τ ν hν hl H _ _ _ σ hDS v w hv hw
  have hc0 : 0 ≤ max Cn 0 := le_max_right _ _
  have hcn : Cn ≤ max Cn 0 := le_max_left _ _
  have hm8 : (8 : ℝ) ≤ D.R.m := by linarith
  have hm1 : (1 : ℝ) ≤ D.R.m := by linarith
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have hkr := Formalism.MainNotions.BridgeLemma.k_le_r D
  have hrk : (D.R.r : ℝ) ≤ 2 * D.R.k := by
    have h3 := D.R.m_add_three_le_k
    have : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; omega
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ D.R.r := by
    have h : 1 ≤ D.R.r := by
      have := D.R.two_le_m
      unfold Ranks.r
      omega
    exact_mod_cast h
  have hm3 : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 3 := by
    calc (D.R.m : ℝ) = (D.R.m : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (D.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hm1 (by norm_num)
  have hN : ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) = D.R.r := deg_cast_r D
  have hN2 : 2 * (D.R.r : ℝ) ≤ D.R.k * (D.R.m : ℝ) ^ 3 := by nlinarith
  have hcard : ∀ J : Finset (Fin (2 * D.R.rS + D.R.k + 1)), (J.card : ℝ) ≤ D.R.r := by
    intro J
    rw [← hN]
    have : J.card ≤ 2 * D.R.rS + D.R.k + 1 := by
      have := Finset.card_le_univ J
      rwa [Fintype.card_fin] at this
    exact_mod_cast this
  have hρ : 2 * ((Cn + 1) * D.R.k * (D.R.m : ℝ) ^ 3) + 2 ≤ (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 := by
    have hm30 : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 3 := by positivity
    have hm31 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 3 := one_le_pow₀ hm1
    have hm6 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 6 := one_le_pow₀ hm1
    have e1 : (Cn + 1) * D.R.k * (D.R.m : ℝ) ^ 3 ≤ (max Cn 0 + 1) * D.R.r * (D.R.m : ℝ) ^ 3 := by
      have : (Cn + 1) * D.R.k ≤ (max Cn 0 + 1) * D.R.r :=
        mul_le_mul (by linarith) hkr hk0 (by linarith)
      exact mul_le_mul_of_nonneg_right this hm30
    have e2 : (1 : ℝ) ≤ D.R.r * (D.R.m : ℝ) ^ 3 := by nlinarith
    calc 2 * ((Cn + 1) * D.R.k * (D.R.m : ℝ) ^ 3) + 2
        ≤ (D.R.r : ℝ) * ((D.R.m : ℝ) ^ 3 * (2 * max Cn 0 + 4)) := by nlinarith
      _ ≤ (D.R.r : ℝ) * ((D.R.m : ℝ) ^ 3 * (D.R.m : ℝ)) := by gcongr; linarith
      _ = (D.R.r : ℝ) * ((D.R.m : ℝ) ^ 3 * (D.R.m : ℝ) * 1) := by ring
      _ ≤ (D.R.r : ℝ) * ((D.R.m : ℝ) ^ 3 * (D.R.m : ℝ) * (D.R.m : ℝ) ^ 6) := by gcongr
      _ = (D.R.r : ℝ) * (D.R.m : ℝ) ^ 10 := by ring
  have e : (Cn + 1) * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 = Cn * D.R.k * (D.R.m : ℝ) ^ 3 + D.R.k * (D.R.m : ℝ) ^ 3 := by ring
  have hkm : (0 : ℝ) ≤ D.R.k * (D.R.m : ℝ) ^ 3 := by positivity
  have hl' : l1dist ν (lamD D τ) ≤ (Cn + 1) * D.R.k * (D.R.m : ℝ) ^ 3 := by rw [e]; linarith
  have hg := gap_near (szh_gap hH.1 τ) hl'
  exact memLp_frob_coef D h30 hν hDS hg (size_gap D large₂ hH.1 hCL hρ) (minpq_pos D) hv hw

variable [Fact Formalism.MainNotions.BridgeCPX.HCMultDSG] [Fact Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOneG] in

theorem family_degree_L2_of_decay {eps : ℝ} (Fm : FamP eps) (hCl : 1 ≤ sCl Fm) (h30 : PlaceDegreeData.FamilyDiscreteSeriesDecay Fm) :
    ∀ Cg cb Cu cT CT C0, deg_L2F Fm Cg cb Cu cT CT C0 := by
  intro Cg cb Cu cT CT C0 Cn
  obtain ⟨x1, _, h1⟩ := ev_m Fm (2 * max Cn 0 + 8)
  refine ⟨x1, fun x hx i => degree_L2_of_decay _ _ _ _ _ _ _ _ _ _ Cn ?_ (h1 x hx i) (h30 x i)⟩
  have hL : 1 ≤ (Fm.L x i).sc.L :=
    Real.one_le_rpow (le_of_lt (Fm.L x i).sc.one_lt_alt) (le_of_lt (Fm.L x i).sc.eps_pos)
  exact one_le_mul_of_one_le_of_one_le hCl hL

variable [Fact Formalism.MainNotions.BridgeLemma₂.deg_DSUniqG] in
theorem up_G (D : D7) (h18 : OnePlaceEstimates.adm18 D) (h90 : OnePlaceEstimates.FormalDegreeRatioAlt D) {W : LocW D.R.k D.R.rS}
    {μ : Fin (2 * D.R.rS + D.R.k + 1) → ℝ} (I : Finset (Fin (2 * D.R.rS + D.R.k + 1)))
    (hgap : ∀ J : Finset (Fin (2 * D.R.rS + D.R.k + 1)), AllGaps (μ + epsI J) 2)
    (hL2 : ∀ J : Finset (Fin (2 * D.R.rS + D.R.k + 1)), IsHCParam (μ + epsI J) → ∀ (H : Type) [NormedAddCommGroup H]
      [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
      IsDS (epsSH D.R) (μ + epsI J) σ → ∀ v w : H, IsKFin (epsSH D.R) σ v → IsKFin (epsSH D.R) σ w →
        MemLp (fun g : Formalism.REAL.UJ (epsSH D.R) => (frob (umat g) : ℂ) * coefOn σ v w g) 2 (Formalism.REAL.muG (epsSH D.R)))
    (hUq : ∃ hb : ℝ, GapAtLeast (epsSH D.R) (μ + epsI I) hb ∧ Formalism.MainNotions.GapDS.thrDS (epsSH D.R) < hb)
    {A A' : LocS W} (hA : GoodS D μ A) (hA' : GoodS D (μ + epsI I) A') :
    A'.deg / A.deg = fdegHC (μ + epsI I) / fdegHC μ := by
  obtain ⟨P, hDS, hf⟩ := deg_datum D hA
  obtain ⟨P', hDS', hf'⟩ := deg_datum D hA'
  have hv0 : A.v0 ≠ 0 := hA.2.2.2.2.2.1
  have hc : (0 : ℝ) < ((D.s.cdScale _ (epsSH D.R) : NNReal) : ℝ) := by exact_mod_cast D.s.cdScale_pos _ _
  have hd := formal_degree_pos D hA
  obtain ⟨H, i1, i2, i3, σ, v, hv, hDSe, hr⟩ := deg_chain D h18 h90 hA.1 hgap hL2 A.H _ hDS A.v0 hv0
    (by rw [hf _ hv0]; positivity) I hA'.1
  obtain ⟨hb, hgb, hthb⟩ := hUq
  obtain ⟨U, hUi⟩ := BridgeDS3.discrete_series_unique_gapped _ (epsSH D.R) (μ + epsI I) H A'.H σ _ hA'.1 hDSe hDS' hb hgb hthb
  have hUv : U v ≠ 0 := fun h0 => hv (U.map_eq_zero_iff.1 h0)
  rw [deg_fdegOf_equiv _ σ _ U hUi v, hf' _ hUv, hf _ hv0, mul_div_mul_left _ _ hc.ne'] at hr
  exact hr

end Formalism.MainNotions.S.Pv.DegI

end
