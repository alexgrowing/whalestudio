import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TruncatedCoefficientPoly
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ConstantLeRpowOfThreeLe
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DvdCoeffsOfMemSpanDistinguished

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_length_three_le_valuation_constant_term [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hRelay : RelayCore W) (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hSat : SATcore W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hKill : KillerLevCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (rr : ℕ) (hrr : (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hkill : ∀ c ∈ (arcOf b w S η up size).cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hPtEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ)
    (hC4 : Formalism.MainNotions.N.LetterConditionLocal W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hD : up (c - 2) = false)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η))
    (f₂ : W.EE) (hf₂ : InFr W c (ps W 2 ^ (size (c - 2) + S)) (ps W 1 ^ size (c - 1)) f₂) (κ₀ : ℕ) (X₀ : O) (hX₀ : InFr W c (ps W 0 ^ (size c + S)) (ps W 1 ^ size (c - 1))
      (lE W κ₀ * f₂ - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE X₀)) :
    ∀ r : ℚ, v (algebraMap O LL X₀) = ((r : ℚ) : WithTop ℚ) →
      ((size (c - 2) : ℝ) + S - size (c - 1) + ((size c + S : ℕ) : ℝ) / PD.p - ((size c + S : ℕ) : ℝ) / (PD.p : ℝ) ^ 2 - 2 -
        Real.logb PD.p (2 * (((arcOf b w S η up size).h : ℕ) : ℝ))) + κ₀ ≤ (r : ℝ) := by
  intro r hr
  classical
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  obtain ⟨hcr, -⟩ := hW₁
  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T₁ hcr hO hinj
  obtain ⟨hl11, hSet, -, hη20, hS20, -⟩ := hB
  obtain ⟨-, -, hsz, -⟩ := hSet

  have hthick : ∀ d : ℕ, 1 ≤ d → d < 3 →
      Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1) := by
    intro d hd1 hd3
    by_contra hnt
    have hmem : d ∈ {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} :=
      ⟨hd1, hnt⟩
    have hle := Nat.sInf_le hmem
    have hlen' : (arcOf b w S η up size).len c =
        sInf {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := rfl
    rw [hlen'] at hlen
    omega
  have ht1 : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
    have h := hthick 2 (by norm_num) (by norm_num)
    have e2 : c - ((2 : ℕ) : ZMod n) + 1 = c - 1 := by push_cast; ring
    rwa [e2] at h
  have ht0 : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size c := by
    have h := hthick 1 le_rfl (by norm_num)
    have e1 : c - ((1 : ℕ) : ZMod n) + 1 = c := by push_cast; ring
    rwa [e1] at h
  have hh : (arcOf b w S η up size).h = b + η + S := by
    show Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = _
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB
    rw [if_pos ⟨c - 1, ht1⟩]
  have hη1 := hsz (c - 1)
  have hη0 := hsz c
  have hB1 : 1 ≤ size c + S := by omega
  have hb1 : 1 ≤ size (c - 1) := by omega
  have hB11 : size c + S ≤ 11 * size (c - 1) := by
    obtain ⟨h1, -⟩ := ht1
    obtain ⟨-, h2⟩ := ht0
    omega

  simp only [Br.ps_eq, ← Br.cst_pow] at hf₂ hX₀
  obtain ⟨U₁, U₂, hU⟩ := Br.inFr_const c hf₂ hX₀
  have hp0 : Br.P.p 0 = PowerSeries.X := rfl
  rw [hp0] at hU

  by_cases hx0 : X₀ = 0
  · rw [hx0, map_zero, AddValuation.map_zero] at hr
    exact (WithTop.top_ne_coe hr).elim
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨nn, u, hxu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  obtain ⟨vl, hvl⟩ := l_eq_unit_mul_pow hϖ Br.P.hl0
  obtain ⟨e, he⟩ : ∃ e, e = eO (O := O) PD.p := ⟨_, rfl⟩
  rw [← he] at hvl

  have hunit : ∀ y : Oˣ, v (algebraMap O LL (y : O)) = 0 := by
    intro y
    have h1 := hO y
    have h2 := hO (↑y⁻¹ : O)
    have h3 : v (algebraMap O LL (y : O)) + v (algebraMap O LL (↑y⁻¹ : O)) = 0 := by
      rw [← AddValuation.map_mul, ← _root_.map_mul, Units.mul_inv, _root_.map_one,
        AddValuation.map_one]
    exact le_antisymm (le_of_le_of_eq (le_add_of_nonneg_right h2) h3) h1
  have hϖ0 : v (algebraMap O LL ϖ) ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]
    intro h
    exact hϖ.ne_zero (hinj (by rw [h, _root_.map_zero]))
  obtain ⟨d, hd⟩ := WithTop.ne_top_iff_exists.mp hϖ0
  have hvl1 : (((e : ℚ) * d : ℚ) : WithTop ℚ) = 1 := by
    have h := W.v_l
    rw [← map_natCast (algebraMap O LL), hvl, _root_.map_mul, _root_.map_pow,
      AddValuation.map_mul, AddValuation.map_pow, hunit, ← hd, zero_add] at h
    rw [← h, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have hEd : (e : ℚ) * d = 1 := by exact_mod_cast hvl1
  have hrv : (r : ℚ) = nn * d := by
    have h := hr
    rw [hxu, _root_.map_mul, _root_.map_pow, AddValuation.map_mul, AddValuation.map_pow, hunit,
      ← hd, zero_add, ← WithTop.coe_nsmul, nsmul_eq_mul] at h
    exact_mod_cast h.symm

  obtain ⟨k₃, hk₃⟩ : ∃ k : ℕ, k = ⌈(e : ℝ) * (((size (c - 2) + S : ℕ) : ℝ) -
      ((size c + S : ℕ) : ℝ) / ((PD.p : ℕ) : ℝ) ^ 2)⌉₊ := ⟨_, rfl⟩
  have hc3 := Br.P.c3a hϖ (size (c - 2) + S) (size c + S) hB1 k₃ (by rw [← he]; exact hk₃.le)
  obtain ⟨α₁, β₁, hαβ⟩ := Ideal.mem_span_pair.mp hc3
  have hF1 : (e : ℝ) * (((size (c - 2) + S : ℕ) : ℝ) -
      ((size c + S : ℕ) : ℝ) / ((PD.p : ℕ) : ℝ) ^ 2) ≤ k₃ := by
    rw [hk₃]; exact Nat.le_ceil _

  have hc2 := Br.P.constant_le_rpow_of_three_le hϖ (size c + S) (size (c - 1)) hB1 hb1
  rw [← he] at hc2
  have hL : (11 : ℝ) ≤ ((PD.p : ℕ) : ℝ) := by exact_mod_cast hl11
  have hL1 : (1 : ℝ) < ((PD.p : ℕ) : ℝ) := by linarith
  have hy1 : (1 : ℝ) ≤ ((size (c - 1) : ℕ) : ℝ) := by exact_mod_cast hb1
  have hBl : ((size c + S : ℕ) : ℝ) / ((PD.p : ℕ) : ℝ) ≤ ((size (c - 1) : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    have : ((size c + S : ℕ) : ℝ) ≤ 11 * ((size (c - 1) : ℕ) : ℝ) := by exact_mod_cast hB11
    nlinarith
  have hlog0 : 0 ≤ Real.logb ((PD.p : ℕ) : ℝ) ((size (c - 1) : ℕ) : ℝ) := Real.logb_nonneg hL1 hy1
  have hbr : 0 ≤ ((size (c - 1) : ℕ) : ℝ) - ((size c + S : ℕ) : ℝ) / ((PD.p : ℕ) : ℝ) + 2 +
      Real.logb ((PD.p : ℕ) : ℝ) ((size (c - 1) : ℕ) : ℝ) := by linarith
  rw [max_eq_right hbr] at hc2
  have hE0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
  have hF2 : ((e * κ₀ + k₃ : ℕ) : ℝ) - nn ≤ (e : ℝ) * (((size (c - 1) : ℕ) : ℝ) -
      ((size c + S : ℕ) : ℝ) / ((PD.p : ℕ) : ℝ) + 2 +
      Real.logb ((PD.p : ℕ) : ℝ) ((size (c - 1) : ℕ) : ℝ)) := by
    by_cases hlt : nn < e * κ₀ + k₃
    · obtain ⟨m, hm⟩ : ∃ m, e * κ₀ + k₃ = nn + m := ⟨e * κ₀ + k₃ - nn, by omega⟩
      have hpw : (PowerSeries.C ϖ) ^ (e * κ₀) * (PowerSeries.C ϖ) ^ k₃ =
          (PowerSeries.C ϖ) ^ nn * (PowerSeries.C ϖ) ^ m := by
        rw [← pow_add, ← pow_add, hm]
      rw [hvl, hxu, _root_.map_mul, _root_.map_mul, _root_.map_pow, _root_.map_pow, mul_pow,
        ← pow_mul, ← hαβ] at hU
      have hdist := (ContPA.dist_X_pow (O := O) (size c + S)).1
      have hdvd := ContM_cancel_unif hϖ hdist nn
        (x := PowerSeries.C (u : O) * Br.P.p 1 ^ size (c - 1) -
          (PowerSeries.C ϖ) ^ m * (PowerSeries.C (vl : O) ^ κ₀ * α₁ * U₁))
        (a := PowerSeries.C (vl : O) ^ κ₀ * (PowerSeries.C ϖ) ^ (e * κ₀) * β₁ * U₁ - U₂)
        (by linear_combination hU + PowerSeries.C (vl : O) ^ κ₀ * α₁ * U₁ * hpw)
      obtain ⟨γ, hγ⟩ := hdvd
      have hu1 : PowerSeries.C (↑u⁻¹ : O) * PowerSeries.C (u : O) = 1 := by
        rw [← _root_.map_mul, Units.inv_mul, _root_.map_one]
      have hmem : Br.P.p 1 ^ size (c - 1) ∈
          Ideal.span {PowerSeries.C ϖ ^ m, (PowerSeries.X : PowerSeries O) ^ (size c + S)} := by
        refine Ideal.mem_span_pair.mpr ⟨PowerSeries.C (↑u⁻¹ : O) *
          (PowerSeries.C (vl : O) ^ κ₀ * α₁ * U₁), PowerSeries.C (↑u⁻¹ : O) * γ, ?_⟩
        linear_combination (-PowerSeries.C (↑u⁻¹ : O)) * hγ + Br.P.p 1 ^ size (c - 1) * hu1
      have hcont := (Cont.mem_iff_le ϖ _ _ m).mp hmem
      rw [← ENat.natCast_toNat hc2.1] at hcont
      have hmle : (m : ℝ) ≤
          ((cont ϖ (PowerSeries.X ^ (size c + S)) (Br.P.p 1 ^ size (c - 1))).toNat : ℝ) := by
        exact_mod_cast hcont
      have : ((e * κ₀ + k₃ : ℕ) : ℝ) - nn = m := by rw [hm]; push_cast; ring
      rw [this]
      exact hmle.trans hc2.2
    · have : ((e * κ₀ + k₃ : ℕ) : ℝ) - nn ≤ 0 := by
        have : e * κ₀ + k₃ ≤ nn := by omega
        have : ((e * κ₀ + k₃ : ℕ) : ℝ) ≤ nn := by exact_mod_cast this
        linarith
      exact this.trans (mul_nonneg hE0 hbr)

  rw [hh]
  have hlog : Real.logb ((PD.p : ℕ) : ℝ) ((size (c - 1) : ℕ) : ℝ) ≤
      Real.logb ((PD.p : ℕ) : ℝ) (2 * ((b + η + S : ℕ) : ℝ)) := by
    have h2h : (1 : ℝ) ≤ ((b + η + S : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ b + η + S by obtain ⟨-, h2⟩ := ht1; omega)
    apply (Real.logb_le_logb hL1 (by linarith) (by linarith)).mpr
    obtain ⟨-, h2⟩ := ht1
    have : size (c - 1) ≤ 2 * (b + η + S) := by omega
    exact_mod_cast this
  have h3 := mul_le_mul_of_nonneg_left hlog hE0
  have hEd' : (e : ℝ) * (d : ℝ) = 1 := by exact_mod_cast hEd
  have hrv' : ((r : ℚ) : ℝ) = (nn : ℝ) * (d : ℝ) := by exact_mod_cast hrv
  have hd0 : (0 : ℝ) < d := by
    rcases lt_or_ge 0 (d : ℝ) with h | h
    · exact h
    · nlinarith
  push_cast at hF1 hF2 h3 ⊢
  have hmain : (e : ℝ) * ((size (c - 2) : ℝ) + S - size (c - 1) + ((size c : ℝ) + S) / PD.p -
      ((size c : ℝ) + S) / (PD.p : ℝ) ^ 2 - 2 - Real.logb PD.p (2 * ((b : ℝ) + η + S)) + κ₀) ≤ nn := by
    linear_combination hF1 + hF2 + h3
  rw [hrv']
  calc _ = ((e : ℝ) * ((size (c - 2) : ℝ) + S - size (c - 1) + ((size c : ℝ) + S) / PD.p -
      ((size c : ℝ) + S) / (PD.p : ℝ) ^ 2 - 2 - Real.logb PD.p (2 * ((b : ℝ) + η + S)) + κ₀)) * d := by
        rw [mul_comm (e : ℝ), mul_assoc, hEd', mul_one]
    _ ≤ (nn : ℝ) * d := mul_le_mul_of_nonneg_right hmain hd0.le

end Formalism.MainNotions.N.FrobeniusPowerSeries
