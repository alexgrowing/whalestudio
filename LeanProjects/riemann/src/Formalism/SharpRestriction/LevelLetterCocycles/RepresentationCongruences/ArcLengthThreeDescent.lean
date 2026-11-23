import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TruncatedCoefficientPoly
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.IsDistPow

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

theorem liftsAt_of_scaled_power (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (bb : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d) {f : W.EE}
    {e k : ℕ} (h : LiftsAt W A F c bb sol k₀ (lE W k * f) e) : LiftsAt W A F c bb sol k₀ f (e + k) := by
  obtain ⟨w₁, z, h1, h2, h3, h4, h5⟩ := h
  refine ⟨w₁, z, h1, h2, h3, h4, ?_⟩
  have he : (fun k' => if k' = k₀ then lE W e * (lE W k * f) else 0) =
      (fun k' => if k' = k₀ then lE W (e + k) * f else 0) := by
    funext k'
    unfold lE
    rw [← mul_assoc, ← pow_add]
  rw [← he]
  exact h5

theorem arc_length_three_descent [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η)) :
    ∃ (t₂ X₂ : O) (f₂ : W.EE),
      (∃ r : ℚ, v (algebraMap O LL t₂) = ((r : ℚ) : WithTop ℚ) ∧
        (r : ℝ) ≤ ((η : ℝ) + 2 + Real.logb PD.p (2 * (((arcOf b w S η up size).h : ℕ) : ℝ))) * bandI PD.p b w S η size Cb) ∧
      algebraMap O W.EE t₂ * f = algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE X₂ + f₂ ∧
      InFr W c (ps W 2 ^ (size (c - 2) + S)) (ps W 1 ^ size (c - 1)) f₂ ∧
      ∃ (κ : ℕ) (X₀ : O), InFr W c (ps W 0 ^ (size c + S)) (ps W 1 ^ size (c - 1))
        (lE W κ * f₂ - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE X₀) := by
  have hl11 : 11 ≤ PD.p := hB.1
  have hηs : ∀ i, η < size i := hB.2.1.2.2.1

  have hup1 : up (c - 1) = true := by
    have h := (halt (c - 2)).1
    have e : c - 2 + 1 = c - 1 := by ring
    rw [e, hD] at h
    simpa using h
  have hup0 : up c = false := by
    have h := (halt (c - 1)).1
    have e : c - 1 + 1 = c := by ring
    rw [e, hup1] at h
    simpa using h

  have hnn : nnDen W (arcOf b w S η up size) c = ps W 1 ^ size (c - 1) := by
    unfold nnDen prodTy
    rw [hlen]
    simp [Finset.prod_range_succ, arcOf, hup0, hup1, hD]
  obtain ⟨hf1, hfd⟩ := hf
  rw [hnn] at hf1
  have hf2 := hfd 2 (by rw [hlen]; norm_num) (size (c - 2)) (by simp [arcOf, hD])
  have hf0 := hfd 0 (by rw [hlen]; norm_num) (size c) (by simp [arcOf, hup0])
  rw [hnn] at hf2 hf0

  obtain ⟨-, -, hcut, hnot⟩ := hOK.2.2.1 c hc
  rw [hlen] at hcut hnot
  have hnth : ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 2) := by
    have h := hcut
    simp only [arcOf, Finset.mem_filter, Finset.mem_univ, true_and] at h
    have e : c - ((3 : ℕ) : ZMod n) + 1 = c - 2 := by push_cast; ring
    rwa [e] at h
  have hth : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
    have h := hnot 2 (by norm_num) (by norm_num)
    simp only [arcOf, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at h
    have e : c - ((2 : ℕ) : ZMod n) + 1 = c - 1 := by push_cast; ring
    rwa [e] at h
  have hb1 : 1 ≤ size (c - 1) := by have := hηs (c - 1); omega
  have hy1 : 1 ≤ size (c - 2) + S := by have := hηs (c - 2); omega
  obtain ⟨X₂, f₂, hsplit, hlev2, hlev0⟩ := ArcLengthThreeDescent.split W hcase hP9 T₁ hW₁.1 hO hinj c (size (c - 1))
    (size (c - 2) + S) (size c + S) hy1 hb1 f hf1 hf2 hf0
  have hval : v (algebraMap O LL (((PD.p : ℕ) : O) ^ ArcLengthThreeDescent.Kc PD.p (size (c - 1)) (size (c - 2) + S))) =
      (((ArcLengthThreeDescent.Kc PD.p (size (c - 1)) (size (c - 2) + S) : ℚ) : ℚ) : WithTop ℚ) := by
    rw [map_pow, map_natCast, AddValuation.map_pow, W.v_l, nsmul_one]
    simp
  have heq : algebraMap O W.EE (((PD.p : ℕ) : O) ^ ArcLengthThreeDescent.Kc PD.p (size (c - 1)) (size (c - 2) + S)) * f =
      algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE X₂ + f₂ := by
    rw [← hsplit, map_pow, map_natCast]; rfl
  refine ⟨((PD.p : ℕ) : O) ^ ArcLengthThreeDescent.Kc PD.p (size (c - 1)) (size (c - 2) + S), X₂, f₂,
    ⟨(ArcLengthThreeDescent.Kc PD.p (size (c - 1)) (size (c - 2) + S) : ℚ), hval, ?_⟩, heq, hlev2, hlev0⟩
  rw [Rat.cast_natCast]

  have : Fact PD.p.Prime := ⟨PD.hp⟩
  have hth1 : b ≤ size (c - 1) := hth.1
  have hth2 : size (c - 1) ≤ b + η := hth.2
  have hh : ((arcOf b w S η up size).h : ℕ) = Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size := rfl
  have hhB : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := by
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB; rw [if_pos ⟨c - 1, hth⟩]
  rw [hh]
  have hp1 : (1 : ℝ) < PD.p := by exact_mod_cast (by omega : 1 < PD.p)
  have hlog0 : 0 ≤ Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) := by
    apply Real.logb_nonneg hp1
    rw [hhB]; push_cast
    have : (1 : ℝ) ≤ (size (c - 1) : ℝ) := by exact_mod_cast hb1
    have : ((size (c - 1) : ℕ) : ℝ) ≤ b + η := by exact_mod_cast hth2
    have : (0 : ℝ) ≤ S := Nat.cast_nonneg _
    linarith
  have hη0 : (0 : ℝ) ≤ η := Nat.cast_nonneg _
  by_cases hlt : size (c - 1) < PD.p * (size (c - 2) + S)
  · have hK0 : ArcLengthThreeDescent.Kc PD.p (size (c - 1)) (size (c - 2) + S) = 0 := by
      unfold ArcLengthThreeDescent.Kc; rw [if_pos hlt]
    have hbd : 0 ≤ bandI PD.p b w S η size Cb := by unfold bandI; split_ifs <;> norm_num
    rw [hK0, Nat.cast_zero]
    exact mul_nonneg (by linarith) hbd
  · push Not at hlt
    have hK := ArcLengthThreeDescent.Kc_le PD.p (size (c - 1)) (size (c - 2) + S) η hy1 hlt hy
    have hA : (PD.p : ℝ) * size (c - 2) + PD.p * S ≤ size (c - 1) := by
      have : ((PD.p * (size (c - 2) + S) : ℕ) : ℝ) ≤ size (c - 1) := by exact_mod_cast hlt
      push_cast at this; linarith [mul_add (PD.p : ℝ) (size (c - 2)) S]
    have hB' : (size (c - 1) : ℝ) < PD.p * size (c - 2) + PD.p * S + PD.p * η := by
      have : ((size (c - 1) : ℕ) : ℝ) < ((PD.p * (size (c - 2) + S + η) : ℕ) : ℝ) := by exact_mod_cast hy
      push_cast at this; linarith [mul_add (PD.p : ℝ) (size (c - 2) + S) η, mul_add (PD.p : ℝ) (size (c - 2)) S]
    have hC1 : (b : ℝ) ≤ size (c - 1) := by exact_mod_cast hth1
    have hC2 : (size (c - 1) : ℝ) ≤ b + η := by exact_mod_cast hth2
    have hband : bandI PD.p b w S η size Cb = 1 := by
      unfold bandI
      rw [if_pos]
      refine ⟨c - 2, hnth, Or.inl (by rwa [show c - 2 + 1 = c - 1 by ring]), ?_⟩
      have hp0 : (0 : ℝ) < PD.p := by linarith
      have hbl : (0 : ℝ) ≤ (b : ℝ) / PD.p := by positivity
      have hpl : (0 : ℝ) ≤ PD.p * Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) :=
        mul_nonneg hp0.le hlog0
      have hw0 : (0 : ℝ) ≤ size (c - 2) := Nat.cast_nonneg _
      have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
      have hpη : (η : ℝ) ≤ PD.p * η := by nlinarith
      set Q : ℝ := (PD.p : ℝ) * η + PD.p * S + b / PD.p + size (c - 2) +
        PD.p * Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) with hQ
      have hpS : (0 : ℝ) ≤ PD.p * S := mul_nonneg hp0.le hS0
      have hQ1 : (PD.p : ℝ) * η + PD.p * S ≤ Q := by rw [hQ]; linarith
      have hQ2 : Q ≤ Cb * Q := by nlinarith
      rw [abs_le]
      constructor <;> linarith
    rw [hband, mul_one]
    have hlb : Real.logb PD.p (size (c - 1) : ℝ) ≤ Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ)) := by
      apply Real.logb_le_logb_of_le hp1 (by exact_mod_cast (by omega : 0 < size (c - 1)))
      rw [hhB]; push_cast
      have : (0 : ℝ) ≤ S := Nat.cast_nonneg _
      have : (1 : ℝ) ≤ (size (c - 1) : ℝ) := by exact_mod_cast hb1
      linarith
    linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
