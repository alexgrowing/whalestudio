import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TsumThree
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLenTwoThickLetters
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThickLetterType

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

theorem arc_length_two_case_down [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb)
    (hlen : (arcOf b w S η up size).len c = 2) (hdiff : up (c - 1) ≠ up c)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hup : up c = false) (h2b : size (c - 1) ≤ Formalism.MainNotions.LiftingTheory.AI W F (c - 1) + η) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 15 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 + η * bandI PD.p b w S η size Cb ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  classical
  have hB' := hB
  obtain ⟨hp11, hSet, hwb, hηb, hSb, -⟩ := hB
  obtain ⟨-, hSur, hηs, -, -, hnt, -⟩ := hSet
  have hl5 : 5 ≤ PD.p := by omega
  obtain ⟨hct, hcm⟩ := ArcLengthTwo.arc_len_two_thick_letters c hlen
  have hc1 : ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c + 1) := by
    have h := hc
    simp only [arcOf, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h
  have hupm : up (c - 1) = true := by
    cases h : up (c - 1)
    · exact absurd (h.trans hup.symm) hdiff
    · rfl
  have hty0 : (arcOf b w S η up size).ty c = Formalism.MainNotions.LocalTheoryWindows.LT.down (size c) := by
    simp [arcOf, hup]
  have hty1 : (arcOf b w S η up size).ty (c - 1) = Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - 1)) := by
    simp [arcOf, hupm]
  have hnn : nnDen W (arcOf b w S η up size) c = ps W 1 ^ size (c - 1) := by
    unfold nnDen prodTy
    rw [hlen, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_zero]
    simp [hty0, hty1]
  have hthick : ∀ s < (arcOf b w S η up size).len c,
      ((arcOf b w S η up size).ty (c - (s : ZMod n))).thick := by
    intro s _
    simp only [arcOf]
    split <;> rfl
  obtain ⟨κ, x, hx⟩ := hf.2 0 (by rw [hlen]; norm_num) (size c) (by simpa using hty0)
  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T₁ hW₁.1 hO hinj
  have hy1 : 1 ≤ size (c - 1) := by have := hηs (c - 1); omega
  obtain ⟨de, x', hde, hde0, hg1, hg2⟩ := ArcLengthTwo.den_step W Br c (size (c - 1)) (size c + S) κ hy1
    (by have := hηs c; omega) f x (by rw [← hnn]; exact hf.1) (by rw [← hnn]; exact hx)
  set g := lE W de * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x' with hgdef
  have hdown : ∀ s < (arcOf b w S η up size).len c, ∀ bs,
      (arcOf b w S η up size).ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      InFr W c (ps W s ^ (bs + (arcOf b w S η up size).S)) (nnDen W (arcOf b w S η up size) c) g := by
    intro s hs bs hbs
    rw [hlen] at hs
    interval_cases s
    · simp only [Nat.cast_zero, sub_zero, hty0, Formalism.MainNotions.LocalTheoryWindows.LT.down.injEq] at hbs
      subst hbs
      rw [hnn]
      exact hg2
    · simp [hty1] at hbs
  have hgl : LiftsAt W (arcOf b w S η up size) F c bb sol k₀ g (rr + (arcOf b w S η up size).σ PD.p) :=
    liftsAt_thick_letter_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL hFL
      hO hOv hinj hArc hArcL hNN hW₁ hW₂ hSur rr hkill hbb hk₀ g (by rw [hnn]; exact hg1) hdown
  obtain ⟨d₁, b₁, sol₁, c₁, hb₁, hpr⟩ := constants_pre W (arcOf b w S η up size) F c bb sol k₀ hOK hc hcase hl5
    hHF hArcL hW₁ hSur rr hkill hbb
  have hcst : LiftsAt W (arcOf b w S η up size) F c bb sol k₀ (algebraMap O W.EE x')
      (rr + (arcOf b w S η up size).σ PD.p) :=
    liftsAt_constants_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL
      hFL hO hOv hinj hArc hArcL hW₁ hW₂ hSur rr hkill hbb hk₀ b₁ sol₁ hb₁ c₁ hpr x'
  have hcst' : LiftsAt W (arcOf b w S η up size) F c bb sol k₀
      (algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x') (rr + (arcOf b w S η up size).σ PD.p) :=
    LiftsAtT.letter W (arcOf b w S η up size) F c bb sol k₀ hbb hcst
  have hsum := LiftsAt.add_proof W (arcOf b w S η up size) F c bb sol k₀ hcst' hgl
  have esum : algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x' + g = lE W de * f := by
    rw [hgdef]; ring
  rw [esum] at hsum
  have hfin := ArcLengthTwo.lifts_scale W (arcOf b w S η up size) F c bb sol k₀ hsum
  refine ⟨rr + (arcOf b w S η up size).σ PD.p + de, ?_, hfin⟩

  have hhB : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := by
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB; rw [if_pos ⟨c, hct⟩]
  have hSgeq : Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by
    unfold Formalism.MainNotions.N.Ln17.Sg Formalism.MainNotions.N.FrobeniusPowerSeries.Sg; rw [hhB]
  rw [hSgeq] at hrr hσ ⊢
  set Sg' := Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η with hSg'
  have hx11 : (11 : ℝ) ≤ PD.p := by exact_mod_cast hp11
  have hSg1 : 1 ≤ Sg' := by
    rw [hSg']; unfold Formalism.MainNotions.N.FrobeniusPowerSeries.Sg
    have hh1 : (1 : ℝ) ≤ ((b + η + S : ℕ) : ℝ) := by
      have := hηs c; have := hct.2; exact_mod_cast (by omega : 1 ≤ b + η + S)
    have h1 : 0 ≤ ((b + η + S : ℕ) : ℝ) / (PD.p : ℝ) ^ 2 := by positivity
    have h2 : 0 ≤ ((w : ℝ) + S + η) / PD.p := by positivity
    have h3 : 0 ≤ Real.logb PD.p (2 * ((b + η + S : ℕ) : ℝ)) :=
      Real.logb_nonneg (by linarith) (by linarith)
    linarith
  have hband0 : 0 ≤ bandI PD.p b w S η size Cb := by unfold bandI; split_ifs <;> norm_num
  have hη0 : (0 : ℝ) ≤ η := Nat.cast_nonneg _
  have hηb0 : 0 ≤ (η : ℝ) * bandI PD.p b w S η size Cb := mul_nonneg hη0 hband0
  push_cast
  rcases lt_or_ge (PD.p * size (c - 1)) (size c + S) with hlt | hge
  · rw [hde0 hlt]; push_cast; linarith
  have hb1 : 1 ≤ b := by have := hηs c; have := hct.2; omega
  have hw' : size (c - 1) ≤ w := hnt (c - 1) hcm
  have hAI := ArcLengthTwo.aI_le W F hB' CR hWR c hct hc1
  have hwA : (size (c - 1) : ℝ) ≤ (Formalism.MainNotions.LiftingTheory.AI W F (c - 1) : ℝ) + η := by exact_mod_cast h2b
  obtain ⟨k1, k2⟩ := case2b PD.p hp11 b w (size (c - 1)) S η (size c) hb1 hηb hSb hwb hw' hy1 hct.1 hct.2
    _ hAI hwA
  have hDle : (de : ℝ) ≤ η + 5 * Sg' := by
    have hm0 : 0 ≤ max 0 (((size (c - 1) : ℕ) : ℝ) - ((size c + S : ℕ) : ℝ) / PD.p + 2 +
        Real.logb PD.p ((size (c - 1) : ℕ) : ℝ)) := le_max_left _ _
    have hc' := Nat.ceil_lt_add_one hm0
    have hde' : (de : ℝ) ≤ (⌈max 0 (((size (c - 1) : ℕ) : ℝ) - ((size c + S : ℕ) : ℝ) / PD.p + 2 +
        Real.logb PD.p ((size (c - 1) : ℕ) : ℝ))⌉₊ : ℝ) := by exact_mod_cast hde
    have hmax : max 0 (((size (c - 1) : ℕ) : ℝ) - ((size c + S : ℕ) : ℝ) / PD.p + 2 +
        Real.logb PD.p ((size (c - 1) : ℕ) : ℝ)) ≤ η + 5 * Sg' - 1 := by
      apply max_le (by linarith)
      push_cast
      linarith
    linarith
  by_cases hband : Formalism.MainNotions.TruncatedSeriesCountingBounds.Band PD.p b S η size
      (Real.logb PD.p (2 * (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℝ))) Cb
  · have h1 : bandI PD.p b w S η size Cb = 1 := by unfold bandI; rw [if_pos hband]
    rw [h1]; linarith
  · have h0 : bandI PD.p b w S η size Cb = 0 := by unfold bandI; rw [if_neg hband]
    rw [hhB] at hband
    have hnb := fun hle => hband ⟨c - 1, hcm, Or.inl (by rw [sub_add_cancel]; exact hct), hle⟩
    have hη4 := k2 Cb hCb hge hnb
    rw [h0]; linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
