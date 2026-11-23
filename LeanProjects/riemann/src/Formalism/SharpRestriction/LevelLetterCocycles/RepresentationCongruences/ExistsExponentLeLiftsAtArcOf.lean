import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthFourDenominator
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.HmaxLeAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CmpDSmulLetter
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LiftsAtThickLetterType
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SaturationFractionModule

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthFourFirst

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 Formalism.MainNotions.N.FrobeniusPowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem lifts_shift (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d) {f : W.EE} {s e : ℕ}
    (h : LiftsAt W A F c b sol k₀ (lE W s * f) e) : LiftsAt W A F c b sol k₀ f (e + s) := by
  obtain ⟨w₁, z, h1, h2, h3, h4, h5⟩ := h
  refine ⟨w₁, z, h1, h2, h3, h4, ?_⟩
  have hfun : (fun k => if k = k₀ then lE W (e + s) * f else 0) =
      (fun k => if k = k₀ then lE W e * (lE W s * f) else 0) := by
    funext k
    split_ifs
    · simp only [lE, pow_add]; ring
    · rfl
  rw [hfun]; exact h5

theorem letE_idem (c : ZMod n) : (letE c : LetA O n) * letE c = letE c := by
  funext i
  by_cases h : i = c
  · subst h; simp [letE]
  · simp [letE, Pi.single_eq_of_ne h]

theorem exists_exponent_le_liftsAt_arcOf [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hU : up (c - 2) = true)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hth : size (c - 2) < Formalism.MainNotions.LiftingTheory.AI W F (c - 2) + η + 2 * (arcOf b w S η up size).σ PD.p + 2)
    (hconst : ∀ y : O, LiftsAt W (arcOf b w S η up size) F c bb sol k₀ (algebraMap O W.EE y)
      (rr + (arcOf b w S η up size).σ PD.p)) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 34 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 + η * bandI PD.p b w S η size Cb ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  set A := arcOf b w S η up size with hAdef
  have hB' := hB
  obtain ⟨hp11, hSet, hwb, hηb, hSb, -⟩ := hB'
  obtain ⟨-, hSur, hηs, -, -, hnt, -⟩ := hSet

  have hlen' : sInf {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} = 3 := hlen
  have hne : {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)}.Nonempty := by
    by_contra hcon
    rw [Set.not_nonempty_iff_eq_empty] at hcon
    rw [hcon, Nat.sInf_empty] at hlen'
    omega
  have hm3 := Nat.sInf_mem hne
  rw [hlen'] at hm3
  have hm2 := Nat.notMem_of_lt_sInf (s := {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)})
    (m := 2) (by rw [hlen']; norm_num)
  have e3 : c - ((3 : ℕ) : ZMod n) + 1 = c - 2 := by push_cast; ring
  have e2 : c - ((2 : ℕ) : ZMod n) + 1 = c - 1 := by push_cast; ring
  have hnt2 : ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 2) := by
    have := hm3.2; rwa [e3] at this
  have hT1 : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
    by_contra hcon
    exact hm2 ⟨by norm_num, by rw [e2]; exact hcon⟩

  have hhB : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := by
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB; rw [if_pos ⟨c - 1, hT1⟩]
  have eSg : Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by
    rw [show Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size =
      Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size) w S η from rfl, hhB]

  have e21 : c - 2 + 1 = c - 1 := by ring
  have e11 : c - 1 + 1 = c := by ring
  have hup1 : up (c - 1) = false := by
    have := (halt (c - 2)).1; rw [e21, hU] at this
    cases h : up (c - 1) <;> simp_all
  have hup0 : up c = true := by
    have := (halt (c - 1)).1; rw [e11, hup1] at this
    cases h : up c <;> simp_all
  have hty : ∀ i, A.ty i = if up i then Formalism.MainNotions.LocalTheoryWindows.LT.up (size i) else Formalism.MainNotions.LocalTheoryWindows.LT.down (size i) :=
    fun i => rfl

  have hty1 : A.ty (c - ((1 : ℕ) : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - 1)) := by
    rw [hty, Nat.cast_one, hup1]; rfl
  obtain ⟨κ, x, hx⟩ := hf.2 1 (by rw [hlen]; norm_num) (size (c - 1)) hty1
  obtain ⟨s, hsb, hdvd⟩ := arc_length_four_denominator W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill
    hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb halt hsm
    hlen hU hOK hσ κ x hx
  obtain ⟨y, hy⟩ := hdvd

  set ι := algebraMap (LetA O n) W.EE with hι
  have hOι : ∀ z : O, algebraMap O W.EE z = ι (algebraMap O (LetA O n) z) := fun z =>
    IsScalarTower.algebraMap_apply O (LetA O n) W.EE z
  have hlE : ∀ k, lE W k = ι (((PD.p : ℕ) : LetA O n) ^ k) := fun k => by
    simp [lE, hι, map_pow, map_natCast]
  set g : W.EE := lE W s * f - ι (letE c) * algebraMap O W.EE y with hg
  have hnnD : nnDen W A c ∈ W.AΔ := by
    unfold nnDen prodTy
    exact Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ (GS.ps_mem W i) _
  have hpA : ∀ k, ((PD.p : ℕ) : LetA O n) ^ k ∈ W.AΔ := fun k =>
    Subalgebra.pow_mem _ (Subalgebra.natCast_mem _ _) _
  have hCy : algebraMap O (LetA O n) y ∈ W.AΔ := Subalgebra.algebraMap_mem _ y
  have hlet : (letE c : LetA O n) ∈ W.AΔ := fun δ _ => GS.γA_letE W δ c
  obtain ⟨u, hu, hfu⟩ := hf.1
  set u' : LetA O n := ((PD.p : ℕ) : LetA O n) ^ s * u - nnDen W A c * algebraMap O (LetA O n) y with hu'
  have hu'A : u' ∈ W.AΔ := Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (hpA s) hu)
    (Subalgebra.mul_mem _ hnnD hCy)
  have hN1eq : ι (nnDen W A c) * g = ι (letE c * 1 * u') := by
    rw [hg, hu', hOι, hlE, mul_sub, ← mul_assoc, mul_comm (ι (nnDen W A c)) (ι _), mul_assoc, hfu]
    simp only [map_mul, map_sub, map_one]
    ring
  have hN1 : InFr W c 1 (nnDen W A c) g := ⟨u', hu'A, hN1eq⟩

  have hN2 : ∀ s' < A.len c, ∀ bs, A.ty (c - (s' : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
      InFr W c (ps W s' ^ (bs + A.S)) (nnDen W A c) g := by
    intro s' hs' bs hbs
    rw [hlen] at hs'
    interval_cases s'
    · exfalso
      rw [hty, Nat.cast_zero, sub_zero, hup0] at hbs
      simp at hbs
    · have hbs' : bs = size (c - 1) := by
        rw [hty1] at hbs; exact (Formalism.MainNotions.LocalTheoryWindows.LT.down.inj hbs).symm
      subst hbs'
      obtain ⟨u₀, hu₀, hxu⟩ := hx
      set P : LetA O n := ps W 1 ^ (size (c - 1) + A.S) with hP
      set z : LetA O n := letE c * 1 * u' with hz
      have hzA : z ∈ W.AΔ := Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hlet (Subalgebra.one_mem _)) hu'A
      have hyy : ((PD.p : ℕ) : O) ^ κ * y = ((PD.p : ℕ) : O) ^ s * x := hy.symm
      have hkey : ι (((PD.p : ℕ) : LetA O n) ^ κ * (1 * z)) = ι (P * (letE c * ((PD.p : ℕ) : LetA O n) ^ s * u₀)) := by
        have e1 : ι (((PD.p : ℕ) : LetA O n) ^ κ * (1 * z)) = lE W κ * (ι (nnDen W A c) * g) := by
          rw [hN1eq, hlE, one_mul, map_mul]
        have hxy : lE W κ * algebraMap O W.EE y = lE W s * algebraMap O W.EE x := by
          have := congrArg (algebraMap O W.EE) hyy
          simpa [map_mul, map_pow, map_natCast, lE] using this
        have e2 : lE W κ * (ι (nnDen W A c) * g) =
            lE W s * (ι (nnDen W A c) * (lE W κ * f - ι (letE c) * algebraMap O W.EE x)) := by
          rw [hg]
          have : lE W κ * (ι (nnDen W A c) * (lE W s * f - ι (letE c) * algebraMap O W.EE y)) =
              ι (nnDen W A c) * (lE W s * lE W κ * f - ι (letE c) * (lE W κ * algebraMap O W.EE y)) := by ring
          rw [this, hxy]; ring
        rw [e1, e2, hxu, hlE, ← map_mul]
        congr 1
        ring
      have hkey' := W.EE_inj hkey
      have hP1 : P ∈ PiPs W := Submonoid.pow_mem _
        (Submonoid.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range_self (f := ps W) 1))) _
      obtain ⟨y', hy'A, hzy⟩ := saturation_fraction_ring W hcase hP9 hinj P 1 1 hP1 (Submonoid.one_mem _)
        (Submonoid.one_mem _) z (by rw [one_mul]; exact hzA)
        (⟨κ, letE c * ((PD.p : ℕ) : LetA O n) ^ s * u₀,
          Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hlet (hpA s)) hu₀, hkey'⟩ :
          ∃ (k : ℕ) (y : LetA O n), y ∈ W.AΔ ∧ lA W ^ k * (1 * z) = P * y)
      refine ⟨y', hy'A, ?_⟩
      have hzz : letE c * z = z := by rw [hz, ← mul_assoc, ← mul_assoc, letE_idem]
      rw [one_mul] at hzy
      rw [hN1eq]
      show ι z = ι (letE c * P * y')
      congr 1
      calc z = letE c * z := hzz.symm
        _ = letE c * P * y' := by rw [hzy, mul_assoc]
    · exfalso
      have e22 : c - ((2 : ℕ) : ZMod n) = c - 2 := by push_cast; ring
      rw [hty, e22, hU] at hbs
      simp at hbs

  have hthick : ∀ s' < A.len c, (A.ty (c - (s' : ZMod n))).thick := by
    intro s' _
    rw [hty]; cases up (c - (s' : ZMod n)) <;> simp [Formalism.MainNotions.LocalTheoryWindows.LT.thick]
  have hl5 : 5 ≤ PD.p := by omega
  have hNg := liftsAt_thick_letter_type W A F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL hFL hO hOv hinj
    hArc hArcL hNN hW₁ hW₂ hSur rr hkill hbb hk₀ g hN1 hN2
  have hCg : LiftsAt W A F c bb sol k₀ (ι (letE c) * algebraMap O W.EE y) (rr + A.σ PD.p) :=
    LiftsAtT.letter W A F c bb sol k₀ hbb (hconst y)
  have hsum := LiftsAt.add_proof W A F c bb sol k₀ hNg hCg
  rw [hg, sub_add_cancel] at hsum
  have hlift := lifts_shift W A F c bb sol k₀ hsum
  refine ⟨rr + A.σ PD.p + s, ?_, hlift⟩

  have hx11 : (11 : ℝ) ≤ PD.p := by exact_mod_cast hp11
  have hw2 : size (c - 2) ≤ w := hnt (c - 2) hnt2
  have hb1 : 1 ≤ b := by have := hηs (c - 2); omega
  have hAa := (AKill.ai_le W F hB CR hWR (c - 2)).1
  rw [e21, eSg] at hAa
  have hsb' : (s : ℝ) - 1 ≤ max 1 ((size (c - 2) : ℝ) - ((size (c - 1) : ℝ) + S) / PD.p +
      16 / 5 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η) := by
    rw [eSg] at hsb; linarith
  have hσ' : ((A.σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by rw [← eSg]; exact hσ
  have hth' : (size (c - 2) : ℝ) < (Formalism.MainNotions.LiftingTheory.AI W F (c - 2) : ℝ) + η + 2 * ((A.σ PD.p : ℕ) : ℝ) + 2 := by
    exact_mod_cast hth
  have halt4 := le_band_add_errorScale PD.p hp11 b w (size (c - 2)) S η (size (c - 1)) hb1 hηb hSb hwb hw2 hT1.1 hT1.2
    (Formalism.MainNotions.LiftingTheory.AI W F (c - 2) : ℝ) ((A.σ PD.p : ℕ) : ℝ) ((s : ℝ) - 1) Cb hCb hAa hσ' hth' hsb'
  have hband : (if |(PD.p : ℝ) * (size (c - 2) : ℕ) - b| ≤
        Cb * ((PD.p : ℝ) * η + (PD.p : ℝ) * S + (b : ℝ) / PD.p + (size (c - 2) : ℕ) +
          (PD.p : ℝ) * Real.logb PD.p (2 * ((b + η + S : ℕ) : ℝ))) then (1 : ℝ) else 0) ≤
      bandI PD.p b w S η size Cb := by
    split_ifs with h1
    · unfold bandI
      rw [hhB, if_pos]
      exact ⟨c - 2, hnt2, Or.inl (by rw [e21]; exact hT1), h1⟩
    · unfold bandI; split_ifs <;> norm_num
  have hηb0 : (0 : ℝ) ≤ η := Nat.cast_nonneg _
  have hmb := mul_le_mul_of_nonneg_left hband hηb0
  rw [eSg] at hrr ⊢
  push_cast
  linarith

theorem exists_liftsAt_arcOf_exponent_le [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hU : up (c - 2) = true)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hth : size (c - 2) < Formalism.MainNotions.LiftingTheory.AI W F (c - 2) + η + 2 * (arcOf b w S η up size).σ PD.p + 2) :
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 34 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 + η * bandI PD.p b w S η size Cb ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  have hp11 : 11 ≤ PD.p := hB.1
  have hl5 : 5 ≤ PD.p := by omega
  have hSur : Formalism.MainNotions.LiftingTheory.Sur W F := hB.2.1.2.1
  have hthick : ∀ s' < (arcOf b w S η up size).len c,
      ((arcOf b w S η up size).ty (c - (s' : ZMod n))).thick := by
    intro s' _
    show ((if up (c - (s' : ZMod n)) then Formalism.MainNotions.LocalTheoryWindows.LT.up (size (c - (s' : ZMod n)))
      else Formalism.MainNotions.LocalTheoryWindows.LT.down (size (c - (s' : ZMod n)))).thick) = true
    cases up (c - (s' : ZMod n)) <;> rfl
  obtain ⟨d₁, b₁, sol₁, c₁, hb₁, hpr⟩ := constants_pre W (arcOf b w S η up size) F c bb sol k₀ hOK hc hcase hl5
    hHF hArcL hW₁ hSur rr hkill hbb
  exact exists_exponent_le_liftsAt_arcOf W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj
    hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf hP5 Cb hCb halt hsm hlen hU hOK hσ hth
    (fun y => liftsAt_constants_type W (arcOf b w S η up size) F c bb sol k₀ hOK hc hthick hcase hl5 hP2 hP9 hpi0 hSec hGL
      hFL hO hOv hinj hArc hArcL hW₁ hW₂ hSur rr hkill hbb hk₀ b₁ sol₁ hb₁ c₁ hpr y)

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthFourFirst
