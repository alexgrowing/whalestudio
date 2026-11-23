import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ContentBoundLevelIdeal

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

theorem arc_length_four_denominator [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (κ : ℕ) (x : O)
    (hx : InFr W c (ps W 1 ^ (size (c - 1) + S)) (nnDen W (arcOf b w S η up size) c)
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)) :
    ∃ s : ℕ, (s : ℝ) ≤ max 1 ((size (c - 2) : ℝ) - ((size (c - 1) : ℝ) + S) / PD.p + 16 / 5 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size) + 1 ∧
      ((PD.p : ℕ) : O) ^ κ ∣ ((PD.p : ℕ) : O) ^ s * x := by
  obtain ⟨hp11, hset, h20w, h20η, -, -⟩ := hB
  obtain ⟨-, -, hη, -, -, hsz, -⟩ := hset
  have hl3 : (arcOf b w S η up size).len c = 3 := hlen
  have hlen' : sInf {d : ℕ | 1 ≤ d ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} = 3 := hlen
  have hne : ({d : ℕ | 1 ≤ d ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} : Set ℕ).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Nat.sInf_empty] at hlen'
    omega
  have hT2 : ¬ TruncatedSeriesCountingBounds.Thick b η size (c - 2) := by
    have hm := Nat.sInf_mem hne
    rw [hlen'] at hm
    have hm' : 1 ≤ 3 ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - ((3 : ℕ) : ZMod n) + 1) := hm
    have e : c - ((3 : ℕ) : ZMod n) + 1 = c - 2 := by push_cast; ring
    rw [e] at hm'
    exact hm'.2
  have hT0 : TruncatedSeriesCountingBounds.Thick b η size c := by
    by_contra hnt
    have hmem : (1 : ℕ) ∈ {d : ℕ | 1 ≤ d ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := by
      refine ⟨le_refl 1, ?_⟩
      simpa using hnt
    have hle := Nat.sInf_le hmem
    rw [hlen'] at hle
    omega
  have hT1 : TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
    by_contra hnt
    have hmem : (2 : ℕ) ∈ {d : ℕ | 1 ≤ d ∧ ¬ TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := by
      refine ⟨by norm_num, ?_⟩
      have e : c - ((2 : ℕ) : ZMod n) + 1 = c - 1 := by push_cast; ring
      rw [e]
      exact hnt
    have hle := Nat.sInf_le hmem
    rw [hlen'] at hle
    omega
  have hu1 : up (c - 1) = false := by
    have h := (halt (c - 2)).1
    rw [show c - 2 + 1 = c - 1 by ring, hU] at h
    simpa using h
  have hu0 : up c = true := by
    have h := (halt (c - 1)).1
    rw [sub_add_cancel, hu1] at h
    simpa using h
  have hh : TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := by
    unfold TruncatedSeriesCountingBounds.hB
    rw [if_pos ⟨c, hT0⟩]
  obtain ⟨s₁, hs1, hs1le, hsB, hnot⟩ := exists_s1_bound_choice PD.p b w S η (size c) (size (c - 1))
    (size (c - 2)) hp11 (Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (by unfold Formalism.MainNotions.N.Ln17.Sg; rw [hh]) hsm h20w h20η
    (by have := hη (c - 2); omega) (hsz (c - 2) hT2) hT1.1 hT0.2
  refine ⟨s₁, hs1le, ?_⟩
  obtain ⟨Br⟩ := exists_phiBridge W hcase hP9 T₂ hW₂.1 hO hinj
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hps : ∀ s, ps W s = (fun _ => Br.ι (Br.P.p s) : LetA O n) := by
    intro s
    induction s with
    | zero =>
      funext i
      simp [ps, qA, LocWach.π₀, lA, PhiData.p, Br.ι_X]
    | succ s ih =>
      have e : ps W (s + 1) = W.φA (ps W s) := by
        simp only [ps, pow_succ', AlgHom.mul_apply]
      rw [e, ih]
      funext i
      simp [LocWach.φA, letφ, PhiData.p, Function.iterate_succ_apply', Br.ι_φ]
  have hpsc : ∀ s, Br.ι (Br.P.p s) = ps W s c := fun s => by rw [hps s]
  have hX : Br.ι PowerSeries.X = ps W 0 c := hpsc 0
  have hCι : ∀ a : O, Br.ι (PowerSeries.C a) = PowerSeries.C a := fun a => Br.ι.commutes a
  have hN : nnDen W (arcOf b w S η up size) c = ps W 0 ^ size c * ps W 2 ^ size (c - 2) := by
    unfold nnDen prodTy
    rw [hl3]
    simp [Finset.prod_range_succ, arcOf, hu0, hu1, hU]
  have hf1 : InFr W c 1 (nnDen W (arcOf b w S η up size) c) f := by
    unfold InFF at hf
    exact hf.1
  obtain ⟨u₀, hu₀, h0⟩ := hf1
  obtain ⟨u, hu, h1⟩ := hx
  have key : algebraMap (LetA O n) W.EE (letE c * (((PD.p : ℕ) : LetA O n) ^ κ * u₀ -
      nnDen W (arcOf b w S η up size) c * algebraMap O (LetA O n) x -
      ps W 1 ^ (size (c - 1) + S) * u)) = 0 := by
    have hx' : algebraMap O W.EE x = algebraMap (LetA O n) W.EE (algebraMap O (LetA O n) x) :=
      IsScalarTower.algebraMap_apply O (LetA O n) W.EE x
    have hl : lE W κ = ((PD.p : ℕ) : W.EE) ^ κ := rfl
    rw [hx', hl] at h1
    simp only [map_sub, map_mul, map_pow, map_natCast, map_one] at h0 h1 ⊢
    linear_combination h1 - ((PD.p : ℕ) : W.EE) ^ κ * h0
  have key2 : letE c * (((PD.p : ℕ) : LetA O n) ^ κ * u₀ -
      nnDen W (arcOf b w S η up size) c * algebraMap O (LetA O n) x -
      ps W 1 ^ (size (c - 1) + S) * u) = 0 := W.EE_inj (key.trans (map_zero _).symm)
  have key3 := congrFun key2 c
  rw [hN] at key3
  simp only [letE, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.natCast_apply, Pi.zero_apply,
    Pi.single_eq_same, one_mul, Pi.algebraMap_apply] at key3
  have hAC : algebraMap O (PowerSeries O) x = PowerSeries.C x := rfl
  try rw [hAC] at key3
  haveI : Fact (Nat.Prime PD.p) := ⟨PD.hp⟩
  obtain ⟨U₁, hU₁⟩ := Br.range u₀ hu₀ c
  obtain ⟨U₂, hU₂⟩ := Br.range u hu c
  refine den_of_rel Br.P hϖ (D := Br.P.p 2 ^ size (c - 2) * PowerSeries.X ^ size c)
    (U₁ := U₁) (U₂ := U₂) (B := size (c - 1) + S) (s₁ := s₁) ?_ ?_
  · apply Br.inj
    simp only [map_mul, map_sub, map_pow, map_one, mul_one, hCι, map_natCast]
    rw [hX, hpsc 2, hpsc 1, ← hU₁, ← hU₂]
    linear_combination -key3
  · intro hmem
    exact hnot (content_bound_level_ideal (P := Br.P) hϖ (size (c - 2)) (size c) (size (c - 1) + S) s₁
      (by have := hη (c - 2); omega) hs1 hsB hmem)

end Formalism.MainNotions.N.FrobeniusPowerSeries
