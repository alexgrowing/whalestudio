import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TruncatedCoefficientPoly
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeDescent
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeConstantTerm
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeExistsLiftsAtScalarMul
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.AlgebraMapMemInvariants
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

theorem arc_length_three_case_d [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    ∃ e₁ : ℕ, (e₁ : ℝ) ≤ 22 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size + 1 + η * bandI PD.p b w S η size Cb ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ f e₁ := by
  obtain ⟨t₂, X₂, f₂, ⟨r₂, hr₂, hr₂b⟩, hsplit, hf₂, hf₂0⟩ := arc_length_three_descent W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy
  obtain ⟨e, t₃, he, ⟨r₃, hr₃, hr₃b⟩, hl⟩ := arc_length_three_exists_liftsAt_scalar_mul W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy f₂ hf₂ hf₂0
  have hc := arc_length_three_constant_term W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy (t₃ * X₂)
  have hadd := LiftsAt.add_proof W (arcOf b w S η up size) F c bb sol k₀
    (LiftsAt.liftsAt_mono W (arcOf b w S η up size) F c bb sol k₀ (le_max_right e (rr + (arcOf b w S η up size).σ PD.p)) hc)
    (LiftsAt.liftsAt_mono W (arcOf b w S η up size) F c bb sol k₀ (le_max_left e (rr + (arcOf b w S η up size).σ PD.p)) hl)
  have heq : algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE (t₃ * X₂) + algebraMap O W.EE t₃ * f₂ =
      algebraMap O W.EE t₃ * (algebraMap O W.EE t₂ * f) := by
    rw [hsplit, map_mul]; ring
  rw [heq] at hadd
  have hr₂0 : (0 : ℚ) ≤ r₂ := by
    have h0 := hO t₂; rw [hr₂] at h0; exact_mod_cast h0
  have hr₃0 : (0 : ℚ) ≤ r₃ := by
    have h0 := hO t₃; rw [hr₃] at h0; exact_mod_cast h0
  obtain ⟨N, hNge, hNlt⟩ : ∃ N : ℕ, r₃ + r₂ ≤ (N : ℚ) ∧ (N : ℚ) < r₃ + r₂ + 1 :=
    ⟨⌈r₃ + r₂⌉₊, Nat.le_ceil _, Nat.ceil_lt_add_one (by linarith)⟩
  have hv : v (algebraMap O LL t₃ * algebraMap O LL t₂) = ((r₃ + r₂ : ℚ) : WithTop ℚ) := by
    rw [AddValuation.map_mul, hr₃, hr₂, WithTop.coe_add]
  have ht0 : algebraMap O LL t₃ * algebraMap O LL t₂ ≠ 0 := by
    intro h0; rw [h0, AddValuation.map_zero] at hv; exact WithTop.top_ne_coe hv
  have hvx : 0 ≤ v ((PD.p : LL) ^ N * (algebraMap O LL t₃ * algebraMap O LL t₂)⁻¹) := by
    rw [AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_inv, hv, W.v_l]
    have hc' : (N • (1 : WithTop ℚ)) + -(((r₃ + r₂ : ℚ)) : WithTop ℚ) = (((N : ℚ) - (r₃ + r₂) : ℚ) : WithTop ℚ) := by
      rw [← WithTop.coe_one, ← WithTop.coe_nsmul, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add,
        nsmul_one, sub_eq_add_neg]
    rw [hc']
    exact_mod_cast (by linarith : (0 : ℚ) ≤ (N : ℚ) - (r₃ + r₂))
  obtain ⟨t', ht'⟩ := hOv _ hvx
  have ht'O : t' * (t₃ * t₂) = ((PD.p : ℕ) : O) ^ N := by
    apply hinj
    rw [map_mul, map_mul, ht', map_pow, map_natCast, inv_mul_cancel_right₀ ht0]
  have h2 := liftsAt_algebraMap_mul W (arcOf b w S η up size) F c bb sol k₀ t' hadd
  have heq2 : algebraMap O W.EE t' * (algebraMap O W.EE t₃ * (algebraMap O W.EE t₂ * f)) = lE W N * f := by
    rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_assoc t' t₃ t₂, ht'O, map_pow, map_natCast]
    rfl
  rw [heq2] at h2
  refine ⟨max e (rr + (arcOf b w S η up size).σ PD.p) + N, ?_, liftsAt_of_scaled_power W (arcOf b w S η up size) F c bb sol k₀ h2⟩
  have hp : (11 : ℝ) ≤ (PD.p : ℝ) := by exact_mod_cast hB.1
  have hh : (1 : ℝ) ≤ (((arcOf b w S η up size).h : ℕ) : ℝ) := by exact_mod_cast hOK.2.2.2.2.2.2.1
  have hlog : 0 ≤ Real.logb PD.p (2 * (((arcOf b w S η up size).h : ℕ) : ℝ)) :=
    Real.logb_nonneg (by linarith) (by linarith)
  have key : ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → z + 1 ≤ x + y + z + 1 := by
    intro x y z hx hy; linarith
  have hSg : Real.logb PD.p (2 * (((arcOf b w S η up size).h : ℕ) : ℝ)) + 1 ≤ Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size := by
    unfold Formalism.MainNotions.N.Ln17.Sg
    exact key _ _ _ (by positivity) (by positivity)
  have hband : 0 ≤ bandI PD.p b w S η size Cb ∧ bandI PD.p b w S η size Cb ≤ 1 := by
    unfold bandI; split_ifs <;> norm_num
  have h2b : (2 + Real.logb PD.p (2 * (((arcOf b w S η up size).h : ℕ) : ℝ))) * bandI PD.p b w S η size Cb ≤
      2 + Real.logb PD.p (2 * (((arcOf b w S η up size).h : ℕ) : ℝ)) := by
    nlinarith [hband.1, hband.2]
  have hmax : (max (e : ℝ) ((rr : ℝ) + ((arcOf b w S η up size).σ PD.p : ℝ))) ≤ 6 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size :=
    max_le he (by linarith)
  have hN : (N : ℝ) < (r₃ : ℝ) + r₂ + 1 := by exact_mod_cast hNlt
  have hη : (0 : ℝ) ≤ η := Nat.cast_nonneg _
  push_cast
  nlinarith [hband.1, hband.2, hr₂b, hr₃b, hmax, h2b, hSg, hlog, hN]

end Formalism.MainNotions.N.FrobeniusPowerSeries
