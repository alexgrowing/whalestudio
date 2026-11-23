import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TruncatedCoefficientPoly
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.PpLeHLD

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

theorem inFNc_of_inFP_of_arc_sigma_le [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η))  :
    ∀ x : W.DD T₂, InFP W T₂ (c - 1) 1 (qA W ^ (size c + S)) x → InFNc W T₂ c 1 x := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨qA W ^ (size c + S) • y, ?_, ?_, (one_smul _ _).symm⟩
  · refine DYB.Pp_qpow (W := W) T₂ (c - 1) (size c + S) ?_ hy
    intro z hz
    obtain ⟨-, hs, hp2⟩ := id hcase
    obtain ⟨hcr, hWj⟩ := id hW₂
    obtain ⟨-, -, h9one⟩ := hP9 T₂ hcr hs hp2
    obtain ⟨hring, -⟩ := h9one (NTB.finrank_one W hcase)
    obtain ⟨-, -, -, -, ⟨u, hu⟩, -⟩ := hring
    have hq : W.q = (u : LetA O n) * qA W := by
      rw [hu]
      congr 1
      funext i
      simp [DeltaInvariantLattices.Eat, qA, lA]
    have hQ : W.Q = W.q := by
      simp [LocWach.Q, hs]
    obtain ⟨-, hS, -⟩ := hB
    unfold TruncatedSeriesCountingBounds.HidaSetting at hS
    obtain ⟨-, -, hηs, -⟩ := hS
    have hJ : DeltaInvariantLattices.JumpsLet W T₂ (fun i => size i + S) (fun i => size i + S) := by
      intro τ i hτ a ha
      have h2 := hWj i τ hτ a ha
      have hη := hηs i
      cases hup : up i <;> simp [arcOf, hup, LocalTheoryWindows.LT.win] at h2 <;>
        simp only [Set.mem_Icc, Nat.cast_add] <;> omega
    have h5 : W.Q ^ (size c + S) • W.φD T₂ z ∈ W.N T₂ :=
      (hP5 T₂ (fun i => size i + S) (fun i => size i + S) hcr hJ).1 c z hz.2
    rw [hQ, hq] at h5
    have h6 := Submodule.smul_mem (W.N T₂) ((↑(u⁻¹) : LetA O n) ^ (size c + S)) h5
    rw [smul_smul, ← mul_pow, ← mul_assoc, Units.inv_mul, one_mul] at h6
    exact h6
  · have hH := DYB.Pp_le_HLD (W := W) T₂ (c - 1) hy
    obtain ⟨h, -⟩ := hH
    rw [sub_add_cancel] at h
    rw [smul_smul, mul_comm, ← smul_smul, h]

end Formalism.MainNotions.N.FrobeniusPowerSeries
