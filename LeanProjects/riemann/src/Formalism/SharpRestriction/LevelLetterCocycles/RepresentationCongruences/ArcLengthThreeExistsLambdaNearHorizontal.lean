import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TruncatedCoefficientPoly
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.SaturationFractionModule
import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible
import Formalism.SharpRestriction.LevelLetterCocycles.LetterConditionGlobal

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

theorem ring_identity_lambda_terms {R : Type} [CommRing R] (L Φ G a B J : R) (s1 s k1 E K S : ℕ) (hK : K = k1 + E)
    (hS : S = s1 + s) (H : L ^ s * Φ * G = (a * L ^ E + B * J) * G) :
    L ^ K * (L ^ s1 * G * a) - L ^ S * (Φ * (L ^ k1 * G)) = J * (-(L ^ s1 * L ^ k1 * G * B)) := by
  subst hK hS
  linear_combination (-(L ^ s1 * L ^ k1)) * H

theorem arc_length_three_exists_lambda_near_horizontal [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    ∃ (lam : W.DD T₂) (κ : ℕ) (Hh : W.DD T₂), InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 1 lam ∧
      InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (W.γ T₂ lam - lam) ∧
      IsHorTr W T₂ bb sol ((arcOf b w S η up size).M PD.p) κ k₀ Hh ∧
      ∃ κ' : ℕ, InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ ((arcOf b w S η up size).σ PD.p) • ((W.φD T₂) ^ 2) Hh)) := by
  set A := arcOf b w S η up size with hAdef
  set c' : ZMod n := c - ((A.len c : ℕ) : ZMod n) with hc'
  have hl : 2 ≤ PD.p := PD.hp.two_le
  have hp2 : PD.p ≠ 2 := hcase.2.2
  have hT₂ : IsCrys PD T₂.ρ := hW₂.1
  have hC := Formalism.MainNotions.UnusedSlot80.Relay2.ctx_of W hinj hOv hP9 hH hTr hcase T₂ hT₂
  have h9 := (Formalism.MainNotions.LiftingTheory.frame_p9A W hP9 hcase T₂ hT₂).1
  have hM : 2 * A.G₀ ≤ (PD.p - 1) * A.M PD.p :=
    Formalism.MainNotions.UnusedSlot80.Relay2.arith_M PD.p A.G₀ A.h hl hOK.2.2.2.2.2.1
  have hHc := hH hcase T₂ hT₂ c'
  have hbd : ∀ r m, Formalism.MainNotions.LiftingTheory.Bd W r (sol k₀ r m) := fun r m =>
    (hHc.2.2.2.2 d bb hbb.1 sol hbb.2).1 k₀ r m
  have h4 := hHc.2.2.2.1
  have hg : ∀ r m, ∃ o : O, algebraMap O LL o =
      (PD.p : LL) ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r * sol k₀ r m :=
    fun r m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hOv r (h4 r) _ (hbd r m)
  choose g hg using hg
  set M := A.M PD.p with hMdef
  set JJ1 := Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) M with hJJ1
  have hdec : ∀ r, ∃ a ∈ W.AΔ, ∃ B' ∈ W.AΔ, ∀ m,
      ((PD.p : ℕ) : LetA O n) ^ Formalism.NOK.sigNOK PD.p (2 * A.G₀) M 1 * ((W.φA ^ 1) W.π₀) ^ r *
          algebraMap O (LetA O n) (g r m) =
        (a * ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r + B' * JJ1) *
          algebraMap O (LetA O n) (g r m) := by
    intro r
    obtain ⟨a, ha, B', hB', h⟩ := Formalism.MainNotions.LiftingTheory.tr_trunc_int W h9 hp2 1 (2 * A.G₀) M r le_rfl
    exact ⟨a, ha, B', hB', fun m => by rw [h]; rfl⟩
  choose a ha B' hB' heq using hdec
  set σ := A.σ PD.p with hσdef
  set sg := Formalism.NOK.sigNOK PD.p (2 * A.G₀) M 1 with hsg
  have hsgσ : sg ≤ σ := Formalism.MainNotions.UnusedSlot80.Relay2.sig_le A PD.p
  set κ := Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M with hκ
  let y : ℕ → Fin d → O := fun r m => ((PD.p : ℕ) : O) ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g r m
  have hy : ∀ r < M, ∀ m, algebraMap O LL (y r m) = (PD.p : LL) ^ κ * sol k₀ r m := by
    intro r hr m
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le
    simp only [y, map_mul, map_pow, map_natCast, hg]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  have hyA : ∀ r m, algebraMap O (LetA O n) (y r m) =
      lA W ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * algebraMap O (LetA O n) (g r m) := by
    intro r m; simp only [y, map_mul, map_pow, map_natCast]; rfl
  let β : Fin d → W.DD T₂ := fun m => ((W.φD T₂) ^ 1) (bb m)
  have hβ : ∀ m, β m ∈ Pp W T₂ c' 1 := fun m => Formalism.MainNotions.UnusedSlot80.Relay2.Pp_phi W T₂ c' 1 (hbb.1.1 m)
  have hlA : lA W ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.Relay2.lA_mem W
  have hcoef : ∀ r m, lA W ^ (σ - sg) * algebraMap O (LetA O n) (g r m) * a r ∈ W.AΔ :=
    fun r m => W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hlA _) (W.AΔ.algebraMap_mem _)) (ha r)
  set lam₀ : W.DD T₂ := ∑ r ∈ Finset.range M, ∑ m,
    (lA W ^ (σ - sg) * algebraMap O (LetA O n) (g r m) * a r) • β m with hl0
  have hlam₀ : lam₀ ∈ Pp W T₂ c' 1 := by
    rw [hl0]
    exact AddSubgroup.sum_mem _ fun r _ => AddSubgroup.sum_mem _ fun m _ =>
      Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T₂ c' 1 (hcoef r m) _ (hβ m)
  set Z : W.DD T₂ := ∑ r ∈ Finset.range M, ∑ m,
    (-(lA W ^ (σ - sg) * lA W ^ (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) *
      algebraMap O (LetA O n) (g r m) * B' r)) • β m with hZdef
  have hZ : Z ∈ Pp W T₂ c' 1 := by
    rw [hZdef]
    exact AddSubgroup.sum_mem _ fun r _ => AddSubgroup.sum_mem _ fun m _ =>
      Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T₂ c' 1 (W.AΔ.neg_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem
        (W.AΔ.pow_mem hlA _) (W.AΔ.pow_mem hlA _)) (W.AΔ.algebraMap_mem _)) (hB' r))) _ (hβ m)
  set Hh : W.DD T₂ := ∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T₂ bb (y r) with hHh
  have hφS : ((W.φD T₂) ^ 1) Hh = ∑ r ∈ Finset.range M, ∑ m,
      (((W.φA ^ 1) W.π₀) ^ r * algebraMap O (LetA O n) (y r m)) • β m := by
    rw [hHh, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul, map_pow, Formalism.MainNotions.LiftingTheory.vecB, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, ← algebraMap_smul (LetA O n) (y r m), smul_smul]
  have key : lA W ^ κ • lam₀ - lA W ^ σ • ((W.φD T₂) ^ 1) Hh = JJ1 • Z := by
    rw [hφS, hl0, hZdef, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul, smul_smul, smul_smul, ← sub_smul]
    congr 1
    have hle := Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl (Finset.mem_range.1 hr).le
    have := ring_identity_lambda_terms (lA W) (((W.φA ^ 1) W.π₀) ^ r)
      (algebraMap O (LetA O n) (g r m)) (a r) (B' r) JJ1
      (σ - sg) sg (κ - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) (Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) κ σ
      (by omega) (by omega) (heq r m)
    rw [hyA]
    linear_combination this
  obtain ⟨x, hx, hxe⟩ := (hbb.2 k₀).1 M κ y hy
  rw [smul_zero, sub_zero, ← hHh] at hxe
  have hγφ : ∀ (e : ℕ) (z : W.DD T₂), W.γ T₂ (((W.φD T₂) ^ e) z) = ((W.φD T₂) ^ e) (W.γ T₂ z) :=
    fun e z => Formalism.MainNotions.UnusedSlot80.Relay2.γ_φpow W T₂ W.gam e z
  have hA1 : InFP W T₂ c' 1 JJ1 (W.γ T₂ (((W.φD T₂) ^ 1) Hh) - ((W.φD T₂) ^ 1) Hh) := by
    rw [hγφ, ← map_sub, hxe]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.phij_pi0pow W T₂ c' hC.hπ hC.Tr2 1 (2 * A.G₀) M hM hx
  obtain ⟨ka, hka, -, hγπ⟩ := gamma_pi0_eq_pi0_mul_one_add_unit_mul_q W hcase hP9
  have hqA : qA W ∈ W.AΔ := W.AΔ.add_mem hC.hπ hlA
  have hγJJ : W.γA W.gam JJ1 = JJ1 * ((1 + ka * qA W) ^ M * (1 + W.π₀ * ka) ^ (2 * A.G₀)) := by
    have hq : W.γA W.gam (Formalism.MainNotions.LiftingTheory.pk W 0) = Formalism.MainNotions.LiftingTheory.pk W 0 * (1 + W.π₀ * ka) := by
      have e1 : Formalism.MainNotions.LiftingTheory.pk W 0 = W.π₀ + lA W := by simp [Formalism.MainNotions.LiftingTheory.pk, Formalism.MainNotions.LiftingTheory.qp, lA]
      have e2 : W.γA W.gam (lA W) = lA W := by simp [lA]
      rw [e1, map_add, e2, hγπ]
      simp only [qA]
      ring
    simp only [hJJ1, Formalism.MainNotions.LiftingTheory.JJ, Finset.prod_range_one, map_mul, map_pow, hq, hγπ, mul_pow]
    ring
  have hu : (1 + ka * qA W) ^ M * (1 + W.π₀ * ka) ^ (2 * A.G₀) ∈ W.AΔ :=
    W.AΔ.mul_mem (W.AΔ.pow_mem (W.AΔ.add_mem W.AΔ.one_mem (W.AΔ.mul_mem hka hqA)) _)
      (W.AΔ.pow_mem (W.AΔ.add_mem W.AΔ.one_mem (W.AΔ.mul_mem hC.hπ hka)) _)
  have hγsm : ∀ (f : LetA O n) (z : W.DD T₂), W.γ T₂ (f • z) = W.γA W.gam f • W.γ T₂ z := by
    intro f z
    show W.γD T₂ W.gam (f • z) = W.γA W.gam f • W.γD T₂ W.gam z
    rw [← algebraMap_smul W.EE f z, W.γD_smul, W.γE_ext, algebraMap_smul]
    rfl
  have hJZ : InFP W T₂ c' 1 JJ1 (W.γ T₂ (JJ1 • Z) - JJ1 • Z) := by
    rw [hγsm, hγJJ, mul_smul, ← smul_sub]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_of_mem W T₂ c' 1 JJ1
      (sub_mem (Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T₂ c' 1 hu _
        (Formalism.MainNotions.UnusedSlot80.Relay2.Pp_γ W T₂ c' 1 _ hZ)) hZ)
  have hkey' : lA W ^ κ • lam₀ = lA W ^ σ • ((W.φD T₂) ^ 1) Hh + JJ1 • Z := by
    rw [← key]; abel
  have hγl : InFP W T₂ c' 1 JJ1 (lA W ^ κ • (W.γ T₂ lam₀ - lam₀)) := by
    have e : lA W ^ κ • (W.γ T₂ lam₀ - lam₀) =
        lA W ^ σ • (W.γ T₂ (((W.φD T₂) ^ 1) Hh) - ((W.φD T₂) ^ 1) Hh) +
          (W.γ T₂ (JJ1 • Z) - JJ1 • Z) := by
      rw [smul_sub, ← Formalism.MainNotions.UnusedSlot80.Relay2.γ_lsmul, hkey', map_add, Formalism.MainNotions.UnusedSlot80.Relay2.γ_lsmul,
        smul_sub]
      abel
    rw [e]
    exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_add W T₂ c' 1 JJ1
      (Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_lA_pow_smul W T₂ c' 1 JJ1 σ hA1) hJZ
  have hsub : W.γ T₂ lam₀ - lam₀ ∈ Pp W T₂ c' 1 :=
    sub_mem (Formalism.MainNotions.UnusedSlot80.Relay2.Pp_γ W T₂ c' 1 _ hlam₀) hlam₀
  obtain ⟨Y, hY, hYe⟩ := Formalism.MainNotions.UnusedSlot80.Relay2.satP_JJ W hSatP hcase hC.hπ T₂ hT₂ c' 1 (2 * A.G₀) M _
    hsub κ hγl
  have hφ2 : ∀ z : W.DD T₂, ((W.φD T₂) ^ 2) z = ((W.φD T₂) ^ 1) (((W.φD T₂) ^ 1) z) := fun z => by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_add]; rfl
  have hφP : ∀ z ∈ Pp W T₂ c' 1, ((W.φD T₂) ^ 1) z ∈ Pp W T₂ c' 2 := by
    refine Formalism.MainNotions.UnusedSlot80.Relay2.Pp_ind W T₂ c' 1 (fun z => ((W.φD T₂) ^ 1) z ∈ Pp W T₂ c' 2) ?_ ?_ ?_ ?_
    · rw [map_zero]; exact (Pp W T₂ c' 2).zero_mem
    · intro z z' hz hz'; rw [map_add]; exact (Pp W T₂ c' 2).add_mem hz hz'
    · intro z hz; rw [map_neg]; exact (Pp W T₂ c' 2).neg_mem hz
    · intro f hf z hz
      rw [Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul, ← hφ2]
      exact Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T₂ c' 2 (Formalism.MainNotions.UnusedSlot80.PhiPowers.φA_pow_mem_AΔ W hf 1) hz
  refine ⟨((W.φD T₂) ^ 1) lam₀, κ, Hh, ?_, ?_, ⟨y, hy, rfl⟩, 0, ?_⟩
  · exact ⟨_, hφP _ hlam₀, (one_smul _ _).symm⟩
  · refine ⟨((W.φD T₂) ^ 1) Y, hφP _ hY, ?_⟩
    rw [hγφ, ← map_sub, hYe, Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul, pow_one W.φA]
  · refine ⟨((W.φD T₂) ^ 1) Z, hφP _ hZ, ?_⟩
    rw [pow_zero, one_smul, hφ2, ← Formalism.MainNotions.UnusedSlot80.Relay2.φpow_lsmul, ← Formalism.MainNotions.UnusedSlot80.Relay2.φpow_lsmul,
      ← map_sub, key, Formalism.MainNotions.UnusedSlot80.Relay2.φpow_smul, pow_one W.φA]

end Formalism.MainNotions.N.FrobeniusPowerSeries
