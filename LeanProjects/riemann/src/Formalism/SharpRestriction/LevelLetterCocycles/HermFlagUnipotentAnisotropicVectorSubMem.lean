import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
import Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool
import Formalism.SharpRestriction.LevelLetterCocycles.CompleteOfPow
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegerSpanGenerators

open Classical

noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.UnusedSlot80.Relay2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem letE_γ (T : LocLat G Qp LL O) (i : ZMod n) (x : W.DD T) :
    (letE i : LetA O n) • W.γ T x = W.γ T ((letE i : LetA O n) • x) := by
  show (letE i : LetA O n) • W.γD T W.gam x = W.γD T W.gam ((letE i : LetA O n) • x)
  rw [Formalism.MainNotions.LiftingTheory.frame_γD_smul, Formalism.MainNotions.LiftingTheory.frame_γA_letE]

theorem z_of_InI (T : LocLat G Qp LL O) (i : ZMod n) {w : W.DD T} (hw : Formalism.MainNotions.CrystallineLiftingInputs.InI W T i w) :
    ∃ z', Formalism.MainNotions.LiftingTheory.InNΔi W T i z' ∧ W.γ T w - w = W.π₀ • z' := by
  obtain ⟨⟨hwl, -⟩, -, y, hy, hyΔ, hyw⟩ := hw
  refine ⟨(letE i : LetA O n) • y, InNΔi_of W T i
    (Formalism.MainNotions.UnusedSlot80.SatW.smul_mem_NΔ W T (Formalism.MainNotions.LiftingTheory.idempotent_mem_invariants W i) ⟨hy, hyΔ⟩)
    (by rw [smul_smul, letE_mul_self]), ?_⟩
  rw [smul_comm, ← pow_one W.π₀, ← hyw, smul_sub, letE_γ, hwl]

theorem DL_of (T : LocLat G Qp LL O) (i : ZMod n) {x : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) :
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x ∧ x ∈ W.N T :=
  ⟨⟨InNΔi_letter W T i hx, hx.1.2⟩, hx.1.1⟩

theorem InNΔi_of_DL (T : LocLat G Qp LL O) (i : ZMod n) {x : W.DD T} (h : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x)
    (hN : x ∈ W.N T) : Formalism.MainNotions.LiftingTheory.InNΔi W T i x :=
  InNΔi_of W T i ⟨hN, h.2⟩ h.1

theorem eY_eq (l y : ℕ) : Formalism.MainNotions.CrystallineLiftingInputs.eY l y = Ex l y := rfl

theorem γsum (T : LocLat G Qp LL O) (K : ℕ) (a : ℕ → ℕ) (c : ℕ → W.DD T) :
    ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ a y • (W.γ T (W.π₀ ^ y • c y) - W.π₀ ^ y • c y) =
      W.γ T (∑ y ∈ Finset.range K, W.π₀ ^ y • (((PD.p : ℕ) : O) ^ a y • c y)) -
        ∑ y ∈ Finset.range K, W.π₀ ^ y • (((PD.p : ℕ) : O) ^ a y • c y) := by
  rw [map_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_comm (W.π₀ ^ y) (((PD.p : ℕ) : O) ^ a y) (c y), (W.γ T).map_smul, smul_sub]

theorem alg_uniq {M : Type} [AddCommGroup M] [Module O M] (u1 u2 : O) (P Sc Sc' A A' : M)
    (h1 : u1 • (P - Sc) = A) (h2 : u2 • (P - Sc') = A') : (u1 * u2) • (Sc - Sc') = u1 • A' - u2 • A := by
  rw [← h1, ← h2]
  simp only [smul_sub, smul_smul]
  rw [mul_comm u2 u1]
  abel

theorem ser_exists [NeZero n] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (i : ZMod n) (w : W.DD T) (hw : Formalism.MainNotions.CrystallineLiftingInputs.InI W T i w) : ∃ c, Formalism.MainNotions.CrystallineLiftingInputs.IsSer W T i w c := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  obtain ⟨d, b, cf, hb, hsol, hc0, hbd⟩ :=
    solData W T i (Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hA T hT).2 (hH hA T hT i).2.2.1 _ (z_of_InI W T i hw)
  have h4 := (hH hA T hT i).2.2.2.1
  have hg : ∀ r m, ∃ o : O, algebraMap O LL o = (PD.p : LL) ^ Ex PD.p r * cf r m :=
    fun r m => int_of_bd W hO2 r (h4 r) _ (hbd r m)
  choose g hg using hg
  have hg0 : g 0 = 0 := by
    funext m
    apply hinj
    rw [hg, hc0]
    simp
  refine ⟨fun y => Formalism.MainNotions.LiftingTheory.vecB W T b (g y), ?_, fun y => ?_, fun K => ?_⟩
  · show Formalism.MainNotions.LiftingTheory.vecB W T b (g 0) = 0
    rw [hg0]
    simp [Formalism.MainNotions.LiftingTheory.vecB]
  · exact DL_of W T i (Formalism.MainNotions.LiftingTheory.frame_vecB_mem W T i b hb _)
  · refine ⟨0, ?_⟩
    set yv : ℕ → Fin d → O := fun r m => ((PD.p : ℕ) : O) ^ (Ex PD.p K - Ex PD.p r) * g r m
    have hy : ∀ r < K, ∀ m, algebraMap O LL (yv r m) = (PD.p : LL) ^ Ex PD.p K * cf r m := by
      intro r hr m
      have hle := Ex_mono PD.p hl hr.le
      simp only [yv, map_mul, map_pow, map_natCast, hg]
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    obtain ⟨x, hx, hxe⟩ := hsol K (Ex PD.p K) yv hy
    refine ⟨-x, (W.N T).neg_mem hx.1.1, fun δ hδ => by rw [map_neg, hx.1.2 δ hδ], ?_⟩
    have hv : ∀ r, Formalism.MainNotions.LiftingTheory.vecB W T b (yv r) =
        ((PD.p : ℕ) : O) ^ (Ex PD.p K - Ex PD.p r) • Formalism.MainNotions.LiftingTheory.vecB W T b (g r) :=
      fun r => Formalism.MainNotions.LiftingTheory.frame_vecB_smul W T b _ (g r)
    simp only [hv] at hxe
    rw [γsum, pow_zero, one_smul, smul_neg, ← hxe]
    simp only [eY_eq]
    abel

theorem ser_unique [NeZero n] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (i : ZMod n) (w : W.DD T) (c c' : ℕ → W.DD T) (hc : Formalism.MainNotions.CrystallineLiftingInputs.IsSer W T i w c)
    (hc' : Formalism.MainNotions.CrystallineLiftingInputs.IsSer W T i w c') (K : ℕ) : ∃ j : ℕ,
      Formalism.MainNotions.CrystallineLiftingInputs.InPN W T K (((PD.p : ℕ) : O) ^ j • ∑ y ∈ Finset.range K,
        ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) •
          (W.π₀ ^ y • (c y - c' y))) := by
  have hr := (Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hA T hT).1
  obtain ⟨hc0, hcN, hcK⟩ := hc
  obtain ⟨hc0', hcN', hcK'⟩ := hc'
  obtain ⟨j1, a, ha, haΔ, hae⟩ := hcK K
  obtain ⟨j2, a', ha', haΔ', hae'⟩ := hcK' K
  set ex : ℕ → ℕ := fun y => Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y
  have he : ∀ y, Formalism.MainNotions.LiftingTheory.InNΔi W T i (c y - c' y) := fun y =>
    InNΔi_sub W T i (InNΔi_of_DL W T i (hcN y).1 (hcN y).2) (InNΔi_of_DL W T i (hcN' y).1 (hcN' y).2)
  set E : W.DD T := ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ ex y • (W.π₀ ^ y • (c y - c' y)) with hE

  have hterm : ∀ y, W.π₀ ^ y • (c y - c' y) = W.π₀ • (W.π₀ ^ (y - 1) • (c y - c' y)) := by
    intro y
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · rw [hc0, hc0', sub_self]; simp
    · rw [smul_smul, ← pow_succ', Nat.sub_add_cancel hy]
  set E' : W.DD T := ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ ex y • (W.π₀ ^ (y - 1) • (c y - c' y))
  have hEE' : E = W.π₀ • E' := by
    rw [hE, Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hterm, smul_comm]
  have hE'N : Formalism.MainNotions.LiftingTheory.InNΔi W T i E' :=
    InNΔi_sum W T i _ _ fun y _ => InNΔi_osmul W T i _ (InNΔi_smul W T i (W.AΔ.pow_mem hr.1 _) (he y))

  have hγE : W.γ T E - E = ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ ex y •
        (W.γ T (W.π₀ ^ y • c y) - W.π₀ ^ y • c y) -
      ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ ex y •
        (W.γ T (W.π₀ ^ y • c' y) - W.π₀ ^ y • c' y) := by
    have hy : ∀ y, W.γ T (((PD.p : ℕ) : O) ^ ex y • (W.π₀ ^ y • (c y - c' y))) -
        ((PD.p : ℕ) : O) ^ ex y • (W.π₀ ^ y • (c y - c' y)) =
        ((PD.p : ℕ) : O) ^ ex y • (W.γ T (W.π₀ ^ y • c y) - W.π₀ ^ y • c y) -
        ((PD.p : ℕ) : O) ^ ex y • (W.γ T (W.π₀ ^ y • c' y) - W.π₀ ^ y • c' y) := by
      intro y
      rw [(W.γ T).map_smul, smul_sub (W.π₀ ^ y) (c y) (c' y), map_sub]
      simp only [smul_sub]
      abel
    rw [hE, map_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => hy y
  set E2 : W.DD T := ((PD.p : ℕ) : O) ^ (j1 + j2) • E
  have hlet : ∀ y, (letE i : LetA O n) • (W.π₀ ^ y • (c y - c' y)) = W.π₀ ^ y • (c y - c' y) := by
    intro y
    rw [smul_comm, InNΔi_letter W T i (he y)]
  have hEl : (letE i : LetA O n) • E = E := by
    rw [hE, Finset.smul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [smul_comm, hlet]
  have hz0 : W.γ T E2 - E2 = W.π₀ ^ K •
      (((PD.p : ℕ) : O) ^ j1 • a' - ((PD.p : ℕ) : O) ^ j2 • a) := by
    have e1 : W.γ T E2 - E2 = ((PD.p : ℕ) : O) ^ (j1 + j2) • (W.γ T E - E) := by
      rw [(W.γ T).map_smul, smul_sub]
    rw [e1, hγE, pow_add, alg_uniq _ _ _ _ _ _ _ hae hae', smul_comm (((PD.p : ℕ) : O) ^ j1) (W.π₀ ^ K) a',
      smul_comm (((PD.p : ℕ) : O) ^ j2) (W.π₀ ^ K) a, ← smul_sub]
  set z0 : W.DD T := ((PD.p : ℕ) : O) ^ j1 • a' - ((PD.p : ℕ) : O) ^ j2 • a
  have hz : Formalism.MainNotions.LiftingTheory.InNΔi W T i ((letE i : LetA O n) • z0) :=
    InNΔi_of W T i (Formalism.MainNotions.UnusedSlot80.SatW.smul_mem_NΔ W T (Formalism.MainNotions.LiftingTheory.idempotent_mem_invariants W i)
      ((W.NΔ T).sub_mem ((W.NΔ T).smul_mem _ ⟨ha', haΔ'⟩) ((W.NΔ T).smul_mem _ ⟨ha, haΔ⟩)))
      (by rw [smul_smul, letE_mul_self])
  have hzE : W.γ T E2 - E2 = W.π₀ ^ K • ((letE i : LetA O n) • z0) := by
    rw [smul_comm, ← hz0, smul_sub, letE_γ]
    have : (letE i : LetA O n) • E2 = E2 := by
      show (letE i : LetA O n) • (((PD.p : ℕ) : O) ^ (j1 + j2) • E) = _
      rw [smul_comm, hEl]
    rw [this]
  obtain ⟨k, x, hx, hkx⟩ := formal_unique W T i hinj hO2 hr.1 hr.2.2.1 (hH hA T hT i).1
    (hH hA T hT i).2.1 K E2 ⟨((PD.p : ℕ) : O) ^ (j1 + j2) • E', InNΔi_osmul W T i _ hE'N, by
      show ((PD.p : ℕ) : O) ^ (j1 + j2) • E = _
      rw [hEE', smul_comm]⟩ ⟨_, hz, hzE⟩
  refine ⟨k + (j1 + j2), x, hx.1.1, hx.1.2, ?_⟩
  rw [← hkx, ← lsmul_eq, pow_add, mul_smul]

theorem tTool1_of [NeZero n] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) : Formalism.MainNotions.CrystallineLiftingInputs.TTool1 W := by
  intro hA T hT i w hw
  exact ⟨ser_exists W hinj hO2 h9 hH hA T hT i w hw,
    fun c c' hc hc' K => ser_unique W hinj hO2 h9 hH hA T hT i w c c' hc hc' K⟩

end Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Classical

noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.UnusedSlot80.Relay2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

include W in

theorem l_ne : ((PD.p : ℕ) : O) ≠ 0 := by
  intro h
  apply Formalism.MainNotions.LiftingTheory.tr_pLL_ne W
  have := congrArg (algebraMap O LL) h
  rwa [map_natCast, map_zero] at this

theorem l_reg [IsDomain O] (hl : ((PD.p : ℕ) : O) ≠ 0) (k : ℕ) {x y : LetA O n}
    (h : ((PD.p : ℕ) : LetA O n) ^ k * x = ((PD.p : ℕ) : LetA O n) ^ k * y) : x = y := by
  funext i
  ext m
  have h1 := congrArg (fun t : LetA O n => PowerSeries.coeff m (t i)) h
  simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply] at h1
  rw [← map_natCast (PowerSeries.C (R := O)), ← map_pow, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul] at h1
  exact mul_left_cancel₀ (pow_ne_zero k hl) h1

theorem s_mem [IsDomain O] (hl : ((PD.p : ℕ) : O) ≠ 0) {e σ : ℕ} {r s : LetA O n} (hr : r ∈ W.AΔ)
    (h : ((PD.p : ℕ) : LetA O n) ^ e * s = ((PD.p : ℕ) : LetA O n) ^ σ * r) : s ∈ W.AΔ := by
  intro δ hδ
  apply l_reg hl e
  have h1 := congrArg (W.γA δ) h
  rw [map_mul, map_mul, map_pow, map_pow, map_natCast, hr δ hδ, ← h] at h1
  exact h1

theorem rem_mem (hπ : W.π₀ ∈ W.AΔ) {j M X y : ℕ} {r : LetA O n}
    (h : Formalism.MainNotions.CrystallineLiftingInputs.IsRem W j M X y r) : r ∈ W.AΔ := by
  obtain ⟨⟨a, rfl⟩, -⟩ := h
  exact W.AΔ.sum_mem fun k _ => W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hπ _)

theorem f_mem (hπ : W.π₀ ∈ W.AΔ) (M X : ℕ) : Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X ∈ W.AΔ :=
  W.AΔ.mul_mem (W.AΔ.pow_mem hπ _) (W.AΔ.pow_mem (Formalism.MainNotions.LiftingTheory.lifta_qΔ W hπ) _)

theorem f_unit (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (M X : ℕ) :
    IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X)) := by
  rw [Formalism.MainNotions.CrystallineLiftingInputs.fMX, map_mul, map_pow, map_pow]
  exact (hR.πU.pow _).mul (hR.qU.pow _)

theorem g_mem (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) {j M X y : ℕ} {r : LetA O n}
    (h : Formalism.MainNotions.CrystallineLiftingInputs.IsRem W j M X y r) : ∃ g ∈ W.AΔ,
      ((W.φA ^ j) W.π₀) ^ y - r = Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X * g := by
  obtain ⟨g, hg⟩ := h.2
  refine ⟨g, Formalism.MainNotions.LiftingTheory.lifta_divΔ W _ g (f_mem W hR.πΔ M X) (f_unit W hR M X) ?_, hg⟩
  rw [← hg]
  exact W.AΔ.sub_mem (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.φA_pow_mem_AΔ W hR.πΔ j) _) (rem_mem W hR.πΔ h)

theorem qp_ps : Formalism.MainNotions.LiftingTheory.qp W = Formalism.MainNotions.ArcLiftingSetup.ps W 0 := by
  simp [Formalism.MainNotions.LiftingTheory.qp, Formalism.MainNotions.ArcLiftingSetup.ps, Formalism.MainNotions.ArcLiftingSetup.qA, Formalism.MainNotions.ArcLiftingSetup.lA]

theorem f_PiPs (M X : ℕ) : Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X ∈ Formalism.MainNotions.ArcLiftingSetup.PiPs W := by
  refine Submonoid.mul_mem _ (Submonoid.pow_mem _ (Submonoid.subset_closure (Set.mem_insert _ _)) _)
    (Submonoid.pow_mem _ (Submonoid.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range.2 ⟨0, (qp_ps W).symm⟩))) _)

theorem f_γ (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (M X : ℕ) :
    ∃ u, W.γA W.gam (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X) = u * Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X ∧ u ∈ W.AΔ := by
  obtain ⟨t, ht, hγπ⟩ := hR.γπ
  obtain ⟨t', ht', hγq⟩ := hR.γq
  refine ⟨(algebraMap O (LetA O n) (Formalism.MainNotions.LiftingTheory.u₁ W) + W.π₀ * t) ^ M * (1 + W.π₀ * t') ^ X, ?_, ?_⟩
  · rw [Formalism.MainNotions.CrystallineLiftingInputs.fMX, map_mul, map_pow, map_pow, hγπ, hγq, mul_pow, mul_pow]
    ring
  · exact W.AΔ.mul_mem (W.AΔ.pow_mem (W.AΔ.add_mem (W.AΔ.algebraMap_mem _) (W.AΔ.mul_mem hR.πΔ ht)) _)
      (W.AΔ.pow_mem (W.AΔ.add_mem W.AΔ.one_mem (W.AΔ.mul_mem hR.πΔ ht')) _)

theorem keyF (hπ : W.π₀ ∈ W.AΔ)
    (h2 : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * r))
    (T : LocLat G Qp LL O) (i : ZMod n) {j : ℕ} (hj : 1 ≤ j) (M X : ℕ) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T i j (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X) (((W.φD T) ^ j) (W.π₀ ^ (max M X + 1) • x)) := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  have hM : X ≤ (PD.p - 1) * (max M X + 1) := by
    have : X ≤ max M X + 1 := by omega
    calc X ≤ max M X + 1 := this
      _ = 1 * (max M X + 1) := (one_mul _).symm
      _ ≤ (PD.p - 1) * (max M X + 1) := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨y, hy, hyx⟩ := phij_pi0pow W T i hπ h2 j X (max M X + 1) hM hx
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  set e : LetA O n := W.π₀ ^ (max M X + 1 - M) * ∏ k ∈ Finset.range j', Formalism.MainNotions.LiftingTheory.pk W (k + 1) ^ X
  have he : e ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.pow_mem hπ _)
    (W.AΔ.prod_mem fun k _ => W.AΔ.pow_mem (pk_mem_AΔ W hπ _) _)
  have hJ : Formalism.MainNotions.LiftingTheory.JJ W (j' + 1) X (max M X + 1) = Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X * e := by
    rw [Formalism.MainNotions.LiftingTheory.JJ, Finset.prod_range_succ', Formalism.MainNotions.CrystallineLiftingInputs.fMX]
    have hp0 : Formalism.MainNotions.LiftingTheory.pk W 0 = Formalism.MainNotions.LiftingTheory.qp W := by simp [Formalism.MainNotions.LiftingTheory.pk]
    rw [hp0]
    have : W.π₀ ^ (max M X + 1) = W.π₀ ^ M * W.π₀ ^ (max M X + 1 - M) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    ring
  refine ⟨e • y, Pp_smul W T i _ he y hy, ?_⟩
  rw [hyx, hJ, mul_smul]

theorem pp_pull (T : LocLat G Qp LL O) (i : ZMod n) (j : ℕ) :
    ∀ y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T i j, y ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T i j := by
  refine Pp_ind W T i j _ (Submodule.zero_mem _) (fun x y hx hy => Submodule.add_mem _ hx hy)
    (fun x hx => Submodule.neg_mem _ hx) ?_
  intro a _ x hx
  exact Submodule.smul_mem _ a (Submodule.subset_span ⟨x, ⟨hx.1.1, InNΔi_letter W T i hx, hx.1.2⟩, rfl⟩)

theorem fp_pull (T : LocLat G Qp LL O) (i : ZMod n) (j : ℕ) (f : LetA O n) {x : W.DD T}
    (h : Formalism.MainNotions.ArcLiftingSetup.InFP W T i j f x) : ∃ p ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T i j, x = f • p := by
  obtain ⟨y, hy, rfl⟩ := h
  exact ⟨y, pp_pull W T i j y hy, rfl⟩

theorem sat (hsp : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) (i : ZMod n) (j M X : ℕ) {x : W.DD T} (hx : x ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T i j) (k : ℕ)
    (h : Formalism.MainNotions.ArcLiftingSetup.InFP W T i j (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X) (((PD.p : ℕ) : O) ^ k • x)) :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T i j (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X) x := by
  refine hsp hA T i j _ 1 hT (f_PiPs W M X) (Submonoid.one_mem _) x ⟨x, hx, by simp⟩ ⟨k, ?_⟩
  rw [← lsmul_eq]
  exact h

theorem term_id {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (L f Φ r s g : A) {e σ N : ℕ}
    (hle : e ≤ N) (hs : L ^ e * s = L ^ σ * r) (hg : Φ - r = f * g) (P : M) :
    L ^ N • (s • P) = L ^ σ • (L ^ (N - e) • (Φ • P)) - f • ((L ^ (N - e) * L ^ σ * g) • P) := by
  obtain ⟨d, rfl⟩ : ∃ d, N = e + d := ⟨N - e, by omega⟩
  rw [Nat.add_sub_cancel_left, smul_smul, smul_smul, smul_smul, smul_smul, ← sub_smul]
  congr 1
  linear_combination L ^ d * hs - L ^ d * L ^ σ * hg

theorem eY_mono {y Y : ℕ} (h : y ≤ Y) : Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y ≤ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p Y :=
  Ex_mono PD.p PD.hp.two_le h

theorem InNΔi_c (T : LocLat G Qp LL O) (i : ZMod n) {w : W.DD T} {c : ℕ → W.DD T}
    (hc : Formalism.MainNotions.CrystallineLiftingInputs.IsSer W T i w c) (y : ℕ) : Formalism.MainNotions.LiftingTheory.InNΔi W T i (c y) :=
  InNΔi_of_DL W T i (hc.2.1 y).1 (hc.2.1 y).2

theorem red (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (T : LocLat G Qp LL O) (i : ZMod n) {j M X σ : ℕ}
    {w z : W.DD T} {c : ℕ → W.DD T} {r s : ℕ → LetA O n}
    (hc : Formalism.MainNotions.CrystallineLiftingInputs.IsSer W T i w c)
    (hrs : ∀ y, Formalism.MainNotions.CrystallineLiftingInputs.IsRem W j M X y (r y) ∧
      ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y * s y = ((PD.p : ℕ) : LetA O n) ^ σ * r y)
    (hz : z = ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) w -
      ∑ y ∈ Finset.range (max M X + 1), s y • ((W.φD T) ^ j) (c y)) (t : ℕ) :
    ∃ Gv ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T i j,
      ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p (max M X + 1) + t) • z =
        ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j)
          (((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p (max M X + 1) + t) • w -
            ∑ y ∈ Finset.range (max M X + 1),
              ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p (max M X + 1) + t - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) •
                (W.π₀ ^ y • c y)) +
        Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X • Gv := by
  set K0 := max M X + 1
  set N := Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K0 + t
  have hg := fun y => g_mem W hR (hrs y).1
  choose g hgA hg using hg
  set L : LetA O n := Formalism.MainNotions.ArcLiftingSetup.lA W
  refine ⟨∑ y ∈ Finset.range K0, (L ^ (N - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) * L ^ σ * g y) •
      ((W.φD T) ^ j) (c y), ?_, ?_⟩
  · exact (Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).sum_mem fun y _ => Pp_gen W T i j
      (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (lA_mem W) _) (W.AΔ.pow_mem (lA_mem W) _)) (hgA y))
      (InNΔi_c W T i hc y)
  have e1 : ∀ y ∈ Finset.range K0, ((PD.p : ℕ) : O) ^ N • (s y • ((W.φD T) ^ j) (c y)) =
      ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) (((PD.p : ℕ) : O) ^ (N - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) •
        (W.π₀ ^ y • c y)) -
      Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X • ((L ^ (N - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) * L ^ σ * g y) • ((W.φD T) ^ j) (c y)) := by
    intro y hy
    have hle : Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y ≤ N :=
      le_trans (eY_mono (PD := PD) (le_of_lt (Finset.mem_range.1 hy))) (Nat.le_add_right _ _)
    rw [LinearMap.map_smul_of_tower, φpow_smul, map_pow, lsmul_eq, lsmul_eq, lsmul_eq]
    exact term_id L _ _ _ _ _ hle (hrs y).2 (hg y) _
  rw [hz, smul_sub, Finset.smul_sum, Finset.sum_congr rfl e1, Finset.sum_sub_distrib, map_sub,
    LinearMap.map_smul_of_tower, map_sum, smul_sub, Finset.smul_sum, smul_comm (((PD.p : ℕ) : O) ^ N)]
  simp only [Finset.smul_sum]
  abel

theorem L_sub {T : LocLat G Qp LL O} {i : ZMod n} {x y : W.DD T} (hx : (letE i : LetA O n) • x = x)
    (hy : (letE i : LetA O n) • y = y) : (letE i : LetA O n) • (x - y) = x - y := by
  rw [smul_sub, hx, hy]

theorem L_add {T : LocLat G Qp LL O} {i : ZMod n} {x y : W.DD T} (hx : (letE i : LetA O n) • x = x)
    (hy : (letE i : LetA O n) • y = y) : (letE i : LetA O n) • (x + y) = x + y := by
  rw [smul_add, hx, hy]

theorem L_smul {T : LocLat G Qp LL O} {i : ZMod n} {x : W.DD T} (a : LetA O n)
    (hx : (letE i : LetA O n) • x = x) : (letE i : LetA O n) • (a • x) = a • x := by
  rw [smul_comm, hx]

theorem L_osmul {T : LocLat G Qp LL O} {i : ZMod n} {x : W.DD T} (a : O)
    (hx : (letE i : LetA O n) • x = x) : (letE i : LetA O n) • (a • x) = a • x := by
  rw [smul_comm, hx]

theorem L_sum {T : LocLat G Qp LL O} {i : ZMod n} (s : Finset ℕ) (g : ℕ → W.DD T)
    (h : ∀ y ∈ s, (letE i : LetA O n) • g y = g y) :
    (letE i : LetA O n) • ∑ y ∈ s, g y = ∑ y ∈ s, g y := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl h

theorem L_γ {T : LocLat G Qp LL O} {i : ZMod n} {x : W.DD T} (hx : (letE i : LetA O n) • x = x) :
    (letE i : LetA O n) • W.γ T x = W.γ T x := by
  rw [letE_γ, hx]

theorem let_fix (T : LocLat G Qp LL O) (i : ZMod n) (K : ℕ) {v a : W.DD T} (ha : a ∈ W.N T)
    (haΔ : ∀ δ ∈ W.DelF, W.γD T δ a = a) (hv : (letE i : LetA O n) • v = v) (hva : v = W.π₀ ^ K • a) :
    Formalism.MainNotions.LiftingTheory.InNΔi W T i ((letE i : LetA O n) • a) ∧ v = W.π₀ ^ K • ((letE i : LetA O n) • a) := by
  refine ⟨InNΔi_of W T i (Formalism.MainNotions.UnusedSlot80.SatW.smul_mem_NΔ W T (Formalism.MainNotions.LiftingTheory.idempotent_mem_invariants W i) ⟨ha, haΔ⟩)
    (by rw [smul_smul, letE_mul_self]), ?_⟩
  rw [smul_comm, ← hva, hv]

def E0 (T : LocLat G Qp LL O) (K : ℕ) (w : W.DD T) (c : ℕ → W.DD T) : W.DD T :=
  ((PD.p : ℕ) : O) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K • w -
    ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) •
      (W.π₀ ^ y • c y)

theorem truncatedSeries_pow_shift (T : LocLat G Qp LL O) (K t : ℕ) (w : W.DD T) (c : ℕ → W.DD T) :
    ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K + t) • w -
      ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K + t - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) •
        (W.π₀ ^ y • c y) = ((PD.p : ℕ) : O) ^ t • E0 W T K w c := by
  rw [E0, smul_sub, Finset.smul_sum, ← mul_smul, ← pow_add, add_comm t]
  congr 1
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [← mul_smul, ← pow_add]
  congr 2
  have := eY_mono (PD := PD) (le_of_lt (Finset.mem_range.1 hy))
  omega

theorem truncatedSeries_gamma_sub (T : LocLat G Qp LL O) (K : ℕ) (w : W.DD T) (c : ℕ → W.DD T) :
    W.γ T (E0 W T K w c) - E0 W T K w c =
      ((PD.p : ℕ) : O) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K • (W.γ T w - w) -
        ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) •
          (W.γ T (W.π₀ ^ y • c y) - W.π₀ ^ y • c y) := by
  rw [E0, map_sub, (W.γ T).map_smul, map_sum]
  simp only [(W.γ T).map_smul, smul_sub, Finset.sum_sub_distrib]
  abel

theorem truncatedSeries_sub (T : LocLat G Qp LL O) (K : ℕ) (w : W.DD T) (c c' : ℕ → W.DD T) :
    E0 W T K w c - E0 W T K w c' = -∑ y ∈ Finset.range K,
      ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) • (W.π₀ ^ y • (c y - c' y)) := by
  rw [E0, E0]
  simp only [smul_sub, Finset.sum_sub_distrib]
  abel

theorem idempotent_smul_truncatedSeries (T : LocLat G Qp LL O) (i : ZMod n) (K : ℕ) {w : W.DD T} {c : ℕ → W.DD T}
    (hw : (letE i : LetA O n) • w = w) (hc : ∀ y, (letE i : LetA O n) • c y = c y) :
    (letE i : LetA O n) • E0 W T K w c = E0 W T K w c :=
  L_sub W (L_osmul W _ hw) (L_sum W _ _ fun y _ => L_osmul W _ (L_smul W _ (hc y)))

theorem S_mem [IsDomain O] (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (T : LocLat G Qp LL O) (i : ZMod n)
    {j M X σ : ℕ} {w : W.DD T} {c : ℕ → W.DD T} {r s : ℕ → LetA O n}
    (hc : Formalism.MainNotions.CrystallineLiftingInputs.IsSer W T i w c)
    (hrs : ∀ y, Formalism.MainNotions.CrystallineLiftingInputs.IsRem W j M X y (r y) ∧
      ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y * s y = ((PD.p : ℕ) : LetA O n) ^ σ * r y) :
    ∑ y ∈ Finset.range (max M X + 1), s y • ((W.φD T) ^ j) (c y) ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T i j :=
  (Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).sum_mem fun y _ => Pp_gen W T i j
    (s_mem W (l_ne W) (rem_mem W hR.πΔ (hrs y).1) (hrs y).2) (InNΔi_c W T i hc y)

theorem b1 (T : LocLat G Qp LL O) (i : ZMod n) {j M X σ : ℕ} {w z : W.DD T}
    (hz : Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T i j M X σ w z) :
    z - ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) w ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T i j := by
  obtain ⟨c, r, s, hc, -, rfl⟩ := hz
  rw [sub_sub_cancel_left]
  refine Submodule.neg_mem _ (Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.subset_span ⟨c y, ⟨(hc.2.1 y).2, (hc.2.1 y).1⟩, rfl⟩

theorem gamma_sub_of_frobenius_power [IsDomain O] (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (hsp : Formalism.MainNotions.ArcLiftingSetup.SATPcore W)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (h2 : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * r))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) {j M X σ : ℕ} (hj : 1 ≤ j)
    {w z : W.DD T} (hw : Formalism.MainNotions.CrystallineLiftingInputs.InI W T i w) (hz : Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T i j M X σ w z) :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T i j (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X) (W.γ T z - z) := by
  obtain ⟨c, r, s, hc, hrs, hzd⟩ := hz
  set K0 := max M X + 1
  obtain ⟨t, a, ha, haΔ, hae⟩ := hc.2.2 K0
  obtain ⟨Gv, hGv, hred⟩ := red W hR T i hc hrs hzd t
  rw [truncatedSeries_pow_shift] at hred

  have hEl := idempotent_smul_truncatedSeries W T i K0 hw.1.1 fun y => (hc.2.1 y).1.1
  have hv : ((PD.p : ℕ) : O) ^ t • (W.γ T (E0 W T K0 w c) - E0 W T K0 w c) = W.π₀ ^ K0 • a := by
    rw [truncatedSeries_gamma_sub]; exact hae
  obtain ⟨ha', hva⟩ := let_fix W T i K0 ha haΔ (L_osmul W _ (L_sub W (L_γ W hEl) hEl)) hv

  obtain ⟨z', hz', hzw⟩ := z_of_InI W T i hw
  set S := ∑ y ∈ Finset.range K0, s y • ((W.φD T) ^ j) (c y)
  have hS := S_mem W hR T i hc hrs
  have hV : W.γ T z - z ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T i j := by
    have e : W.γ T z - z = ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) (W.π₀ • z') - (W.γ T S - S) := by
      have g1 : W.γ T (((W.φD T) ^ j) w) = ((W.φD T) ^ j) (W.γ T w) := γ_φpow W T W.gam j w
      rw [hzd, ← hzw, map_sub, (W.γ T).map_smul, map_sub, g1, smul_sub]
      abel
    rw [e]
    refine (Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).sub_mem (Pp_osmul W T i j _ _ ?_)
      ((Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).sub_mem (Pp_γ W T i j S hS) hS)
    rw [φpow_smul]
    exact Pp_gen W T i j (Formalism.MainNotions.UnusedSlot80.PhiPowers.φA_pow_mem_AΔ W hR.πΔ j) hz'
  refine sat W hsp hA T hT i j M X hV (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K0 + t) ?_
  have e2 : ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K0 + t) • (W.γ T z - z) =
      ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) (W.π₀ ^ K0 • ((letE i : LetA O n) • a)) +
        (W.γ T (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X • Gv) - Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X • Gv) := by
    have g2 : W.γ T (((W.φD T) ^ j) (((PD.p : ℕ) : O) ^ t • E0 W T K0 w c)) =
        ((W.φD T) ^ j) (((PD.p : ℕ) : O) ^ t • W.γ T (E0 W T K0 w c)) := by
      rw [← (W.γ T).map_smul]; exact γ_φpow W T W.gam j _
    rw [smul_sub, ← (W.γ T).map_smul, hred, ← hva, map_add, (W.γ T).map_smul, g2, smul_sub (((PD.p : ℕ) : O) ^ t),
      map_sub, smul_sub]
    abel
  rw [e2]
  exact inMultiple_add W T i j _ (InFP_osmul W T i j _ _ (keyF W hR.πΔ h2 T i hj M X ha'))
    (inMultiple_sub W T i j _ (InFP_γ W T i j (f_γ W hR M X) (inMultiple_of_mem W T i j _ hGv)) (inMultiple_of_mem W T i j _ hGv))

theorem S_diff (T : LocLat G Qp LL O) {j M X σ : ℕ} {w z z' : W.DD T} {c c' : ℕ → W.DD T}
    {s s' : ℕ → LetA O n}
    (hzd : z = ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) w -
      ∑ y ∈ Finset.range (max M X + 1), s y • ((W.φD T) ^ j) (c y))
    (hzd' : z' = ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) w -
      ∑ y ∈ Finset.range (max M X + 1), s' y • ((W.φD T) ^ j) (c' y)) :
    z - z' = ∑ y ∈ Finset.range (max M X + 1), s' y • ((W.φD T) ^ j) (c' y) -
      ∑ y ∈ Finset.range (max M X + 1), s y • ((W.φD T) ^ j) (c y) := by
  rw [hzd, hzd']; abel

theorem uniq_alt_alt [NeZero n] [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (hsp : Formalism.MainNotions.ArcLiftingSetup.SATPcore W)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (h2 : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * r))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) {j M X σ : ℕ} (hj : 1 ≤ j)
    {w z z' : W.DD T} (hz : Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T i j M X σ w z)
    (hz' : Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T i j M X σ w z') :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T i j (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X) (z - z') := by
  obtain ⟨c, r, s, hc, hrs, hzd⟩ := hz
  obtain ⟨c', r', s', hc', hrs', hzd'⟩ := hz'
  set K0 := max M X + 1
  obtain ⟨t, a, ha, haΔ, hae⟩ := ser_unique W hinj hO2 h9 hH hA T hT i w c c' hc hc' K0
  obtain ⟨Gv, hGv, hred⟩ := red W hR T i hc hrs hzd t
  obtain ⟨Gv', hGv', hred'⟩ := red W hR T i hc' hrs' hzd' t
  rw [truncatedSeries_pow_shift] at hred hred'
  have hl : ∀ y, (letE i : LetA O n) • (c y - c' y) = c y - c' y := fun y =>
    L_sub W (hc.2.1 y).1.1 (hc'.2.1 y).1.1
  obtain ⟨ha', hva⟩ := let_fix W T i K0 ha haΔ
    (L_osmul W _ (L_sum W _ _ fun y _ => L_osmul W _ (L_smul W _ (hl y)))) hae.symm.symm
  have hD : z - z' ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T i j := by
    rw [S_diff W T hzd hzd']
    exact (Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).sub_mem (S_mem W hR T i hc' hrs') (S_mem W hR T i hc hrs)
  refine sat W hsp hA T hT i j M X hD (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K0 + t) ?_
  have hE : ((PD.p : ℕ) : O) ^ t • E0 W T K0 w c =
      ((PD.p : ℕ) : O) ^ t • E0 W T K0 w c' - W.π₀ ^ K0 • ((letE i : LetA O n) • a) := by
    rw [← hva, eq_sub_iff_add_eq, ← smul_add]
    congr 1
    have hs := truncatedSeries_sub W T K0 w c c'
    rw [sub_eq_iff_eq_add] at hs
    rw [hs]
    abel
  have e : ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K0 + t) • (z - z') =
      -(((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) (W.π₀ ^ K0 • ((letE i : LetA O n) • a))) +
        Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X • (Gv - Gv') := by
    rw [smul_sub, hred, hred', hE, map_sub, smul_sub, smul_sub]
    abel
  rw [e]
  exact inMultiple_add W T i j _ (inMultiple_neg W T i j _ (InFP_osmul W T i j _ _ (keyF W hR.πΔ h2 T i hj M X ha')))
    (inMultiple_of_mem W T i j _ ((Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).sub_mem hGv hGv'))

theorem term_lin (T : LocLat G Qp LL O) (a a' : O) (y : ℕ) (x x' : W.DD T) :
    W.γ T (W.π₀ ^ y • (a • x + a' • x')) - W.π₀ ^ y • (a • x + a' • x') =
      a • (W.γ T (W.π₀ ^ y • x) - W.π₀ ^ y • x) + a' • (W.γ T (W.π₀ ^ y • x') - W.π₀ ^ y • x') := by
  rw [smul_add, smul_comm (W.π₀ ^ y) a x, smul_comm (W.π₀ ^ y) a' x', map_add, (W.γ T).map_smul,
    (W.γ T).map_smul]
  simp only [smul_sub]
  abel

theorem ser_lin (T : LocLat G Qp LL O) (i : ZMod n) (a a' : O) {w w' : W.DD T} {c c' : ℕ → W.DD T}
    (hc : Formalism.MainNotions.CrystallineLiftingInputs.IsSer W T i w c) (hc' : Formalism.MainNotions.CrystallineLiftingInputs.IsSer W T i w' c') :
    Formalism.MainNotions.CrystallineLiftingInputs.IsSer W T i (a • w + a' • w') (fun y => a • c y + a' • c' y) := by
  refine ⟨by simp [hc.1, hc'.1], fun y => ?_, fun K => ?_⟩
  · exact DL_of W T i (InNΔi_add W T i (InNΔi_osmul W T i a (InNΔi_c W T i hc y))
      (InNΔi_osmul W T i a' (InNΔi_c W T i hc' y)))
  · obtain ⟨j1, x1, hx1, hx1Δ, e1⟩ := hc.2.2 K
    obtain ⟨j2, x2, hx2, hx2Δ, e2⟩ := hc'.2.2 K
    refine ⟨j1 + j2, a • ((PD.p : ℕ) : O) ^ j2 • x1 + a' • ((PD.p : ℕ) : O) ^ j1 • x2,
      (W.N T).add_mem ((W.N T).smul_of_tower_mem _ ((W.N T).smul_of_tower_mem _ hx1))
        ((W.N T).smul_of_tower_mem _ ((W.N T).smul_of_tower_mem _ hx2)),
      fun δ hδ => by simp only [map_add, map_smul, hx1Δ δ hδ, hx2Δ δ hδ], ?_⟩
    have hs : ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) •
        (W.γ T (W.π₀ ^ y • (a • c y + a' • c' y)) - W.π₀ ^ y • (a • c y + a' • c' y)) =
        a • ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) •
          (W.γ T (W.π₀ ^ y • c y) - W.π₀ ^ y • c y) +
        a' • ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) •
          (W.γ T (W.π₀ ^ y • c' y) - W.π₀ ^ y • c' y) := by
      rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [term_lin, smul_add, smul_comm _ a, smul_comm _ a']
    rw [hs, map_add, (W.γ T).map_smul, (W.γ T).map_smul]
    have e3 : ((PD.p : ℕ) : O) ^ (j1 + j2) •
        (((PD.p : ℕ) : O) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K • (a • W.γ T w + a' • W.γ T w' - (a • w + a' • w')) -
          (a • ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) •
            (W.γ T (W.π₀ ^ y • c y) - W.π₀ ^ y • c y) +
          a' • ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) •
            (W.γ T (W.π₀ ^ y • c' y) - W.π₀ ^ y • c' y))) =
        a • ((PD.p : ℕ) : O) ^ j2 • (((PD.p : ℕ) : O) ^ j1 • (((PD.p : ℕ) : O) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K •
          (W.γ T w - w) - ∑ y ∈ Finset.range K,
            ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) •
              (W.γ T (W.π₀ ^ y • c y) - W.π₀ ^ y • c y))) +
        a' • ((PD.p : ℕ) : O) ^ j1 • (((PD.p : ℕ) : O) ^ j2 • (((PD.p : ℕ) : O) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K •
          (W.γ T w' - w') - ∑ y ∈ Finset.range K,
            ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) •
              (W.γ T (W.π₀ ^ y • c' y) - W.π₀ ^ y • c' y))) := by
      simp only [smul_sub, smul_add, smul_smul]
      ring_nf
      abel_nf
    rw [e3, e1, e2, smul_add, smul_comm (W.π₀ ^ K) a, smul_comm (W.π₀ ^ K) a',
      smul_comm (W.π₀ ^ K) (((PD.p : ℕ) : O) ^ j2), smul_comm (W.π₀ ^ K) (((PD.p : ℕ) : O) ^ j1)]

theorem truncatedSeries_linear (T : LocLat G Qp LL O) (K : ℕ) (a a' : O) (w w' : W.DD T) (c c' : ℕ → W.DD T) :
    E0 W T K (a • w + a' • w') (fun y => a • c y + a' • c' y) = a • E0 W T K w c + a' • E0 W T K w' c' := by
  simp only [E0, smul_sub, smul_add, Finset.smul_sum]
  rw [smul_comm _ a w, smul_comm _ a' w']
  have : ∀ y ∈ Finset.range K,
      ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) • W.π₀ ^ y • a • c y +
      ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) • W.π₀ ^ y • a' • c' y =
      a • ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) • W.π₀ ^ y • c y +
      a' • ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) • W.π₀ ^ y • c' y := by
    intro y _
    rw [smul_comm (W.π₀ ^ y) a, smul_comm (W.π₀ ^ y) a', smul_comm _ a, smul_comm _ a']
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  abel

theorem linear_of_frobenius_power [NeZero n] [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (hsp : Formalism.MainNotions.ArcLiftingSetup.SATPcore W)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (h2 : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * r))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) {j M X σ : ℕ} (hj : 1 ≤ j) (a a' : O)
    {w w' z z' z'' : W.DD T} (hz : Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T i j M X σ w z)
    (hz' : Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T i j M X σ w' z')
    (hz'' : Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T i j M X σ (a • w + a' • w') z'') :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T i j (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X) (z'' - (a • z + a' • z')) := by
  obtain ⟨c, r, s, hc, hrs, hzd⟩ := hz
  obtain ⟨c', r', s', hc', hrs', hzd'⟩ := hz'
  obtain ⟨c'', r'', s'', hc'', hrs'', hzd''⟩ := hz''
  set K0 := max M X + 1
  have hc3 := ser_lin W T i a a' hc hc'
  obtain ⟨t, b, hb, hbΔ, hbe⟩ := ser_unique W hinj hO2 h9 hH hA T hT i _ c'' _ hc'' hc3 K0
  obtain ⟨Gv, hGv, hred⟩ := red W hR T i hc hrs hzd t
  obtain ⟨Gv', hGv', hred'⟩ := red W hR T i hc' hrs' hzd' t
  obtain ⟨Gv'', hGv'', hred''⟩ := red W hR T i hc'' hrs'' hzd'' t
  rw [truncatedSeries_pow_shift] at hred hred' hred''
  have hl : ∀ y, (letE i : LetA O n) • (c'' y - (a • c y + a' • c' y)) = c'' y - (a • c y + a' • c' y) :=
    fun y => L_sub W (hc''.2.1 y).1.1 (L_add W (L_osmul W _ (hc.2.1 y).1.1) (L_osmul W _ (hc'.2.1 y).1.1))
  obtain ⟨hb', hvb⟩ := let_fix W T i K0 hb hbΔ
    (L_osmul W _ (L_sum W _ _ fun y _ => L_osmul W _ (L_smul W _ (hl y)))) hbe
  have hD : z'' - (a • z + a' • z') ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T i j := by
    have e : z'' - (a • z + a' • z') =
        a • ∑ y ∈ Finset.range K0, s y • ((W.φD T) ^ j) (c y) +
          a' • ∑ y ∈ Finset.range K0, s' y • ((W.φD T) ^ j) (c' y) -
          ∑ y ∈ Finset.range K0, s'' y • ((W.φD T) ^ j) (c'' y) := by
      rw [hzd'', hzd, hzd', map_add, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
        smul_add, smul_sub, smul_sub, smul_comm _ a, smul_comm _ a']
      abel
    rw [e]
    exact (Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).sub_mem ((Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).add_mem
      (Pp_osmul W T i j a _ (S_mem W hR T i hc hrs)) (Pp_osmul W T i j a' _ (S_mem W hR T i hc' hrs')))
      (S_mem W hR T i hc'' hrs'')
  refine sat W hsp hA T hT i j M X hD (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K0 + t) ?_
  have hE : ((PD.p : ℕ) : O) ^ t • E0 W T K0 (a • w + a' • w') c'' =
      a • (((PD.p : ℕ) : O) ^ t • E0 W T K0 w c) + a' • (((PD.p : ℕ) : O) ^ t • E0 W T K0 w' c') -
        W.π₀ ^ K0 • ((letE i : LetA O n) • b) := by
    have hs := truncatedSeries_sub W T K0 (a • w + a' • w') c'' (fun y => a • c y + a' • c' y)
    rw [truncatedSeries_linear, sub_eq_iff_eq_add] at hs
    rw [hs, ← hvb, smul_add, smul_add, smul_neg, smul_comm _ a, smul_comm _ a']
    abel
  have e : ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K0 + t) • (z'' - (a • z + a' • z')) =
      -(((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) (W.π₀ ^ K0 • ((letE i : LetA O n) • b))) +
        Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X • (Gv'' - (a • Gv + a' • Gv')) := by
    have hsm : ∀ (o : O) (Y : W.DD T), o • (((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) Y) =
        ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) (o • Y) := fun o Y => by
      rw [LinearMap.map_smul_of_tower, smul_comm]
    rw [smul_sub, smul_add, smul_comm _ a z, smul_comm _ a' z', hred, hred', hred'', hE, smul_add a,
      smul_add a', hsm a, hsm a', smul_comm a (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X) Gv,
      smul_comm a' (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X) Gv', map_sub, map_add, smul_sub, smul_add, smul_sub, smul_add]
    abel
  rw [e]
  exact inMultiple_add W T i j _ (inMultiple_neg W T i j _ (InFP_osmul W T i j _ _ (keyF W hR.πΔ h2 T i hj M X hb')))
    (inMultiple_of_mem W T i j _ ((Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).sub_mem hGv'' ((Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).add_mem
      (Pp_osmul W T i j a _ hGv) (Pp_osmul W T i j a' _ hGv'))))

theorem ser_map {T T' : LocLat G Qp LL O} (F : LatHom T.L T'.L) (hT : IsCrys PD T.ρ)
    (hT' : IsCrys PD T'.ρ) (i : ZMod n) {w : W.DD T} {c : ℕ → W.DD T}
    (hc : Formalism.MainNotions.CrystallineLiftingInputs.IsSer W T i w c) :
    Formalism.MainNotions.CrystallineLiftingInputs.IsSer W T' i (W.map F w) (fun y => W.map F (c y)) := by
  have hγm : ∀ x, W.map F (W.γ T x) = W.γ T' (W.map F x) := fun x => W.map_γ F W.gam x
  refine ⟨by simp [hc.1], fun y => DL_of W T' i (InNΔi_map W F hT hT' i (InNΔi_c W T i hc y)),
    fun K => ?_⟩
  obtain ⟨j, x, hx, hxΔ, e⟩ := hc.2.2 K
  refine ⟨j, W.map F x, W.map_N F hT hT' x hx, fun δ hδ => by rw [← W.map_γ, hxΔ δ hδ], ?_⟩
  have := congrArg (W.map F) e
  simp only [map_sub, map_sum, LinearMap.map_smul_of_tower, hγm] at this
  exact this

theorem hermFlagUnipotent_anisotropic_vector_sub_mem [NeZero n] [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (hsp : Formalism.MainNotions.ArcLiftingSetup.SATPcore W)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (h2 : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * r))
    {T T' : LocLat G Qp LL O} (F : LatHom T.L T'.L) (hT : IsCrys PD T.ρ) (hT' : IsCrys PD T'.ρ)
    (i : ZMod n) {j M X σ : ℕ} (hj : 1 ≤ j) {z' : W.DD T'} {w₁ z₁ : W.DD T}
    (hz : Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T i j M X σ w₁ z₁)
    (hz' : Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T' i j M X σ (W.map F w₁) z') :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T' i j (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X) (W.map F z₁ - z') := by
  obtain ⟨c, r, s, hc, hrs, hzd⟩ := hz
  have hzF : Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T' i j M X σ (W.map F w₁) (W.map F z₁) := by
    refine ⟨fun y => W.map F (c y), r, s, ser_map W F hT hT' i hc, hrs, ?_⟩
    rw [hzd, map_sub, map_sum, LinearMap.map_smul_of_tower, map_φpow]
    simp only [mapA_smul, map_φpow]
  exact uniq_alt_alt W hinj hO2 h9 hH hR hsp hA h2 T' hT' i hj hzF hz'

def c0 (T : LocLat G Qp LL O) (y1 : W.DD T) : ℕ → W.DD T :=
  fun y => if y = 1 then ((PD.p : ℕ) : O) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p 1 • y1 else 0

theorem isSeries_first_coefficient (hπ : W.π₀ ∈ W.AΔ) (T : LocLat G Qp LL O) (i : ZMod n) {w y1 : W.DD T}
    (hw : Formalism.MainNotions.CrystallineLiftingInputs.InI W T i w) (hy1 : Formalism.MainNotions.LiftingTheory.InNΔi W T i y1) (hwy : w = W.π₀ • y1) :
    Formalism.MainNotions.CrystallineLiftingInputs.IsSer W T i w (c0 W T y1) := by
  refine ⟨by simp [c0], fun y => ?_, fun K => ?_⟩
  · by_cases h : y = 1
    · simp only [c0, h, if_true]; exact DL_of W T i (InNΔi_osmul W T i _ hy1)
    · simp only [c0, h, if_false]; exact DL_of W T i (InNΔi_zero W T i)
  · obtain ⟨z', hz', hzw⟩ := z_of_InI W T i hw
    rcases lt_or_ge K 2 with hK | hK
    · have hs : ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) •
          (W.γ T (W.π₀ ^ y • c0 W T y1 y) - W.π₀ ^ y • c0 W T y1 y) = 0 := by
        refine Finset.sum_eq_zero fun y hy => ?_
        have : y ≠ 1 := by have := Finset.mem_range.1 hy; omega
        simp [c0, this]
      have hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i (W.π₀ ^ (1 - K) • ((PD.p : ℕ) : O) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K • z') :=
        InNΔi_smul W T i (W.AΔ.pow_mem hπ _) (InNΔi_osmul W T i _ hz')
      refine ⟨0, _, hx.1.1, hx.1.2, ?_⟩
      rw [hs, sub_zero, pow_zero, one_smul, hzw, smul_smul, ← pow_add, show K + (1 - K) = 1 by omega,
        pow_one]
      exact smul_comm _ _ _
    · have h1 : 1 ∈ Finset.range K := Finset.mem_range.2 (by omega)
      have hs : ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) •
          (W.γ T (W.π₀ ^ y • c0 W T y1 y) - W.π₀ ^ y • c0 W T y1 y) =
          ((PD.p : ℕ) : O) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K • (W.γ T w - w) := by
        rw [Finset.sum_eq_single 1 (fun y _ hy => by simp [c0, hy]) (fun h => absurd h1 h)]
        simp only [c0, if_true, pow_one]
        rw [smul_comm W.π₀, (W.γ T).map_smul, ← smul_sub, smul_smul, ← pow_add,
          Nat.sub_add_cancel (eY_mono (PD := PD) (by omega : 1 ≤ K)), hwy]
      refine ⟨0, 0, (W.N T).zero_mem, fun δ _ => map_zero _, ?_⟩
      rw [hs, sub_self, smul_zero, smul_zero]

theorem uniformizer_dvd_of_frobenius_power [NeZero n] [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (hsp : Formalism.MainNotions.ArcLiftingSetup.SATPcore W)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (h2 : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * r))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) {j M X σ : ℕ} (hj : 1 ≤ j) (hM : 1 ≤ M)
    {w z : W.DD T} (hw : Formalism.MainNotions.CrystallineLiftingInputs.InI W T i w) (hw1 : Formalism.MainNotions.CrystallineLiftingInputs.InPN W T 1 w)
    (hz : Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T i j M X σ w z) :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T i j (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X) z := by
  have hz0 := hz
  obtain ⟨c, r, s, hc, hrs, hzd⟩ := hz0
  obtain ⟨y0, hy0, hy0Δ, hwy0⟩ := hw1
  obtain ⟨y1, hy1, hwy1⟩ : ∃ y1, Formalism.MainNotions.LiftingTheory.InNΔi W T i y1 ∧ w = W.π₀ • y1 := by
    obtain ⟨h1, h2⟩ := let_fix W T i 1 hy0 hy0Δ hw.1.1 hwy0
    exact ⟨_, h1, by rw [h2, pow_one]⟩
  have hc0 := isSeries_first_coefficient W hR.πΔ T i hw hy1 hwy1
  set z0 := ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) w -
    ∑ y ∈ Finset.range (max M X + 1), s y • ((W.φD T) ^ j) (c0 W T y1 y)
  have hzt0 : Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T i j M X σ w z0 := ⟨c0 W T y1, r, s, hc0, hrs, rfl⟩
  have hdiff := uniq_alt_alt W hinj hO2 h9 hH hR hsp hA h2 T hT i hj hz hzt0
  obtain ⟨g, hgA, hg⟩ := g_mem W hR (hrs 1).1
  have h1 : 1 ∈ Finset.range (max M X + 1) := Finset.mem_range.2 (by omega)
  have hsum : ∑ y ∈ Finset.range (max M X + 1), s y • ((W.φD T) ^ j) (c0 W T y1 y) =
      s 1 • ((W.φD T) ^ j) (((PD.p : ℕ) : O) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p 1 • y1) := by
    rw [Finset.sum_eq_single 1 (fun y _ hy => by simp [c0, hy]) (fun h => absurd h1 h)]
    simp [c0]
  have hz0f : z0 = Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X •
      ((Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ * g) • ((W.φD T) ^ j) y1) := by
    show ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) w - _ = _
    rw [hsum, hwy1, φpow_smul, ((W.φD T) ^ j).map_smul (((PD.p : ℕ) : O) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p 1) y1,
      lsmul_eq, lsmul_eq, smul_smul, smul_smul, ← sub_smul, smul_smul]
    congr 1
    have hs := (hrs 1).2
    rw [pow_one] at hg
    show Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ * (W.φA ^ j) W.π₀ - s 1 * Formalism.MainNotions.ArcLiftingSetup.lA W ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p 1 = _
    simp only [Formalism.MainNotions.ArcLiftingSetup.lA]
    linear_combination -hs + ((PD.p : ℕ) : LetA O n) ^ σ * hg
  have hz0F : Formalism.MainNotions.ArcLiftingSetup.InFP W T i j (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X) z0 := by
    rw [hz0f]
    exact inMultiple_of_mem W T i j _ (Pp_gen W T i j (W.AΔ.mul_mem (W.AΔ.pow_mem (lA_mem W) _) hgA) hy1)
  have e : z = (z - z0) + z0 := by abel
  rw [e]
  exact inMultiple_add W T i j _ hdiff hz0F

end Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Classical

noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.UnusedSlot80.Relay2 PowerSeries

section Div

variable {O : Type} [CommRing O] [IsLocalRing O]

def Gd (l M X : ℕ) : PowerSeries O := PowerSeries.X ^ M * (PowerSeries.X + ((l : ℕ) : PowerSeries O)) ^ X

theorem Gd_res {l : ℕ} (hlm : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (M X : ℕ) :
    PowerSeries.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) (Gd l M X) = PowerSeries.X ^ (M + X) := by
  have h0 : ((l : ℕ) : PowerSeries (O ⧸ IsLocalRing.maximalIdeal O)) = 0 := by
    rw [← map_natCast (PowerSeries.C (R := O ⧸ IsLocalRing.maximalIdeal O)),
      ← map_natCast (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)), Ideal.Quotient.eq_zero_iff_mem.2 hlm,
      map_zero]
  simp only [Gd, map_mul, map_pow, map_add, PowerSeries.map_X, map_natCast, h0, add_zero, pow_add]

theorem Gd_ne {l : ℕ} (hlm : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (M X : ℕ) :
    PowerSeries.map (IsLocalRing.residue O) (Gd l M X) ≠ 0 := by
  show PowerSeries.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) (Gd l M X) ≠ 0
  rw [Gd_res hlm]
  exact pow_ne_zero _ PowerSeries.X_ne_zero

theorem Gd_ord {l : ℕ} (hlm : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (M X : ℕ) :
    (PowerSeries.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)) (Gd l M X)).order.toNat = M + X := by
  rw [Gd_res hlm, PowerSeries.order_X_pow]
  rfl

variable [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem wdiv {l : ℕ} (hlm : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (M X : ℕ) (F : PowerSeries O) :
    ∃ (Q : PowerSeries O) (R : Polynomial O), F = Gd l M X * Q + (R : PowerSeries O) ∧
      R.degree < ((M + X : ℕ) : WithBot ℕ) := by
  have h := PowerSeries.isWeierstrassDivision_weierstrassDiv_weierstrassMod F (Gd_ne hlm M X)
  refine ⟨_, _, h.eq_mul_add, ?_⟩
  have := h.degree_lt
  rwa [Gd_ord hlm] at this

theorem wuniq {l : ℕ} (hlm : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (M X : ℕ) (P : Polynomial O)
    (hP : P.degree < ((M + X : ℕ) : WithBot ℕ)) (H : PowerSeries O)
    (h : (P : PowerSeries O) = Gd l M X * H) : P = 0 := by
  have d1 : (P : PowerSeries O).IsWeierstrassDivision (Gd l M X) 0 P :=
    ⟨by rw [Gd_ord hlm]; exact hP, by simp⟩
  have d2 : (P : PowerSeries O).IsWeierstrassDivision (Gd l M X) H 0 :=
    ⟨by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _, by rw [h]; simp⟩
  exact (PowerSeries.IsWeierstrassDivision.elim (Gd_ne hlm M X) d1 d2).2

end Div

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem φA_unif (k : ℕ) (i : ZMod n) : ((W.φA ^ k) W.π₀) i = ((W.φA ^ k) W.π₀) 0 := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', AlgHom.mul_apply]
    show W.φ₀ (((W.φA ^ k) W.π₀) (i - 1)) = W.φ₀ (((W.φA ^ k) W.π₀) (0 - 1))
    rw [ih (i - 1), ih (0 - 1)]

theorem rem_exists [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (h9r : Formalism.MainNotions.LiftingTheory.P9π₀ W) {j M X σ y : ℕ}
    (hMX : 1 ≤ M + X)
    (hmem : ∃ α ∈ W.AΔ, ∃ β ∈ W.AΔ, ((PD.p : ℕ) : LetA O n) ^ σ * ((W.φA ^ j) W.π₀) ^ y =
      ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y * α + Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X * β) :
    ∃ r s : LetA O n, Formalism.MainNotions.CrystallineLiftingInputs.IsRem W j M X y r ∧
      ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y * s = ((PD.p : ℕ) : LetA O n) ^ σ * r := by
  have hs : PowerSeries.HasSubst W.π₀₁ := PowerSeries.HasSubst.of_constantCoeff_zero' (Formalism.MainNotions.LiftingTheory.uniformizer_constantCoeff_zero W h9r 0)
  set ι : PowerSeries O →ₐ[O] PowerSeries O := PowerSeries.substAlgHom (R := O) hs
  have hι : ∀ F, PowerSeries.subst (W.π₀ 0) F = ι F := fun F => by
    rw [PowerSeries.coe_substAlgHom]; rfl
  have hιi : ∀ i F, PowerSeries.subst (W.π₀ i) F = ι F := fun i F => hι F
  have hιX : ι PowerSeries.X = W.π₀₁ := by
    rw [← hι]; exact PowerSeries.subst_X hs
  have hπΔ : W.π₀ ∈ W.AΔ := h9r.1
  set a : LetA O n := ((W.φA ^ j) W.π₀) ^ y
  have haΔ : a ∈ W.AΔ := W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.φA_pow_mem_AΔ W hπΔ j) _
  obtain ⟨Fs, hFs, -⟩ := h9r.2.1 a haΔ
  set F := Fs 0
  have haF : ∀ i, a i = ι F := by
    intro i
    have e1 : a i = a 0 := by
      show (((W.φA ^ j) W.π₀) ^ y) i = (((W.φA ^ j) W.π₀) ^ y) 0
      rw [Pi.pow_apply, Pi.pow_apply, φA_unif W j i]
    rw [e1, hFs 0, hι]
  obtain ⟨α, hαA, β, hβA, hαβ⟩ := hmem
  obtain ⟨Fα, hFα, -⟩ := h9r.2.1 α hαA
  obtain ⟨Fβ, hFβ, -⟩ := h9r.2.1 β hβA
  have hFα' : ∀ i, α i = ι (Fα i) := fun i => by rw [hFα, hιi]
  have hFβ' : ∀ i, β i = ι (Fβ i) := fun i => by rw [hFβ, hιi]
  have hι' : ∀ F, ι F = PowerSeries.subst W.π₀₁ F := fun F => by rw [PowerSeries.coe_substAlgHom]
  have hG : ∀ i, (Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X) i = ι (Gd PD.p M X) := by
    intro i
    simp only [Formalism.MainNotions.CrystallineLiftingInputs.fMX, Formalism.MainNotions.LiftingTheory.qp, Gd, Pi.mul_apply, Pi.pow_apply, Pi.add_apply,
      Pi.natCast_apply, map_mul, map_pow, map_add, map_natCast, hιX]
    rfl

  have he : ((PD.p : ℕ) : LetA O n) ^ σ * a ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.pow_mem (W.AΔ.natCast_mem _) _) haΔ
  obtain ⟨f0, -, huniq⟩ := h9r.2.1 _ he
  have h1 : ∀ i, (((PD.p : ℕ) : LetA O n) ^ σ * a) i =
      PowerSeries.subst (W.π₀ i) (((PD.p : ℕ) : PowerSeries O) ^ σ * F) := by
    intro i
    rw [hιi, map_mul, map_pow, map_natCast, ← haF i]
    rfl
  have h2 : ∀ i, (((PD.p : ℕ) : LetA O n) ^ σ * a) i = PowerSeries.subst (W.π₀ i)
      (((PD.p : ℕ) : PowerSeries O) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y * Fα i + Gd PD.p M X * Fβ i) := by
    intro i
    rw [hιi, map_add, map_mul, map_mul, map_pow, map_natCast, ← hFα' i, ← hFβ' i, ← hG i, hαβ]
    rfl
  have heq : ∀ i, ((PD.p : ℕ) : PowerSeries O) ^ σ * F =
      ((PD.p : ℕ) : PowerSeries O) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y * Fα i + Gd PD.p M X * Fβ i := by
    intro i
    have e1 := huniq _ h1
    have e2 := huniq _ h2
    exact congrFun (e1.trans e2.symm) i

  obtain ⟨Q, R, hQR, hRd⟩ := wdiv hlm M X F
  choose Qα ρ hQρ hρd using fun i => wdiv hlm M X (Fα i)
  have hP : ∀ i, ((PD.p : ℕ) : O) ^ σ • R = ((PD.p : ℕ) : O) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y • ρ i := by
    intro i
    rw [← sub_eq_zero]
    refine wuniq hlm M X _ ?_ (((PD.p : ℕ) : PowerSeries O) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y * Qα i + Fβ i -
      ((PD.p : ℕ) : PowerSeries O) ^ σ * Q) ?_
    · exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _)
        (max_lt (lt_of_le_of_lt (Polynomial.degree_smul_le _ _) hRd)
          (lt_of_le_of_lt (Polynomial.degree_smul_le _ _) (hρd i)))
    · rw [Polynomial.coe_sub, Polynomial.coe_smul, Polynomial.coe_smul]
      have eR : (R : PowerSeries O) = F - Gd PD.p M X * Q := by rw [hQR]; ring
      have eρ : (ρ i : PowerSeries O) = Fα i - Gd PD.p M X * Qα i := by rw [hQρ i]; ring
      rw [eR, eρ]
      simp only [Algebra.smul_def, map_pow, map_natCast]
      linear_combination heq i

  have hnat : R.natDegree < M + X := by
    by_cases h0 : R = 0
    · rw [h0, Polynomial.natDegree_zero]; omega
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 hRd
  have hRι : ∀ i, (∑ k ∈ Finset.range (M + X), algebraMap O (LetA O n) (R.coeff k) * W.π₀ ^ k) i = ι R := by
    intro i
    rw [hι', PowerSeries.subst_coe hs, Polynomial.aeval_eq_sum_range' hnat, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.mul_apply, Pi.pow_apply, Pi.algebraMap_apply, Algebra.smul_def]
    rfl
  refine ⟨∑ k ∈ Finset.range (M + X), algebraMap O (LetA O n) (R.coeff k) * W.π₀ ^ k,
    fun i => ι (ρ i), ⟨⟨R.coeff, rfl⟩, fun _ => ι Q, ?_⟩, ?_⟩
  · funext i
    rw [Pi.sub_apply, Pi.mul_apply, hRι, hG i, ← map_mul]
    show a i - ι R = _
    rw [haF i, ← map_sub, hQR]
    congr 1
    ring
  · funext i
    rw [Pi.mul_apply, Pi.mul_apply, hRι, Pi.pow_apply, Pi.pow_apply, Pi.natCast_apply,
      ← map_natCast ι, ← map_pow, ← map_pow, ← map_mul, ← map_mul]
    congr 1
    have := congrArg (fun P : Polynomial O => (P : PowerSeries O)) (hP i)
    simp only [Polynomial.coe_smul, PowerSeries.smul_eq_C_mul, map_pow, map_natCast] at this
    exact this.symm

theorem num2 (l y X : ℕ) (hl : 11 ≤ l) (h : ⌈(X : ℝ) / ((l : ℝ) - 1) ^ 2 + 1⌉₊ < Formalism.MainNotions.CrystallineLiftingInputs.eY l y) :
    Formalism.MainNotions.CrystallineLiftingInputs.eY l y - ⌈(X : ℝ) / ((l : ℝ) - 1) ^ 2 + 1⌉₊ + (X - 1) / l ≤ (l - 1) * y := by
  have hA := (Formalism.MainNotions.CrystallineLiftingInputs.TToolAlg_holds.2 l y X 1 0 hl).2.2
  set σ := ⌈(X : ℝ) / ((l : ℝ) - 1) ^ 2 + 1⌉₊
  set e := Formalism.MainNotions.CrystallineLiftingInputs.eY l y
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hσ : (X : ℝ) / ((l : ℝ) - 1) ^ 2 + 1 ≤ σ := Nat.le_ceil _
  have he : (e : ℝ) < (y : ℝ) * l / ((l : ℝ) - 1) + 1 := by
    have h0 : 0 ≤ (y : ℝ) * l / ((l : ℝ) - 1) := div_nonneg (by positivity) (by linarith)
    exact Nat.ceil_lt_add_one h0
  have hq : (((X - 1) / l : ℕ) : ℝ) ≤ (X : ℝ) / l := by
    calc (((X - 1) / l : ℕ) : ℝ) ≤ ((X - 1 : ℕ) : ℝ) / l := Nat.cast_div_le
      _ ≤ (X : ℝ) / l := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact_mod_cast Nat.sub_le X 1
  have hcast : (((l - 1) * y : ℕ) : ℝ) = ((l : ℝ) - 1) * y := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
  rcases le_total (((l : ℝ) - 1) * y - (X : ℝ) / l) 0 with hm | hm
  · exfalso
    rw [max_eq_left hm] at hA
    have : e ≤ σ := Nat.ceil_le.2 (by linarith)
    omega
  · rw [max_eq_right hm] at hA
    have key : ((e + (X - 1) / l : ℕ) : ℝ) < ((σ + (l - 1) * y + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, hcast, Nat.cast_one]
      linarith
    have key' : e + (X - 1) / l < σ + (l - 1) * y + 1 := by exact_mod_cast key
    omega

theorem bound1 (hπ : W.π₀ ∈ W.AΔ)
    (h2 : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * r))
    (hl : 11 ≤ PD.p) {M X σ : ℕ} (y : ℕ) (hM : 1 ≤ M)
    (hσ : σ = ⌈((M : ℝ) + X) / ((PD.p : ℝ) - 1) + 1⌉₊) :
    ∃ α ∈ W.AΔ, ∃ β ∈ W.AΔ, ((PD.p : ℕ) : LetA O n) ^ σ * ((W.φA ^ 1) W.π₀) ^ y =
      ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y * α + Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X * β := by
  have : Fact PD.p.Prime := ⟨PD.hp⟩
  obtain ⟨u, hu, -, -, -, hφ⟩ := h2 1 1
  simp only [pow_one, Finset.range_one, Finset.prod_singleton, mul_one] at hφ
  have hp0 : Formalism.MainNotions.LiftingTheory.pk W 0 = Formalism.MainNotions.LiftingTheory.qp W := by simp [Formalism.MainNotions.LiftingTheory.pk]
  rw [hp0] at hφ
  have hmem := Formalism.MainNotions.CrystallineLiftingInputs.trunc_floor_one (↥W.AΔ) PD.p (by omega) ⟨W.π₀, hπ⟩ ⟨u, hu⟩ M X y hM
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hmem
  set fl := ⌊((M : ℝ) + X) / ((PD.p : ℝ) - 1) + 1⌋₊
  have hfl : fl ≤ σ := by rw [hσ]; exact Nat.floor_le_ceil _
  refine ⟨((PD.p : ℕ) : LetA O n) ^ (σ - fl) * (a : LetA O n),
    W.AΔ.mul_mem (W.AΔ.pow_mem (W.AΔ.natCast_mem _) _) a.2,
    ((PD.p : ℕ) : LetA O n) ^ (σ - fl) * (b : LetA O n),
    W.AΔ.mul_mem (W.AΔ.pow_mem (W.AΔ.natCast_mem _) _) b.2, ?_⟩
  have hab' := congrArg (fun x : ↥W.AΔ => (x : LetA O n)) hab
  push_cast at hab'
  have hL : ((PD.p : ℕ) : LetA O n) ^ σ = ((PD.p : ℕ) : LetA O n) ^ (σ - fl) * ((PD.p : ℕ) : LetA O n) ^ fl := by
    rw [← pow_add, Nat.sub_add_cancel hfl]
  rw [pow_one, hφ, hL]
  simp only [Formalism.MainNotions.CrystallineLiftingInputs.fMX, Formalism.MainNotions.LiftingTheory.qp]
  linear_combination (-(((PD.p : ℕ) : LetA O n) ^ (σ - fl))) * hab'

theorem bound2 (hπ : W.π₀ ∈ W.AΔ)
    (h1 : ∀ k : ℕ, ∃ a ∈ W.AΔ, ∃ b ∈ W.AΔ,
      Formalism.MainNotions.LiftingTheory.pk W k = ((PD.p : ℕ) : LetA O n) * a + W.π₀ ^ (PD.p ^ k) * b)
    (h2 : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * r))
    (hl : 11 ≤ PD.p) {X σ : ℕ} (y : ℕ) (hσ : σ = ⌈(X : ℝ) / ((PD.p : ℝ) - 1) ^ 2 + 1⌉₊) :
    ∃ α ∈ W.AΔ, ∃ β ∈ W.AΔ, ((PD.p : ℕ) : LetA O n) ^ σ * ((W.φA ^ 2) W.π₀) ^ y =
      ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y * α + Formalism.MainNotions.CrystallineLiftingInputs.fMX W 1 X * β := by
  have hφy : ((W.φA ^ 2) W.π₀) ^ y ∈ W.AΔ := W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.φA_pow_mem_AΔ W hπ 2) _
  have hL : ∀ k, ((PD.p : ℕ) : LetA O n) ^ k ∈ W.AΔ := fun k => W.AΔ.pow_mem (W.AΔ.natCast_mem _) _
  by_cases hle : Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y ≤ σ
  · refine ⟨((PD.p : ℕ) : LetA O n) ^ (σ - Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y) * ((W.φA ^ 2) W.π₀) ^ y,
      W.AΔ.mul_mem (hL _) hφy, 0, W.AΔ.zero_mem, ?_⟩
    rw [mul_zero, add_zero, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
  push Not at hle
  have hy : 1 ≤ y := by
    rcases Nat.eq_zero_or_pos y with rfl | h
    · exfalso; simp [Formalism.MainNotions.CrystallineLiftingInputs.eY] at hle
    · exact h
  obtain ⟨u, hu, -, -, -, hφ⟩ := h2 2 y
  obtain ⟨a, ha, b, hb, hp1⟩ := h1 1
  have hq : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := Formalism.MainNotions.LiftingTheory.lifta_qΔ W hπ

  set d0 : LetA O n := ∑ i ∈ Finset.range PD.p, W.π₀ ^ i * Formalism.MainNotions.LiftingTheory.qp W ^ (PD.p - 1 - i)
  have hd0 : d0 ∈ W.AΔ := W.AΔ.sum_mem fun i _ => W.AΔ.mul_mem (W.AΔ.pow_mem hπ _) (W.AΔ.pow_mem hq _)
  have hd : W.π₀ ^ PD.p = Formalism.MainNotions.LiftingTheory.qp W ^ PD.p - ((PD.p : ℕ) : LetA O n) * d0 := by
    have e := geom_sum₂_mul W.π₀ (Formalism.MainNotions.LiftingTheory.qp W) PD.p
    have : W.π₀ - Formalism.MainNotions.LiftingTheory.qp W = -((PD.p : ℕ) : LetA O n) := by simp [Formalism.MainNotions.LiftingTheory.qp]
    rw [this] at e
    linear_combination -e
  rw [pow_one] at hp1
  have hp1' : Formalism.MainNotions.LiftingTheory.pk W 1 = b * Formalism.MainNotions.LiftingTheory.qp W ^ PD.p + ((PD.p : ℕ) : LetA O n) * (a - d0 * b) := by
    rw [hp1, hd]; ring
  have hE : a - d0 * b ∈ W.AΔ := W.AΔ.sub_mem ha (W.AΔ.mul_mem hd0 hb)
  set c' := Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y - σ
  have hc : c' + (X - 1) / PD.p ≤ (PD.p - 1) * y := by
    have := num2 PD.p y X hl (by rw [← hσ]; exact hle)
    rw [← hσ] at this
    exact this
  have hmem := Formalism.MainNotions.CrystallineLiftingInputs.rem_2 (R := ↥W.AΔ) PD.p (by omega) ⟨W.π₀, hπ⟩ ⟨Formalism.MainNotions.LiftingTheory.qp W, hq⟩ ⟨b, hb⟩
    ⟨a - d0 * b, hE⟩ y X c' hy hc
  obtain ⟨a', b', hab⟩ := Ideal.mem_span_pair.1 hmem
  have hab' := congrArg (fun x : ↥W.AΔ => (x : LetA O n)) hab
  push_cast at hab'
  refine ⟨u * a', W.AΔ.mul_mem hu a'.2, ((PD.p : ℕ) : LetA O n) ^ σ * u * b',
    W.AΔ.mul_mem (W.AΔ.mul_mem (hL σ) hu) b'.2, ?_⟩
  have hprod : ∏ k ∈ Finset.range 2, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * y) =
      Formalism.MainNotions.LiftingTheory.pk W 0 ^ ((PD.p - 1) * y) * Formalism.MainNotions.LiftingTheory.pk W 1 ^ ((PD.p - 1) * y) := by
    rw [Finset.prod_range_succ, Finset.prod_range_one]
  have hp0 : Formalism.MainNotions.LiftingTheory.pk W 0 = Formalism.MainNotions.LiftingTheory.qp W := by simp [Formalism.MainNotions.LiftingTheory.pk]
  have hpow : W.π₀ ^ y * (Formalism.MainNotions.LiftingTheory.pk W 0 ^ ((PD.p - 1) * y) * Formalism.MainNotions.LiftingTheory.pk W 1 ^ ((PD.p - 1) * y)) =
      (W.π₀ * Formalism.MainNotions.LiftingTheory.qp W ^ (PD.p - 1) *
        (b * Formalism.MainNotions.LiftingTheory.qp W ^ PD.p + ((PD.p : ℕ) : LetA O n) * (a - d0 * b)) ^ (PD.p - 1)) ^ y := by
    rw [hp0, hp1', mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_assoc]
  have hexp : ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y =
      ((PD.p : ℕ) : LetA O n) ^ σ * ((PD.p : ℕ) : LetA O n) ^ c' := by
    rw [← pow_add]; congr 1; omega
  rw [hφ, hprod, mul_assoc u, hpow, ← hab', hexp, Formalism.MainNotions.CrystallineLiftingInputs.fMX, pow_one]
  ring

end Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Classical

noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.UnusedSlot80.Relay2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem rs_ex [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (h9r : Formalism.MainNotions.LiftingTheory.P9π₀ W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 11 ≤ PD.p)
    {j M X σ : ℕ} (hc : Formalism.MainNotions.CrystallineLiftingInputs.TCase PD.p j M X σ) :
    ∃ r s : ℕ → LetA O n, ∀ y, Formalism.MainNotions.CrystallineLiftingInputs.IsRem W j M X y (r y) ∧
      ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y * s y = ((PD.p : ℕ) : LetA O n) ^ σ * r y := by
  have hπ : W.π₀ ∈ W.AΔ := h9r.1
  have hrs : ∀ y, ∃ r s : LetA O n, Formalism.MainNotions.CrystallineLiftingInputs.IsRem W j M X y r ∧
      ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y * s = ((PD.p : ℕ) : LetA O n) ^ σ * r := by
    intro y
    rcases hc with ⟨rfl, hM, hσ⟩ | ⟨rfl, rfl, hσ⟩
    · exact rem_exists W hlm h9r (by omega) (bound1 W hπ (hTr hA).2.1 hl y hM hσ)
    · exact rem_exists W hlm h9r (by omega) (bound2 W hπ (hTr hA).1 (hTr hA).2.1 hl y hσ)
  choose r s hrs using hrs
  exact ⟨r, s, hrs⟩

theorem trunc_ex [NeZero n] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 11 ≤ PD.p)
    {j M X σ : ℕ} (hc : Formalism.MainNotions.CrystallineLiftingInputs.TCase PD.p j M X σ) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (i : ZMod n) (w : W.DD T) (hw : Formalism.MainNotions.CrystallineLiftingInputs.InI W T i w) :
    ∃ z, Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T i j M X σ w z := by
  obtain ⟨c, hcs⟩ := ser_exists W hinj hO2 h9 hH hA T hT i w hw
  obtain ⟨r, s, hrs⟩ := rs_ex W hTr hlm (Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hA T hT).1 hA hl hc
  exact ⟨_, c, r, s, hcs, hrs, rfl⟩

end Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Classical

noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.UnusedSlot80.Relay2

def HM {LL : Type} [Field LL] {d : ℕ} (sol : Fin d → ℕ → Fin d → LL) :
    Matrix (Fin d) (Fin d) (PowerSeries LL) :=
  Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m'

theorem HM_apply {LL : Type} [Field LL] {d : ℕ} (sol : Fin d → ℕ → Fin d → LL) (m' k' : Fin d) :
    HM sol m' k' = PowerSeries.mk fun r' => sol k' r' m' := rfl

theorem HM_inv {LL : Type} [Field LL] {d : ℕ} (sol : Fin d → ℕ → Fin d → LL)
    (h0 : ∀ k, sol k 0 = Pi.single k 1) : HM sol * (HM sol)⁻¹ = 1 := by
  apply Matrix.mul_nonsing_inv
  rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
  have : (PowerSeries.constantCoeff (R := LL)).mapMatrix (HM sol) = 1 := by
    ext m' k'
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, HM, Matrix.of_apply, PowerSeries.coeff_zero_eq_constantCoeff.symm,
      PowerSeries.coeff_mk, h0, Matrix.one_apply, Pi.single_apply]
  rw [this, Matrix.det_one]
  exact isUnit_one

theorem HM_coeff {LL : Type} [Field LL] {d : ℕ} (sol : Fin d → ℕ → Fin d → LL)
    (h : HM sol * (HM sol)⁻¹ = 1) (N : ℕ) (m' m : Fin d) :
    ∑ k, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal N, sol k p.1 m' * PowerSeries.coeff p.2 ((HM sol)⁻¹ k m) =
      if N = 0 ∧ m' = m then 1 else 0 := by
  have e := congrArg (fun M : Matrix (Fin d) (Fin d) (PowerSeries LL) => PowerSeries.coeff N (M m' m)) h
  simp only [Matrix.mul_apply, map_sum, PowerSeries.coeff_mul, HM_apply, PowerSeries.coeff_mk,
    Matrix.one_apply] at e
  rw [e]
  by_cases h1 : m' = m
  · by_cases h2 : N = 0 <;> simp [h1, h2, PowerSeries.coeff_one]
  · simp [h1]

theorem poly_cong {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] {A : Type} [CommRing A] [Algebra O A]
    (hinj : Function.Injective (algebraMap O LL)) (l : ℕ) {d : ℕ} (K0 E : ℕ) (sol : Fin d → ℕ → Fin d → LL)
    (hHH : HM sol * (HM sol)⁻¹ = 1) (a bb : ℕ → Fin d → Fin d → O)
    (ha : ∀ y < K0, ∀ k m, algebraMap O LL (a y k m) = (l : LL) ^ E * PowerSeries.coeff y ((HM sol)⁻¹ k m))
    (hb : ∀ y < K0, ∀ k m', algebraMap O LL (bb y k m') = (l : LL) ^ E * sol k y m') (Φ : A) (m m' : Fin d) :
    ∃ R0 : Polynomial O, ∑ k, (∑ y ∈ Finset.range K0, algebraMap O A (bb y k m') * Φ ^ y) *
        (∑ y ∈ Finset.range K0, algebraMap O A (a y k m) * Φ ^ y) =
      algebraMap O A (if m' = m then (l : O) ^ (2 * E) else 0) + Φ ^ K0 * Polynomial.aeval Φ R0 := by
  set Pa : Fin d → Polynomial O := fun k => ∑ y ∈ Finset.range K0, Polynomial.C (a y k m) * Polynomial.X ^ y
  set Pb : Fin d → Polynomial O := fun k => ∑ y ∈ Finset.range K0, Polynomial.C (bb y k m') * Polynomial.X ^ y
  set c : O := if m' = m then (l : O) ^ (2 * E) else 0
  set Q : Polynomial O := ∑ k, Pb k * Pa k - Polynomial.C c
  have hca : ∀ k y, y < K0 → (Pa k).coeff y = a y k m := by
    intro k y hy
    simp only [Pa, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single y (fun b _ hb => if_neg (Ne.symm hb)) (fun h => absurd (Finset.mem_range.2 hy) h)]
    simp
  have hcb : ∀ k y, y < K0 → (Pb k).coeff y = bb y k m' := by
    intro k y hy
    simp only [Pb, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single y (fun b _ hb => if_neg (Ne.symm hb)) (fun h => absurd (Finset.mem_range.2 hy) h)]
    simp
  have hQ : ∀ N < K0, Q.coeff N = 0 := by
    intro N hN
    apply hinj
    rw [map_zero]
    simp only [Q, Polynomial.coeff_sub, Polynomial.finsetSum_coeff, Polynomial.coeff_mul, Polynomial.coeff_C]
    have e1 : ∀ k, algebraMap O LL (∑ x ∈ Finset.HasAntidiagonal.antidiagonal N,
        (Pb k).coeff x.1 * (Pa k).coeff x.2) = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal N,
          (l : LL) ^ E * sol k x.1 m' * ((l : LL) ^ E * PowerSeries.coeff x.2 ((HM sol)⁻¹ k m)) := by
      intro k
      rw [map_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      rw [hca k x.2 (by omega), hcb k x.1 (by omega), map_mul, ha x.2 (by omega), hb x.1 (by omega)]
    rw [map_sub, map_sum]
    simp only [e1]
    have e2 : ∑ k, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal N,
        (l : LL) ^ E * sol k x.1 m' * ((l : LL) ^ E * PowerSeries.coeff x.2 ((HM sol)⁻¹ k m)) =
        (l : LL) ^ (2 * E) * ∑ k, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal N,
          sol k x.1 m' * PowerSeries.coeff x.2 ((HM sol)⁻¹ k m) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [e2, HM_coeff sol hHH N m' m]
    by_cases h1 : N = 0 <;> by_cases h2 : m' = m <;> simp [h1, h2, c]
  obtain ⟨R0, hR0⟩ := Polynomial.X_pow_dvd_iff.2 hQ
  refine ⟨R0, ?_⟩
  have hev := congrArg (Polynomial.aeval Φ) hR0
  simp only [Q, map_sub, map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, Pa, Pb] at hev
  rw [← hev]
  ring

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def cH (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T) (sh : ℕ → Fin d → O) : ℕ → W.DD T :=
  fun y => if y = 0 then 0 else -Formalism.MainNotions.LiftingTheory.vecB W T b (sh y)

theorem vecB_single (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T) (k : Fin d) :
    Formalism.MainNotions.LiftingTheory.vecB W T b (Pi.single k 1) = b k := by
  simp [Formalism.MainNotions.LiftingTheory.vecB, Pi.single_apply]

theorem ser_hor (hinj : Function.Injective (algebraMap O LL)) (hl : 2 ≤ PD.p) (T : LocLat G Qp LL O)
    (i : ZMod n) {d : ℕ} {b : Fin d → W.DD T} (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T i b) (k : Fin d)
    {sol : ℕ → Fin d → LL} (hsol : Formalism.MainNotions.LiftingTheory.IsSol W T i b 0 sol) (hs0 : sol 0 = Pi.single k 1)
    (sh : ℕ → Fin d → O) (hsh : ∀ y m, algebraMap O LL (sh y m) = (PD.p : LL) ^ Ex PD.p y * sol y m) :
    Formalism.MainNotions.CrystallineLiftingInputs.IsSer W T i (b k) (cH W T b sh) := by
  have hsh0 : sh 0 = Pi.single k 1 := by
    funext m
    apply hinj
    rw [hsh, hs0]
    by_cases h : m = k
    · subst h; simp [Ex]
    · simp [h]
  refine ⟨by simp [cH], fun y => ?_, fun K => ?_⟩
  · by_cases h : y = 0
    · simp only [cH, h, if_true]; exact DL_of W T i (InNΔi_zero W T i)
    · simp only [cH, h, if_false]
      have := Formalism.MainNotions.LiftingTheory.frame_vecB_mem W T i b hb (sh y)
      exact DL_of W T i (by rw [← neg_one_smul O]; exact InNΔi_osmul W T i _ this)
  · rcases Nat.eq_zero_or_pos K with rfl | hK
    · have hbk := Formalism.MainNotions.LiftingTheory.frame_vecB_mem W T i b hb (Pi.single k 1)
      rw [vecB_single] at hbk
      have hγ := InNΔi_γ W T i hbk
      refine ⟨0, W.γ T (b k) - b k, (W.N T).sub_mem hγ.1.1 hbk.1.1,
        fun δ hδ => by rw [map_sub, hγ.1.2 δ hδ, hbk.1.2 δ hδ], ?_⟩
      simp [Formalism.MainNotions.CrystallineLiftingInputs.eY]
    · set yv : ℕ → Fin d → O := fun r m => ((PD.p : ℕ) : O) ^ (Ex PD.p K - Ex PD.p r) * sh r m
      have hy : ∀ r < K, ∀ m, algebraMap O LL (yv r m) = (PD.p : LL) ^ Ex PD.p K * sol r m := by
        intro r hr m
        have hle := Ex_mono PD.p hl hr.le
        simp only [yv, map_mul, map_pow, map_natCast, hsh]
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
      obtain ⟨x, hx, hxe⟩ := hsol K (Ex PD.p K) yv hy
      have hS : ∑ r ∈ Finset.range K, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (yv r) = E0 W T K (b k) (cH W T b sh) := by
        obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
        rw [E0, Finset.sum_range_succ', Finset.sum_range_succ']
        have hv : ∀ r, Formalism.MainNotions.LiftingTheory.vecB W T b (yv r) =
            ((PD.p : ℕ) : O) ^ (Ex PD.p (K' + 1) - Ex PD.p r) • Formalism.MainNotions.LiftingTheory.vecB W T b (sh r) :=
          fun r => Formalism.MainNotions.LiftingTheory.frame_vecB_smul W T b _ (sh r)
        simp only [hv, hsh0, vecB_single, cH, Nat.succ_ne_zero, if_false, if_true, smul_zero, pow_zero,
          one_smul, smul_neg, Finset.sum_neg_distrib, sub_neg_eq_add, add_zero, Ex, Formalism.MainNotions.CrystallineLiftingInputs.eY]
        rw [add_comm]
        congr 1
        all_goals first
          | exact Finset.sum_congr rfl fun r _ => smul_comm _ _ _
          | simp
      refine ⟨0, x, hx.1.1, hx.1.2, ?_⟩
      rw [hS, smul_zero, sub_zero] at hxe
      rw [pow_zero, one_smul, ← truncatedSeries_gamma_sub, hxe]

theorem InI_of (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) (i : ZMod n) {x : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T i x) :
    Formalism.MainNotions.CrystallineLiftingInputs.InI W T i x := by
  obtain ⟨x', hx', e⟩ := (Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hA T hT).2.2 x hx.1
  refine ⟨(DL_of W T i hx).1, ⟨0, by simpa [Formalism.BasicNotions.LocWach.InvN] using hx.1.1⟩, x', hx'.1, hx'.2, ?_⟩
  rw [pow_one, e]

theorem aeval_mem_AΔ (P : Polynomial O) {Φ : LetA O n} (hΦ : Φ ∈ W.AΔ) : Polynomial.aeval Φ P ∈ W.AΔ := by
  rw [Polynomial.aeval_eq_sum_range]
  exact W.AΔ.sum_mem fun i _ => W.AΔ.smul_mem (W.AΔ.pow_mem hΦ i) _

theorem phiK (hπ : W.π₀ ∈ W.AΔ)
    (h2 : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * r))
    {j : ℕ} (hj : 1 ≤ j) (M X : ℕ) :
    ∃ e ∈ W.AΔ, ((W.φA ^ j) W.π₀) ^ (max M X + 1) = Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X * e := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  set K0 := max M X + 1
  obtain ⟨u, hu, -, -, -, h⟩ := h2 j K0
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hX : X ≤ (PD.p - 1) * K0 := by
    calc X ≤ K0 := by omega
      _ = 1 * K0 := (one_mul _).symm
      _ ≤ (PD.p - 1) * K0 := Nat.mul_le_mul_right _ (by omega)
  refine ⟨u * W.π₀ ^ (K0 - M) * Formalism.MainNotions.LiftingTheory.qp W ^ ((PD.p - 1) * K0 - X) *
      ∏ k ∈ Finset.range j', Formalism.MainNotions.LiftingTheory.pk W (k + 1) ^ ((PD.p - 1) * K0),
    W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem hu (W.AΔ.pow_mem hπ _))
      (W.AΔ.pow_mem (Formalism.MainNotions.LiftingTheory.lifta_qΔ W hπ) _))
      (W.AΔ.prod_mem fun k _ => W.AΔ.pow_mem (pk_mem_AΔ W hπ _) _), ?_⟩
  rw [h, Finset.prod_range_succ', Formalism.MainNotions.CrystallineLiftingInputs.fMX]
  have hp0 : Formalism.MainNotions.LiftingTheory.pk W 0 = Formalism.MainNotions.LiftingTheory.qp W := by simp [Formalism.MainNotions.LiftingTheory.pk]
  rw [hp0]
  have e1 : W.π₀ ^ K0 = W.π₀ ^ M * W.π₀ ^ (K0 - M) := by rw [← pow_add]; congr 1; omega
  have e2 : Formalism.MainNotions.LiftingTheory.qp W ^ ((PD.p - 1) * K0) =
      Formalism.MainNotions.LiftingTheory.qp W ^ X * Formalism.MainNotions.LiftingTheory.qp W ^ ((PD.p - 1) * K0 - X) := by rw [← pow_add]; congr 1; omega
  rw [e1, e2]
  ring

theorem zterm {A : Type} [CommRing A] (L f Φ r s g c : A) {e σ E : ℕ} (hle : e ≤ E)
    (hs : L ^ e * s = L ^ σ * r) (hg : Φ - r = f * g) :
    L ^ E * (s * c) = L ^ σ * (L ^ (E - e) * c * Φ) - f * (L ^ (E - e) * L ^ σ * g * c) := by
  obtain ⟨t, rfl⟩ : ∃ t, E = e + t := ⟨E - e, by omega⟩
  rw [Nat.add_sub_cancel_left, pow_add]
  linear_combination L ^ t * c * hs - L ^ t * L ^ σ * c * hg

theorem zs_rel (T : LocLat G Qp LL O) {d : ℕ}
    (b : Fin d → W.DD T) (k : Fin d) (j K0 σ : ℕ) (s : ℕ → LetA O n) (sh : ℕ → Fin d → O)
    (hsh0 : sh 0 = Pi.single k 1) (hK : 0 < K0) :
    ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) (b k) -
        ∑ y ∈ Finset.range K0, s y • ((W.φD T) ^ j) (cH W T b sh y) =
      (((PD.p : ℕ) : LetA O n) ^ σ - s 0) • ((W.φD T) ^ j) (b k) +
        ∑ m', (∑ y ∈ Finset.range K0, s y * algebraMap O (LetA O n) (sh y m')) • ((W.φD T) ^ j) (b m') := by
  have h1 : ∑ m', (∑ y ∈ Finset.range K0, s y * algebraMap O (LetA O n) (sh y m')) • ((W.φD T) ^ j) (b m') =
      ∑ y ∈ Finset.range K0, s y • ((W.φD T) ^ j) (Formalism.MainNotions.LiftingTheory.vecB W T b (sh y)) := by
    simp only [Finset.sum_smul, mul_smul, algebraMap_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.smul_sum, Formalism.MainNotions.LiftingTheory.vecB, map_sum]
    simp only [LinearMap.map_smul_of_tower]
  have h2 : ∀ y, s y • ((W.φD T) ^ j) (cH W T b sh y) =
      -(s y • ((W.φD T) ^ j) (Formalism.MainNotions.LiftingTheory.vecB W T b (sh y))) +
        if y = 0 then s 0 • ((W.φD T) ^ j) (b k) else 0 := by
    intro y
    by_cases hy : y = 0
    · subst hy
      simp [cH, hsh0, vecB_single]
    · simp [cH, hy]
  rw [h1, Finset.sum_congr rfl fun y _ => h2 y, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    Finset.sum_ite_eq' (Finset.range K0) 0, if_pos (Finset.mem_range.2 hK), lsmul_eq W T, sub_smul]
  simp only [Formalism.MainNotions.ArcLiftingSetup.lA]
  abel

def Zspan (T : LocLat G Qp LL O) (i : ZMod n) (j M X σ : ℕ) : Submodule (LetA O n) (W.DD T) :=
  Submodule.span (LetA O n) {z | ∃ w, w ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.InI W T i w ∧
    Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T i j M X σ w z}

theorem span_frame [NeZero n] [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (hsp : Formalism.MainNotions.ArcLiftingSetup.SATPcore W)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (h2 : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * r))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) {j M X σ : ℕ} (hj : 1 ≤ j)
    (r s : ℕ → LetA O n)
    (hrs : ∀ y, Formalism.MainNotions.CrystallineLiftingInputs.IsRem W j M X y (r y) ∧
      ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y * s y = ((PD.p : ℕ) : LetA O n) ^ σ * r y) :
    ∃ (d : ℕ) (b : Fin d → W.DD T), Formalism.MainNotions.LiftingTheory.IsFrameΔ W T i b ∧ ∀ m, ∃ p' ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T i j,
      ((PD.p : ℕ) : O) ^ (2 * σ) • ((W.φD T) ^ j) (b m) - Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X • p' ∈
        Zspan W T i j M X σ := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  set K0 := max M X + 1 with hK0
  set E := Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p K0
  set L : LetA O n := ((PD.p : ℕ) : LetA O n)
  set f := Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X
  set Φ := (W.φA ^ j) W.π₀
  have hπ := hR.πΔ
  have hΦ : Φ ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.PhiPowers.φA_pow_mem_AΔ W hπ j
  have hLA : ∀ t, L ^ t ∈ W.AΔ := fun t => W.AΔ.pow_mem (W.AΔ.natCast_mem _) _
  obtain ⟨d, b, hb⟩ := frame_exists W T i (Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hA T hT).2
  have esol := fun k : Fin d => ((hH hA T hT i).2.2.1 d b hb 0 ⟨0, InNΔi_zero W T i, (smul_zero _).symm⟩
    (Pi.single k 1)).1
  choose sol hsol hsol0 using esol
  have hs0 : ∀ k, sol k 0 = Pi.single k 1 := by
    intro k; funext m; rw [hsol0]
    by_cases h : m = k
    · subst h; simp
    · simp [h]
  have hbd := (hH hA T hT i).2.2.2.2 d b hb sol (fun k => ⟨hsol k, hs0 k⟩)
  have hHH := HM_inv sol hs0
  have h4 := (hH hA T hT i).2.2.2.1
  have esh : ∀ k y m', ∃ o : O, algebraMap O LL o = (PD.p : LL) ^ Ex PD.p y * sol k y m' :=
    fun k y m' => int_of_bd W hO2 y (h4 y) _ (hbd.1 k y m')
  choose sh hsh using esh
  have eiv : ∀ k m y, ∃ o : O, algebraMap O LL o =
      (PD.p : LL) ^ Ex PD.p y * PowerSeries.coeff y ((HM sol)⁻¹ k m) :=
    fun k m y => int_of_bd W hO2 y (h4 y) _ (hbd.2 k m y)
  choose iv hiv using eiv
  have hsh0 : ∀ k, sh k 0 = Pi.single k 1 := by
    intro k; funext m; apply hinj
    rw [hsh, hs0]
    by_cases h : m = k
    · subst h; simp [Ex]
    · simp [h]

  set zs : Fin d → W.DD T := fun k => ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) (b k) -
    ∑ y ∈ Finset.range K0, s y • ((W.φD T) ^ j) (cH W T b (sh k) y)
  have hzs : ∀ k, zs k ∈ Zspan W T i j M X σ := fun k => Submodule.subset_span
    ⟨b k, (hb.1 k).1.1, InI_of W h9 hA T hT i (hb.1 k),
      cH W T b (sh k), r, s, ser_hor W hinj hl T i hb k (hsol k) (hs0 k) (sh k) (hsh k), hrs, rfl⟩
  have hsA : ∀ y, s y ∈ W.AΔ := fun y => s_mem W (l_ne W) (rem_mem W hπ (hrs y).1) (hrs y).2
  set Z : Fin d → Fin d → LetA O n := fun k m' => ∑ y ∈ Finset.range K0, s y * algebraMap O (LetA O n) (sh k y m')
  set Z' : Fin d → Fin d → LetA O n := fun k m => ∑ y ∈ Finset.range K0, s y * algebraMap O (LetA O n) (iv k m y)
  have hZA : ∀ k m', Z k m' ∈ W.AΔ := fun k m' =>
    W.AΔ.sum_mem fun y _ => W.AΔ.mul_mem (hsA y) (W.AΔ.algebraMap_mem _)
  have hZ'A : ∀ k m, Z' k m ∈ W.AΔ := fun k m =>
    W.AΔ.sum_mem fun y _ => W.AΔ.mul_mem (hsA y) (W.AΔ.algebraMap_mem _)
  have hrel : ∀ k, zs k = (L ^ σ - s 0) • ((W.φD T) ^ j) (b k) + ∑ m', Z k m' • ((W.φD T) ^ j) (b m') :=
    fun k => zs_rel W T b k j K0 σ s (sh k) (hsh0 k) (by omega)
  obtain ⟨g0, hg0A, hg0⟩ := g_mem W hR (hrs 0).1
  have hs00 : L ^ σ - s 0 = f * (L ^ σ * g0) := by
    have h0 := (hrs 0).2
    simp only [Formalism.MainNotions.CrystallineLiftingInputs.eY, Nat.cast_zero, zero_mul, zero_div, Nat.ceil_zero, pow_zero, one_mul] at h0
    rw [pow_zero] at hg0
    rw [h0]
    linear_combination (L ^ σ) * hg0

  have eg := fun y => g_mem W hR (hrs y).1
  choose g hgA hg using eg
  have hEy : ∀ y ∈ Finset.range K0, Ex PD.p y ≤ E := fun y hy =>
    Ex_mono PD.p hl (le_of_lt (Finset.mem_range.1 hy))
  set P : Fin d → Fin d → LetA O n := fun k m' => ∑ y ∈ Finset.range K0,
    algebraMap O (LetA O n) (((PD.p : ℕ) : O) ^ (E - Ex PD.p y) * sh k y m') * Φ ^ y
  set P' : Fin d → Fin d → LetA O n := fun k m => ∑ y ∈ Finset.range K0,
    algebraMap O (LetA O n) (((PD.p : ℕ) : O) ^ (E - Ex PD.p y) * iv k m y) * Φ ^ y
  set U : Fin d → Fin d → LetA O n := fun k m' => ∑ y ∈ Finset.range K0,
    L ^ (E - Ex PD.p y) * L ^ σ * g y * algebraMap O (LetA O n) (sh k y m')
  set U' : Fin d → Fin d → LetA O n := fun k m => ∑ y ∈ Finset.range K0,
    L ^ (E - Ex PD.p y) * L ^ σ * g y * algebraMap O (LetA O n) (iv k m y)
  have hZ : ∀ k m', L ^ E * Z k m' = L ^ σ * P k m' - f * U k m' := by
    intro k m'
    simp only [Z, P, U, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [zterm L f (Φ ^ y) (r y) (s y) (g y) _ (hEy y hy) (hrs y).2 (show Φ ^ y - r y = f * g y from hg y),
      map_mul, map_pow, map_natCast]
  have hZ' : ∀ k m, L ^ E * Z' k m = L ^ σ * P' k m - f * U' k m := by
    intro k m
    simp only [Z', P', U', Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [zterm L f (Φ ^ y) (r y) (s y) (g y) _ (hEy y hy) (hrs y).2 (show Φ ^ y - r y = f * g y from hg y),
      map_mul, map_pow, map_natCast]
  have hPA : ∀ k m', P k m' ∈ W.AΔ := fun k m' =>
    W.AΔ.sum_mem fun y _ => W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hΦ _)
  have hP'A : ∀ k m, P' k m ∈ W.AΔ := fun k m =>
    W.AΔ.sum_mem fun y _ => W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hΦ _)
  have hUA : ∀ k m', U k m' ∈ W.AΔ := fun k m' => W.AΔ.sum_mem fun y _ =>
    W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (hLA _) (hLA _)) (hgA y)) (W.AΔ.algebraMap_mem _)
  have hU'A : ∀ k m, U' k m ∈ W.AΔ := fun k m => W.AΔ.sum_mem fun y _ =>
    W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (hLA _) (hLA _)) (hgA y)) (W.AΔ.algebraMap_mem _)
  obtain ⟨eK, heKA, heK⟩ := phiK W hπ h2 hj M X
  have hcong : ∀ m m', ∃ β ∈ W.AΔ, L ^ (2 * E) * ((if m' = m then L ^ (2 * σ) else 0) -
      ∑ k, Z' k m * Z k m') = f * β := by
    intro m m'
    obtain ⟨R0, hR0⟩ := poly_cong hinj PD.p K0 E sol hHH (fun y k m => ((PD.p : ℕ) : O) ^ (E - Ex PD.p y) * iv k m y)
      (fun y k m' => ((PD.p : ℕ) : O) ^ (E - Ex PD.p y) * sh k y m')
      (fun y hy k m => by
        rw [map_mul, map_pow, map_natCast, hiv, ← mul_assoc, ← pow_add,
          Nat.sub_add_cancel (hEy y (Finset.mem_range.2 hy))])
      (fun y hy k m' => by
        rw [map_mul, map_pow, map_natCast, hsh, ← mul_assoc, ← pow_add,
          Nat.sub_add_cancel (hEy y (Finset.mem_range.2 hy))])
      Φ m m'
    have hR0' : ∑ k, P k m' * P' k m = (if m' = m then L ^ (2 * E) else 0) +
        f * (eK * Polynomial.aeval Φ R0) := by
      have heK' : Φ ^ K0 = f * eK := heK
      rw [hR0, heK', mul_assoc]
      congr 1
      split_ifs <;> simp [L]
    have hsum : L ^ (2 * E) * ∑ k, Z' k m * Z k m' = L ^ (2 * σ) * ∑ k, P k m' * P' k m -
        f * ∑ k, (L ^ σ * P' k m * U k m' + L ^ σ * U' k m * P k m' - f * U' k m * U k m') := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      linear_combination (L ^ E * Z k m') * hZ' k m + (L ^ σ * P' k m - f * U' k m) * hZ k m'
    refine ⟨-(L ^ (2 * σ) * (eK * Polynomial.aeval Φ R0)) +
        ∑ k, (L ^ σ * P' k m * U k m' + L ^ σ * U' k m * P k m' - f * U' k m * U k m'), ?_, ?_⟩
    · refine W.AΔ.add_mem (W.AΔ.neg_mem (W.AΔ.mul_mem (hLA _) (W.AΔ.mul_mem heKA (aeval_mem_AΔ W R0 hΦ))))
        (W.AΔ.sum_mem fun k _ => W.AΔ.sub_mem (W.AΔ.add_mem
          (W.AΔ.mul_mem (W.AΔ.mul_mem (hLA _) (hP'A k m)) (hUA k m'))
          (W.AΔ.mul_mem (W.AΔ.mul_mem (hLA _) (hU'A k m)) (hPA k m')))
          (W.AΔ.mul_mem (W.AΔ.mul_mem (f_mem W hπ M X) (hU'A k m)) (hUA k m')))
    · rw [mul_sub, hsum, hR0']
      split_ifs
      · ring
      · ring
  refine ⟨d, b, hb, fun m => ?_⟩

  set D : Fin d → LetA O n := fun m' => (if m' = m then L ^ (2 * σ) else 0) - ∑ k, Z' k m * Z k m'
  have hDA : ∀ m', D m' ∈ W.AΔ := fun m' => W.AΔ.sub_mem (by split_ifs; exact hLA _; exact W.AΔ.zero_mem)
    (W.AΔ.sum_mem fun k _ => W.AΔ.mul_mem (hZ'A k m) (hZA k m'))
  set W1 := ∑ m', D m' • ((W.φD T) ^ j) (b m')
  have hW1 : W1 ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T i j :=
    (Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).sum_mem fun m' _ => Pp_gen W T i j (hDA m') (hb.1 m')
  have hW1f : Formalism.MainNotions.ArcLiftingSetup.InFP W T i j f W1 := by
    refine sat W hsp hA T hT i j M X hW1 (2 * E) ?_
    choose β hβA hβ using hcong m
    refine ⟨∑ m', β m' • ((W.φD T) ^ j) (b m'),
      (Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).sum_mem fun m' _ => Pp_gen W T i j (hβA m') (hb.1 m'), ?_⟩
    rw [lsmul_eq, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    exact hβ m'
  set G0 := ∑ k, (Z' k m * (L ^ σ * g0)) • ((W.φD T) ^ j) (b k)
  have hG0 : G0 ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T i j := (Formalism.MainNotions.ArcLiftingSetup.Pp W T i j).sum_mem fun k _ =>
    Pp_gen W T i j (W.AΔ.mul_mem (hZ'A k m) (W.AΔ.mul_mem (hLA _) hg0A)) (hb.1 k)
  have hV : ((PD.p : ℕ) : O) ^ (2 * σ) • ((W.φD T) ^ j) (b m) - ∑ k, Z' k m • zs k = W1 - f • G0 := by
    have e1 : ((PD.p : ℕ) : O) ^ (2 * σ) • ((W.φD T) ^ j) (b m) =
        ∑ m', (if m' = m then L ^ (2 * σ) else 0) • ((W.φD T) ^ j) (b m') := by
      rw [lsmul_eq]
      simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rfl
    have e2 : ∑ k, Z' k m • zs k = f • G0 + ∑ m', (∑ k, Z' k m * Z k m') • ((W.φD T) ^ j) (b m') := by
      simp only [hrel, smul_add, Finset.sum_add_distrib, hs00, G0, Finset.smul_sum, smul_smul, Finset.sum_smul]
      congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        congr 1; ring
      · rw [Finset.sum_comm]
    rw [e1, e2]
    simp only [W1, D, sub_smul, Finset.sum_sub_distrib]
    abel
  obtain ⟨p', hp', hVp⟩ := inMultiple_sub W T i j f hW1f (inMultiple_of_mem W T i j f hG0)
  refine ⟨p', hp', ?_⟩
  have : ((PD.p : ℕ) : O) ^ (2 * σ) • ((W.φD T) ^ j) (b m) - f • p' = ∑ k, Z' k m • zs k := by
    rw [← hVp, ← hV]; abel
  rw [this]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hzs k)

theorem span_gen [NeZero n] [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (hsp : Formalism.MainNotions.ArcLiftingSetup.SATPcore W)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (h2 : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * r))
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) {j M X σ : ℕ} (hj : 1 ≤ j)
    (r s : ℕ → LetA O n)
    (hrs : ∀ y, Formalism.MainNotions.CrystallineLiftingInputs.IsRem W j M X y (r y) ∧
      ((PD.p : ℕ) : LetA O n) ^ Formalism.MainNotions.CrystallineLiftingInputs.eY PD.p y * s y = ((PD.p : ℕ) : LetA O n) ^ σ * r y) :
    ∀ p ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T i j, ∃ p' ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T i j,
      ((PD.p : ℕ) : O) ^ (2 * σ) • p - Formalism.MainNotions.CrystallineLiftingInputs.fMX W M X • p' ∈ Zspan W T i j M X σ :=
  by apply _root_.UpperTheory.Reformulated.B.IntegerSpanGenerators.span_gen <;> assumption

end Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Classical

noncomputable section

namespace Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.UnusedSlot80.Relay2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem tTool2_of [NeZero n] [IsDomain O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hlm : ((PD.p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) : Formalism.MainNotions.CrystallineLiftingInputs.TTool2 W := by
  intro hA hl j M X σ hc
  have hj : 1 ≤ j := by rcases hc with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;> omega
  have hM : 1 ≤ M := by rcases hc with ⟨-, hM, -⟩ | ⟨-, rfl, -⟩ <;> omega
  have hsp : Formalism.MainNotions.ArcLiftingSetup.SATPcore W :=
    Formalism.MainNotions.UnusedSlot80.SatPW.satPCore_of W hinj (fun T hT => h9 T hT)
  have h2 := (hTr hA).2.1
  refine ⟨fun T hT i => ?_, ?_⟩
  · have h9r := (Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hA T hT).1
    have hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W := Formalism.MainNotions.LiftingTheory.lifta_ring_of W h9r
    obtain ⟨r, s, hrs⟩ := rs_ex W hTr hlm h9r hA hl hc
    refine ⟨fun w hw => trunc_ex W hinj hO2 h9 hH hTr hlm hA hl hc T hT i w hw,
      fun w z hw hz => ⟨b1 W T i hz, fp_pull W T i j _ (gamma_sub_of_frobenius_power W hR hsp hA h2 T hT i hj hw hz)⟩,
      fun w z z' _ hz hz' => fp_pull W T i j _ (uniq_alt_alt W hinj hO2 h9 hH hR hsp hA h2 T hT i hj hz hz'),
      fun a a' w w' z z' z'' _ _ hz hz' hz'' =>
        fp_pull W T i j _ (linear_of_frobenius_power W hinj hO2 h9 hH hR hsp hA h2 T hT i hj a a' hz hz' hz''),
      fun w z hw hw1 hz => fp_pull W T i j _ (uniformizer_dvd_of_frobenius_power W hinj hO2 h9 hH hR hsp hA h2 T hT i hj hM hw hw1 hz),
      span_gen W hinj hO2 h9 hH hR hsp hA h2 T hT i hj r s hrs⟩
  · intro T T' F hT hT' i w z z' _ hz hz'
    have hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W := Formalism.MainNotions.LiftingTheory.lifta_ring_of W (Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hA T hT).1
    exact fp_pull W T' i j _ (hermFlagUnipotent_anisotropic_vector_sub_mem W hinj hO2 h9 hH hR hsp hA h2 F hT hT' i hj hz hz')

end Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

namespace Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem truncation_clause_of_tools (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (h1 : Formalism.MainNotions.CrystallineLiftingInputs.adm1 D HW F Cm) (h8 : Formalism.MainNotions.CrystallineLiftingInputs.adm8 D HW F) (h9 : Formalism.MainNotions.CrystallineLiftingInputs.adm9 D HW F) :
    Formalism.MainNotions.CrystallineLiftingInputs.adm15 D HW F Cm := by
  refine ⟨Formalism.MainNotions.CrystallineLiftingInputs.TToolAlg_holds, fun l _ K LL hg _ => ?_⟩
  have hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hg) := (h1 l K 1 LL hg).2.2.2.2.2.2.2.2.1
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hO2 : ∀ x : ↥LL.1, 0 ≤ (D.loc l).v LL x → ∃ o : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 o = x :=
    fun x hx => ⟨⟨x, ((D.loc l).v_O LL x).1 hx⟩, rfl⟩
  letI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := Formalism.MainNotions.CrystallineLiftingInputs.OL.OL_complete_max (D.loc l) LL
  have hlm : (((((D.loc l).PD K).p : ℕ)) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [(D.loc l).PD_p K]; exact Formalism.MainNotions.CrystallineLiftingInputs.OL.l_mem_max (D.loc l) LL
  exact ⟨tTool1_of _ hinj hO2 hP9 (h8 l K 1 LL hg),
    tTool2_of _ hinj hO2 hlm hP9 (h8 l K 1 LL hg) (h9 l K 1 LL hg)⟩

end Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData
