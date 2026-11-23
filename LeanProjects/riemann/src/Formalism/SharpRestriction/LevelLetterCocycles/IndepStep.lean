import Formalism.SharpRestriction.LevelLetterCocycles.LamZero

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O]

theorem cmpD_sum (T : LocLat G Qp LL O) (a : ZMod n) {d : ℕ} (c : Fin d → LetA O n) (z : Fin d → W.DD T)
    (hz : ∀ m, z m ∈ W.N T) (hzl : ∀ m, (letE a : LetA O n) • z m = z m) :
    cmpD W T (∑ m, c m • z m) =
      ∑ m, algebraMap O LL (PowerSeries.constantCoeff (c m a)) • cmpD W T (z m) := by
  have hmem : ∀ m, c m • z m ∈ W.N T := fun m => (W.N T).smul_mem _ (hz m)
  have hs : ∑ m, c m • z m ∈ W.N T := (W.N T).sum_mem fun m _ => hmem m
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hs]
  have e : (⟨∑ m, c m • z m, hs⟩ : ↥(W.N T)) = ∑ m, (⟨c m • z m, hmem m⟩ : ↥(W.N T)) :=
    Subtype.ext (by simp)
  rw [e, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmp_smul_letter W T a (c m) (z m) (hz m) (hzl m),
    Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T (hz m)]

variable [NeZero n]

theorem indep_step (hinj : Function.Injective (algebraMap O LL)) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing (LL := LL) O v)
    (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (hT : Win W A T) {d : ℕ}
    (b : Fin d → W.DD T) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e : ℕ) (c : Fin d → LetA O n)
    (hc : ∀ m, c m ∈ W.AΔ) (hcl : ∀ m, letE (c' + (e : ZMod n)) * c m = c m)
    (h0 : ∑ m, c m • ((W.φD T) ^ e) (b m) = 0) :
    ∀ m, ∃ c₁ ∈ W.AΔ, letE (c' + (e : ZMod n)) * c₁ = c₁ ∧ c m = W.π₀ * c₁ := by
  set a : ZMod n := c' + (e : ZMod n) with hadef
  set Λ : LetA O n := abelian₂ W A a e with hΛdef
  have hz : ∀ m, InFNc W T a 1 (Λ • ((W.φD T) ^ e) (b m)) := fun m =>
    Formalism.MainNotions.UnusedSlot80.ArcC.arc_up W hs hR h5 A hA c' hc' e T hT _ (Formalism.MainNotions.UnusedSlot80.Relay2.Pp_phi W T c' e (hb.1 m))
  have hzN : ∀ m, Λ • ((W.φD T) ^ e) (b m) ∈ W.N T := fun m => by
    obtain ⟨y, hy, -, hye⟩ := hz m; rw [hye, one_smul]; exact hy.1
  have hzl : ∀ m, (letE a : LetA O n) • (Λ • ((W.φD T) ^ e) (b m)) = Λ • ((W.φD T) ^ e) (b m) := fun m => by
    obtain ⟨y, -, hyl, hye⟩ := hz m; rw [hye, one_smul]; exact hyl
  have hsum : ∑ m, c m • (Λ • ((W.φD T) ^ e) (b m)) = 0 := by
    rw [show ∑ m, c m • (Λ • ((W.φD T) ^ e) (b m)) = Λ • ∑ m, c m • ((W.φD T) ^ e) (b m) by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun m _ => smul_comm _ _ _, h0, smul_zero]
  have hcmp := cmpD_sum W T a c _ hzN hzl
  rw [hsum] at hcmp
  have hc0 : cmpD W T (0 : W.DD T) = 0 := by
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T (W.N T).zero_mem]
    exact (W.cmp T).map_zero
  rw [hc0] at hcmp
  obtain ⟨t, ht⟩ := cmpD_lam W hs hR hp0 h5 T h3 A hA c' hc' hT e
  have hfb := (Formalism.MainNotions.UnusedSlot80.ArcF.frame_basis W hs hV T h3 (h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT))
    hmod c' e b hb).1
  have hrel : ∑ m, algebraMap O LL (PowerSeries.constantCoeff (c m a)) •
      dv W T e b (Pi.single m 1) = 0 := by
    have hpt : ((PD.p : LL) ^ t) ≠ 0 := pow_ne_zero _ (Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W)
    rw [← hadef, ← hΛdef] at ht
    have e1 : ((PD.p : LL) ^ t) • ∑ m, algebraMap O LL (PowerSeries.constantCoeff (c m a)) •
        dv W T e b (Pi.single m 1) = 0 := by
      rw [hcmp, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [ht (b m) (hb.1 m), Formalism.MainNotions.UnusedSlot80.ArcF.dv_single, smul_comm]
    exact (smul_eq_zero.1 e1).resolve_left hpt
  have hcc : ∀ m i, PowerSeries.constantCoeff (c m i) = 0 := by
    intro m i
    by_cases hi : i = a
    · subst hi
      have := Fintype.linearIndependent_iff.1 hfb _ hrel m
      exact hinj (by rw [this, map_zero])
    · have := congrFun (hcl m) i
      rw [Pi.mul_apply, letE, Pi.single_eq_of_ne hi, zero_mul] at this
      rw [← this, map_zero]
  intro m
  have hinv : ∀ i, Formalism.MainNotions.WachCoordinates.Br.Inv1 W (c m i) := fun i δ hδ => by
    have := congrFun (hc m δ hδ) i
    rwa [γA_apply] at this
  choose f hf using fun i => Formalism.MainNotions.WachCoordinates.Br.ιOf_full hR (c m i) (hinv i)
  have hf0 : ∀ i, PowerSeries.constantCoeff (f i) = 0 := fun i => by
    rw [← Formalism.MainNotions.WachCoordinates.Br.ιOf_const hR, hf i, hcc m i]
  choose g hg using fun i => (PowerSeries.X_dvd_iff.2 (hf0 i))
  let c₂ : LetA O n := fun i => Formalism.MainNotions.WachCoordinates.Br.ιOf hR (g i)
  have hc₂ : c₂ ∈ W.AΔ := fun δ hδ => by
    funext i
    rw [γA_apply]
    exact Formalism.MainNotions.WachCoordinates.Br.ιOf_inv hR (g i) δ hδ
  have hcm : c m = W.π₀ * c₂ := by
    funext i
    rw [← hf i, hg i, map_mul, Formalism.MainNotions.WachCoordinates.Br.ιOf_X]
    rfl
  refine ⟨letE a * c₂, W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a) hc₂,
    by rw [← mul_assoc, letE_mul_self], ?_⟩
  rw [← hcl m, hcm]
  ring

end Formalism.MainNotions.UnusedSlot80.LevC
