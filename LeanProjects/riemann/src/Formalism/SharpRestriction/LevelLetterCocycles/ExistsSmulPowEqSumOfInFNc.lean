import Formalism.SharpRestriction.LevelLetterCocycles.DvOZeroHigh

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

variable [IsDomain O] [NeZero n]

structure Ctx : Prop where
  hbij : Function.Bijective (algebraMap K₀ K)
  hs : W.s = 1
  hp2 : PD.p ≠ 2
  h5p : 5 ≤ PD.p
  hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W
  h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
    Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h
  h3 : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.p3 W T
  hmod : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀
  hΔ : IsUnit ((W.DelF.card : ℕ) : O)
  hsat : SATcore W
  hsatP : SATPcore W
  hTr : Formalism.MainNotions.LiftingTheory.coreTr W
  hH : Formalism.MainNotions.LiftingTheory.coreH W
  hinj : Function.Injective (algebraMap O LL)
  hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x
  hV : Formalism.MainNotions.WachCoordinates.Br.ValRing (LL := LL) O v
  hp0 : ((PD.p : ℕ) : O) ≠ 0

variable {W}

theorem Ctx.hCA (C : Ctx W) : Formalism.MainNotions.LiftingTheory.CaseA W := ⟨C.hbij, C.hs, C.hp2⟩

theorem exists_smul_pow_eq_sum_of_inFNc (C : Ctx W) (T : LocLat G Qp LL O) (A : ArcP n) (hA : A.OK) (hT : Win W A T) (a : ZMod n)
    (N₁ : ℕ) (hN₁ : Hw A.G₀ A.S A.η (A.ty (a + 1)) ≤ N₁) (x : W.DD T) (hx : InFNc W T (a + 1) 1 x) :
    ∃ (r : ℕ) (bb : Fin r → W.DD T) (β : Fin r → LetA O n), (∀ j, Formalism.MainNotions.LiftingTheory.InNΔi W T a (bb j)) ∧
      (∀ j, β j ∈ W.AΔ) ∧ ps W 0 ^ N₁ • x = ∑ j, β j • W.φD T (bb j) := by
  have h5T := C.h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)
  obtain ⟨y, hyN, hya, rfl⟩ := hx
  rw [one_smul]
  have hyl : y ∈ W.Nl T (a + 1) := ⟨y, hyN.1, by rw [LinearMap.smul_apply, LinearMap.id_apply]; exact hya⟩
  have h1 := Formalism.MainNotions.UnusedSlot80.ArcC.iter_down W C.hs T h5T (a + 1) 1 y hyl
  rw [Finset.prod_range_one, pow_zero, AlgHom.one_apply, Nat.cast_zero, sub_zero, Nat.cast_one,
    add_sub_cancel_right] at h1
  obtain ⟨w, hw, w', hww, -⟩ := q_unit W C.hR C.hp0
  have hp0w : ps W 0 = w' * W.q := by rw [hw, ← mul_assoc, mul_comm w', hww, one_mul]
  obtain ⟨dd, hdd⟩ := Nat.exists_eq_add_of_le hN₁
  have e1 : ps W 0 ^ N₁ • y = (w' ^ N₁ * W.q ^ dd) • (W.q ^ Hw A.G₀ A.S A.η (A.ty (a + 1)) • y) := by
    rw [hp0w, smul_smul, hdd]; congr 1; ring
  have h2 := Submodule.smul_mem _ (w' ^ N₁ * W.q ^ dd) h1
  rw [← e1] at h2
  obtain ⟨⟨r, bb0, hb0, huniq, -⟩, -⟩ := C.hmod T hT.1
  have h3 := Formalism.MainNotions.UnusedSlot80.ArcC.span_pow_le W T bb0 (fun z hz => (huniq z hz).exists) a 1 h2
  obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun (LetA O n)).1 h3
  have hbΔ : ∀ j, Formalism.MainNotions.LiftingTheory.InNΔi W T a ((letE a : LetA O n) • bb0 j) := fun j =>
    ⟨Formalism.MainNotions.UnusedSlot80.PhiPowers.smul_mem_NΔ W T (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a) (hb0 j),
      ⟨bb0 j, (hb0 j).1, by rw [LinearMap.smul_apply, LinearMap.id_apply]⟩⟩
  have hp0Δ : ps W 0 ^ N₁ ∈ W.AΔ := W.AΔ.pow_mem (ps_mem_AΔ W C.hR.1 0) N₁
  obtain ⟨dd, hd, hzd⟩ := Formalism.MainNotions.WachCoordinates.Br.average C.hΔ cc
    (fun j => (W.φD T ^ 1 : Module.End O (W.DD T)) ((letE a : LetA O n) • bb0 j))
    (fun j δ hδ => φD_pow_Δ W T (hbΔ j).1.2 1 δ hδ)
    (fun δ hδ => (Formalism.MainNotions.UnusedSlot80.PhiPowers.smul_mem_NΔ W T hp0Δ hyN).2 δ hδ) hcc.symm
  refine ⟨r, fun j => (letE a : LetA O n) • bb0 j, dd, hbΔ, hd, ?_⟩
  rw [hzd]
  simp only [pow_one]

theorem up1 (C : Ctx W) (T : LocLat G Qp LL O) (A : ArcP n) (hA : A.OK) (hT : Win W A T) (a : ZMod n)
    (H : ℕ) (hH : Mw A.G₀ A.S A.η (A.ty (a + 1)) ≤ H) {vv : LetA O n} (hv : vv ∈ W.AΔ) (y : W.DD T)
    (hy : InFNc W T a 1 y) : InFNc W T (a + 1) 1 ((ps W 0 ^ H * vv) • W.φD T y) := by
  have h5T := C.h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)
  obtain ⟨y', hy'N, hy'l, rfl⟩ := hy
  rw [one_smul]
  have hQ : W.Q = W.q := by simp [LocWach.Q, C.hs]
  have hyl : y' ∈ W.Nl T (a + 1 - 1) := by
    rw [add_sub_cancel_right]
    exact ⟨y', hy'N.1, by rw [LinearMap.smul_apply, LinearMap.id_apply]; exact hy'l⟩
  have hM := h5T.1 (a + 1) y' hyl
  rw [hQ] at hM
  obtain ⟨w, hw, w', hww, -⟩ := q_unit W C.hR C.hp0
  have hp0w : ps W 0 = w' * W.q := by rw [hw, ← mul_assoc, mul_comm w', hww, one_mul]
  have hN : (ps W 0 ^ H * vv) • W.φD T y' ∈ W.N T := by
    obtain ⟨dd, hdd⟩ := Nat.exists_eq_add_of_le hH
    have e1 : (ps W 0 ^ H * vv) • W.φD T y' = (w' ^ H * W.q ^ dd * vv) •
        (W.q ^ Mw A.G₀ A.S A.η (A.ty (a + 1)) • W.φD T y') := by
      rw [hp0w, smul_smul]; congr 1; rw [hdd]; ring
    rw [e1]
    exact (W.N T).smul_mem _ hM
  have hΔ : ∀ δ ∈ W.DelF, W.γD T δ ((ps W 0 ^ H * vv) • W.φD T y') = (ps W 0 ^ H * vv) • W.φD T y' := by
    intro δ hδ
    rw [Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA', (W.AΔ.mul_mem (W.AΔ.pow_mem (ps_mem_AΔ W C.hR.1 0) H) hv) δ hδ,
      ← W.φγ_comm, hy'N.2 δ hδ]
  refine ⟨_, ⟨hN, hΔ⟩, ?_, by rw [one_smul]⟩
  rw [smul_comm]
  congr 1
  have := φD_pow_letter W T a y' hy'l 1
  simpa using this

end Formalism.MainNotions.UnusedSlot80.LevC
