import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfLevelZeroParts

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

theorem dvO_zero_hw (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (T : LocLat G Qp LL O)
    (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e : ℕ)
    (a : ZMod n) (s : ℕ) (u : ℤ) (hu : (Hw A.G₀ A.S A.η (A.ty (a - (s : ZMod n))) : ℤ) < u)
    (c₀ : Fin d → O) (h : dvO W T e b c₀ ∈ FilS W T a s u) : c₀ = 0 := by
  obtain ⟨y, ⟨hyF, hyD⟩, hye⟩ := h
  set i : ZMod n := a - (s : ZMod n) with hidef
  obtain ⟨τ, hτ, hover⟩ := tau_over W C.hbij i
  have hJ : ∀ z, IsJumpV PD T.ρ τ z → z ≤ (Hw A.G₀ A.S A.η (A.ty i) : ℤ) := fun z hz =>
    (Formalism.MainNotions.UnusedSlot80.PhiPowers.win_sub A.G₀ A.S A.η (A.ty i) (hA.2.2.2.2.1 i) (hT.2 i τ hτ z hz)).2
  have hy0 := fil_high W T i τ hover C.hbij.2 _ hJ u hu hyD hyF
  rw [hy0, map_zero] at hye
  have hfb := (Formalism.MainNotions.UnusedSlot80.ArcF.frame_basis W C.hs C.hV T (C.h3 T hT.1)
    (C.h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)) (C.hmod T hT.1) c' e b hb).1
  have hdv : dvO W T e b c₀ = ∑ m, algebraMap O LL (c₀ m) • dv W T e b (Pi.single m 1) := by
    simp only [Formalism.MainNotions.UnusedSlot80.ArcF.dv_single]; rfl
  have hsum : ∑ m, algebraMap O LL (c₀ m) • dv W T e b (Pi.single m 1) = 0 := by rw [← hdv, ← hye]
  funext m
  apply C.hinj
  rw [Fintype.linearIndependent_iff.1 hfb _ hsum m]
  simp

theorem filS_anti (T : LocLat G Qp LL O) (a : ZMod n) (s : ℕ) {u w : ℤ} (h : w ≤ u) :
    FilS W T a s u ≤ FilS W T a s w := by
  apply Submodule.map_mono
  intro x hx
  exact ⟨Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ h hx.1, hx.2⟩

theorem inId_zero (a : ZMod n) (e : ℕ) : InId W a e (fun _ => 0) 0 :=
  ⟨0, W.AΔ.zero_mem, by simp⟩

theorem condPole_of_polar (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (T : LocLat G Qp LL O)
    (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (c : ZMod n)
    (α : ℕ → ℤ) (c₀ : Fin d → O) (hc₀ : c₀ ≠ 0)
    (hP : Formalism.MainNotions.UnusedSlot80.LevC.condPolar (W := W) T c (A.len c) b α c₀) :
    condPole W A T c b α c₀ := by
  intro s hs
  have key : 0 ≤ α s ∨ -(Hw A.G₀ A.S A.η (A.ty (c - (s : ZMod n))) : ℤ) ≤ α s ∧
      dvO W T (A.len c) b c₀ ∈ FilS W T c s (-(α s)) := by
    rcases hP s hs with h | h
    · exact Or.inl h
    · by_cases h0 : 0 ≤ α s
      · exact Or.inl h0
      · refine Or.inr ⟨?_, h⟩
        by_contra hlt
        exact hc₀ (dvO_zero_hw W C A hA c' T hT b hb (A.len c) c s (-(α s)) (by omega) c₀ h)
  cases hty : A.ty (c - (s : ZMod n)) with
  | thin =>
    rw [hty] at key
    simp only [Hw] at key
    rcases key with h | ⟨h, -⟩ <;> omega
  | up bs =>
    rw [hty] at key
    simp only [Hw] at key
    rcases key with h | ⟨h, -⟩ <;> push_cast at h ⊢ <;> omega
  | down bs =>
    rcases key with h | ⟨-, h⟩
    · exact Or.inl h
    · by_cases h0 : 0 ≤ α s
      · exact Or.inl h0
      · exact Or.inr (filS_anti W T c s (by omega) h)

variable {W}

theorem polarToPole_of_ctx (C : Ctx W) : Formalism.MainNotions.UnusedSlot80.Split.PolarToPole W := by
  intro _ _ A hA T₂ hT c hc d b sol hb f hS
  obtain ⟨I, g, c₀, α, hg, hF⟩ := hS
  refine ⟨I, fun i => if c₀ i = 0 then 0 else g i, c₀, fun i => if c₀ i = 0 then fun _ => 0 else α i,
    fun i => ?_, fun k => ?_⟩
  · by_cases h0 : c₀ i = 0
    · simp only [h0, if_true]
      refine ⟨inId_zero W c (A.len c), ?_⟩
      intro s _
      cases A.ty (c - (s : ZMod n)) with
      | thin => simp
      | up bs => simp
      | down bs => exact Or.inl le_rfl
    · simp only [h0, if_false]
      exact ⟨(hg i).1, condPole_of_polar W C A hA _ T₂ hT b hb.1 c (α i) (c₀ i) h0 (hg i).2⟩
  · rw [hF k]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h0 : c₀ i = 0
    · simp [h0]
    · simp [h0]

end Formalism.MainNotions.UnusedSlot80.LevC

namespace Formalism.MainNotions.UnusedSlot80.Split

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

theorem polarToPoleL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h : AdmArcA D HW F Cm) : PolarToPoleL D HW := by
  intro l _ K LL hG hCA h5l
  have := neZero_finrank_max_unramified K
  exact LevC.polarToPole_of_ctx (ctx_of D HW F Cm h l K LL hG hCA h5l)

end Formalism.MainNotions.UnusedSlot80.Split
