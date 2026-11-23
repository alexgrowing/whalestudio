import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensFrame

noncomputable section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GenMass.GlueLoc

open Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Cnt

variable {D : D7} (Z : LocDat D)

def locSp : Formalism.L2.SG.CntLocal.LocSp D Z.M where
  V := Vp D
  H := locH Z
  rank := finrank_Vp
  bc := baseChange₂ D
  bc_smul := baseChange_smul₂
  bc_span := span_baseChange_eq_top
  bc_form p := baseChangeAt_form Z.M p (Z.hcj p)

theorem eq_of_latP {A B : LV D} (hA : A.FG) (hB : B.FG) (h : ∀ p, lattice₂ D Z.M p A = lattice₂ D Z.M p B) : A = B := by
  apply eq_of_locP
  intro P
  exact (locEqC_holds D Z (P.under (𝓞 D.host.F)) A B hA hB).1 (h _) P rfl

theorem mem_of_bcP {Λ : LV D} (hΛ : Λ.FG) {x : (VS D).V} (h : ∀ p, baseChange₂ D p x ∈ lattice₂ D Z.M p Λ) : x ∈ Λ := by
  have e : Λ ⊔ Submodule.span (𝓞 D.host.E) {x} = Λ := by
    refine eq_of_latP Z (hΛ.sup (Submodule.fg_span_singleton x)) hΛ fun p => ?_
    rw [BBTie.latP_sup, BBTie.latP_span, sup_eq_left, Submodule.span_le]
    rintro _ ⟨y, rfl, rfl⟩
    exact h p
  rw [← e]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)

theorem mem_dual_iff (Λ : LV D) (x : (VS D).V) :
    x ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ ↔ ∀ y ∈ Λ, (VS D).hT y x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

theorem unimod_of_loc {Λ : LV D} (hΛ : Λ.FG) (hloc : ∀ p, (locH Z p).IsSelfDual (lattice₂ D Z.M p Λ)) :
    Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := by
  have hf : ∀ p x y, (locH Z p).h (baseChange₂ D p x) (baseChange₂ D p y) = (D.s.atP p).ιE ((VS D).hT y x) :=
    fun p x y => baseChangeAt_form Z.M p (Z.hcj p) x y
  ext x
  rw [mem_dual_iff]
  constructor
  · intro h
    refine mem_of_bcP Z hΛ fun p => ((hloc p).2.2 _).2 fun w hw => ?_
    change LocFacts₂ Z.M p (baseChange₂ D p x) w ∈ _
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      change (locH Z p).h _ _ ∈ _
      rw [hf]
      obtain ⟨o, ho⟩ := Submodule.mem_one.1 (h y hy)
      rw [← ho]
      exact BBTie.bt_iota_int Z p o
    | zero => rw [LocFacts.localForm_zero_right]; exact zero_mem _
    | add a b _ _ ha hb => rw [LocFacts.localForm_add_right]; exact add_mem ha hb
    | smul o w _ hw =>
      change LocFacts₂ Z.M p (baseChange₂ D p x) ((o : (D.s.atP p).Ep) • w) ∈ _
      rw [LocFacts.localForm_smul_right]
      exact mul_mem (LocFacts.lf_cjM_mem Z p _ o.2) hw
  · intro hx y hy
    refine DualityBasisChange.locGlobIntE D _ fun p => ?_
    rw [← hf, ← (Z.agree p).2.2.2.1]
    exact ((hloc p).2.2 (baseChange₂ D p x)).1 (Submodule.subset_span ⟨x, hx, rfl⟩) (baseChange₂ D p y)
      (Submodule.subset_span ⟨y, hy, rfl⟩)

variable (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) {T T' : D.host.E}
  (G : LFlag (VS D) D.R.rS T) (G' : LFlag (VS D) D.R.rS T')

theorem mmfam_eq (p : PlF D) (Λ : Submodule (Z.M p).L.O (Vp D p)) :
    (locH Z p).MMfam (tm FP G G' p Λ) = DualityBasisChange.locFam (locSp Z) Z.δ p G.fl G' := by
  funext b
  unfold Loc.HermSp.MMfam
  cases hs : (Z.M p).split with
  | none =>
    rw [DualityBasisChange.locFam_none (locSp Z) p G.fl G' hs]
    rcases b with a | a <;> rfl
  | some g =>
    rcases b with a | a
    · rw [DualityBasisChange.locFam_some_inl (locSp Z) p G.fl G' hs]; rfl
    · rw [DualityBasisChange.locFam_some_inr (locSp Z) p G.fl G' hs]; rfl

theorem span_mmfam (p : PlF D) (Λ : Submodule (Z.M p).L.O (Vp D p)) :
    Submodule.span (Z.M p).L.O (Set.range ((locH Z p).MMfam (tm FP G G' p Λ))) =
      lattice₂ D Z.M p (MMof D G.fl G') := by
  rw [mmfam_eq]
  exact DualityBasisChange.span_locFam Z.agree (locSp Z) p G.fl G'

theorem mmof_latIn : IsLatIn (UPair D G.fl G') (MMof D G.fl G') := by
  rw [R3.MMof_eq]; exact R3.BB_latIn D G.fl G'

theorem spanE_mmfam (p : PlF D) (Λ : Submodule (Z.M p).L.O (Vp D p)) :
    Submodule.span (D.s.atP p).Ep (Set.range ((locH Z p).MMfam (tm FP G G' p Λ))) =
      Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (UPair D G.fl G' : Set (VS D).V)) := by
  rw [← BBTie.bt_spanEp_spanO Z p, span_mmfam, lattice₂, BBTie.bt_spanEp_spanO Z p, ← (mmof_latIn G G').2,
    BBTie.bt_spanEp_spanE]

theorem glue_iff_local : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (G : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), LinearIndependent D.host.E (Sum.elim (frame G) (frame G')) → ∀ Λ : LV D, Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') ↔ Submodule.IsLattice D.host.E Λ ∧ ∀ p, (locH Z p).IsSelfDual (lattice₂ D Z.M p Λ) ∧ (∀ i, (locH Z p).MMfam (tm FP G G' p (lattice₂ D Z.M p Λ)) i ∈ lattice₂ D Z.M p Λ) ∧ ¬ LocNG.BBne (H := locH Z p) (tm FP G G' p (lattice₂ D Z.M p Λ)) := by
  intro D Z FP u u' G G' _ Λ
  constructor
  · rintro ⟨hL, hU, hM⟩
    refine ⟨hL, fun p => ?_⟩
    have hle : lattice₂ D Z.M p (MMof D G.fl G') ≤ lattice₂ D Z.M p Λ :=
      BBTie.latP_mono Z p (hM ▸ inf_le_left)
    refine ⟨BBTie.bt_selfDual Z (locUnimodC_holds D Z) p Λ hL hU, fun i => hle ?_, ?_⟩
    · rw [← span_mmfam Z FP G G' p (lattice₂ D Z.M p Λ)]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [BBTie.bt_bbne_iff Z p (locSatC_holds D Z) (tm FP G G' p (lattice₂ D Z.M p Λ)) Λ
        (MMof D G.fl G') (UPair D G.fl G') hL.fg rfl
        (span_mmfam Z FP G G' p _) (spanE_mmfam Z FP G G' p _) hle, not_not]
      exact congrArg _ hM
  · rintro ⟨hL, h⟩
    refine ⟨hL, unimod_of_loc Z hL.fg fun p => (h p).1, ?_⟩
    refine eq_of_latP Z (Submodule.FG.of_le hL.fg inf_le_left) (mmof_latIn G G').1 fun p => ?_
    have hle : lattice₂ D Z.M p (MMof D G.fl G') ≤ lattice₂ D Z.M p Λ := by
      rw [← span_mmfam Z FP G G' p (lattice₂ D Z.M p Λ), Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (h p).2.1 i
    have h3 := (h p).2.2
    rw [BBTie.bt_bbne_iff Z p (locSatC_holds D Z) (tm FP G G' p (lattice₂ D Z.M p Λ)) Λ
        (MMof D G.fl G') (UPair D G.fl G') hL.fg rfl
      (span_mmfam Z FP G G' p _) (spanE_mmfam Z FP G G' p _) hle, not_not] at h3
    exact h3

end GlobalTheory.GenMass.GlueLoc
