import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalAutomorphismLocalExtensionMovesLatticesStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemH0sub
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Unfold.massA_eq_sum_orbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (φ : ↥(FlagPairStabilizer F F') →* (∀ p, ↥(FP p).UW0)), (∀ (h : ↥(FlagPairStabilizer F F')) p, Ext p (h : GV D) ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p)) → Function.Injective φ → ∀ [∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p))], (∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d') → ∀ d : Dat Z FP, massA F F' d = ∑' o : Quot (fun y y' : (∀ p, LocNG.Datum (FP p)) => ∃ h : ↥(FlagPairStabilizer F F'), (fun p => φ h p • y p) = y'), if (∀ p, ∃ g : ↥(FP p).UW0, g • d p = o.out p) ∧ {p | o.out p ≠ d p}.Finite then (({h : ↥(FlagPairStabilizer F F') | (fun p => φ h p • o.out p) = o.out}.encard : ℝ≥0∞))⁻¹ else 0 := by
  intro D X Y u u' F F' w hw hG Z FP hB hR φ hφ _hinj _inst hmov d

  have huniq := (GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hR).1

  have key : ∀ (h : ↥(FlagPairStabilizer F F')) (y y' : Dat Z FP),
      RMoves h.1 y y' ↔ (fun p => φ h p • y p) = y' := by
    intro h y y'
    constructor
    · intro hm
      funext p
      obtain ⟨g', hg', hmv⟩ := hm p
      have he : g' = ((φ h p : ↥(FP p).UW0) : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) :=
        (huniq h.1 p).unique hg' (hφ h p)
      subst he
      exact (hmov p (φ h p) (y p) (y' p)).1 hmv
    · intro he p
      exact ⟨_, hφ h p, (hmov p (φ h p) (y p) (y' p)).2 (congrFun he p)⟩

  have hrel : GRel (Z := Z) (FP := FP) F F' =
      (fun y y' : (∀ p, LocNG.Datum (FP p)) => ∃ h : ↥(FlagPairStabilizer F F'), (fun p => φ h p • y p) = y') := by
    funext y y'
    apply propext
    constructor
    · rintro ⟨h, hh, hm⟩
      exact ⟨⟨h, (mem_H0sub F F' h).2 hh⟩, (key ⟨h, (mem_H0sub F F' h).2 hh⟩ y y').1 hm⟩
    · rintro ⟨h, hh⟩
      exact ⟨h.1, (mem_H0sub F F' h.1).1 h.2, (key h y y').2 hh⟩

  have hstab : ∀ y : Dat Z FP, (stabY F F' y).encard =
      {h : ↥(FlagPairStabilizer F F') | (fun p => φ h p • y p) = y}.encard := by
    intro y
    have hs : stabY F F' y = Subtype.val '' {h : ↥(FlagPairStabilizer F F') | (fun p => φ h p • y p) = y} := by
      ext g
      constructor
      · rintro ⟨hg, hm⟩
        exact ⟨⟨g, (mem_H0sub F F' g).2 hg⟩, (key ⟨g, (mem_H0sub F F' g).2 hg⟩ y y).1 hm, rfl⟩
      · rintro ⟨h, hh, rfl⟩
        exact ⟨(mem_H0sub F F' h.1).1 h.2, (key h y y).2 hh⟩
    rw [hs, Subtype.val_injective.encard_image]
  rw [massA, hrel]
  refine tsum_congr fun o => ?_

  have hin : InGen d o.out ↔
      (∀ p, ∃ g : ↥(FP p).UW0, g • d p = o.out p) ∧ {p | o.out p ≠ d p}.Finite := by
    unfold InGen
    refine and_congr (forall_congr' fun p => ?_) Iff.rfl
    constructor
    · rintro ⟨g, hg, hm⟩
      exact ⟨⟨g, hg⟩, (hmov p ⟨g, hg⟩ (d p) (o.out p)).1 hm⟩
    · rintro ⟨g, hg⟩
      exact ⟨g.1, g.2, (hmov p g (d p) (o.out p)).2 hg⟩
  by_cases hc : (∀ p, ∃ g : ↥(FP p).UW0, g • d p = o.out p) ∧ {p | o.out p ≠ d p}.Finite
  · rw [if_pos (hin.2 hc), if_pos hc, hstab]
  · rw [if_neg (mt hin.1 hc), if_neg hc]
