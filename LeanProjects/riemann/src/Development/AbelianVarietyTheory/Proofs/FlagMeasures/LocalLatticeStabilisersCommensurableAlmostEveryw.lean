import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemH0sub
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTermStabilizerCommensurableStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DatumStabilizerPreservesTermLatticeGoodPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinitePlacesNotPrimeToBaseFrameInvariantsStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Unfold.LocStab

theorem finrank_Vp_eq (D : D7) (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have := D.R.two_le_m; obtain ⟨t, ht⟩ := D.R.m_even
  unfold Ranks.rS Ranks.r; omega

theorem relIndex_comap_subtype {G : Type*} [Group G] (U X Y : Subgroup G) (hY : Y ≤ U) :
    (X.comap U.subtype).relIndex (Y.comap U.subtype) = X.relIndex Y := by
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_of_le_right hY]

theorem stabilizer_eq_comap {G α : Type*} [Group G] (U : Subgroup G) [MulAction U α] (S : Subgroup G) (d : α)
    (h : ∀ g : U, g.1 ∈ S ↔ g • d = d) : MulAction.stabilizer U d = S.comap U.subtype := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_comap, Subgroup.coe_subtype, h g]

theorem comap_subtype_inf {G : Type*} [Group G] (U A : Subgroup G) :
    (U ⊓ A).comap U.subtype = A.comap U.subtype := by
  ext g; simp

end GlobalTheory.Unfold.LocStab

namespace GlobalTheory.Unfold.LocStab

set_option maxHeartbeats 1000000 in

theorem local_stabilisers : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ [∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p))], (∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d') → (∀ p (d : LocNG.Datum (FP p)) (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ g • d = d) → ∀ (Λ₀ : LV D) (d0 : Dat Z FP), LocOver Λ₀ d0 → (∀ p, (MulAction.stabilizer ↥(FP p).UW0 (d0 p)).relIndex ((LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype) ≠ 0 ∧ ((LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) ≠ 0) ∧ {p | (LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype ≠ MulAction.stabilizer ↥(FP p).UW0 (d0 p)}.Finite ∧ ∀ d : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d p) τ) → ∀ p, (MulAction.stabilizer ↥(FP p).UW0 (d0 p)).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d p)) ≠ 0 ∧ (MulAction.stabilizer ↥(FP p).UW0 (d p)).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) ≠ 0 ∧ GlobalTheory.HL.invVol (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) (MulAction.stabilizer ↥(FP p).UW0 (d p)) = LocNG.Datum.wt (d0 p) (d p) := by
  intro D X Y u u' F F' w hw hG Z FP hB hRel _ hMv hSt Λ₀ d0 hLO
  have hOK : ∀ p, (Z.M p).OK := fun p => (Z.agree p).1
  have hstab : ∀ p (d : LocNG.Datum (FP p)),
      MulAction.stabilizer ↥(FP p).UW0 d = (LocNG.Datum.Stab d).comap (FP p).UW0.subtype :=
    fun p d => stabilizer_eq_comap _ _ d (fun g => hSt p d g)
  have hle : ∀ p (d : LocNG.Datum (FP p)), LocNG.Datum.Stab d ≤ (FP p).UW0 :=
    fun p d => Subgroup.closure_le _ |>.2 fun g hg => hg.1
  choose τ0 hτ0 hτ0L using hLO.2
  have hc := fun p => GlobalTheory.T.hermitianTerm_stabilizer_commensurable (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_Vp_eq D p)
    (hRel p) (d0 p) (τ0 p) (hτ0 p)
  have hA : ∀ p, (LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype =
      ((FP p).UW0 ⊓ LocNG.Aut (τ0 p).abelian₂).comap (FP p).UW0.subtype := by
    intro p; rw [comap_subtype_inf, hτ0L p]
  refine ⟨fun p => ?_, ?_, fun d hd p => ?_⟩
  · rw [hA p, hstab p]
    refine ⟨?_, ?_⟩
    · rw [relIndex_comap_subtype _ _ _ inf_le_left, Subgroup.relIndex_eq_one.2 (hc p).1]
      exact one_ne_zero
    · rw [relIndex_comap_subtype _ _ _ (hle p (d0 p))]
      exact (hc p).2.1
  · have hAt : ∀ p, GlobalTheory.LocOver.AtBase Z p F F' (Tu D u) (Tu D u') (FP p) := fun p => by
      obtain ⟨h1, h2, h3, h4⟩ := hB p
      exact ⟨h1, h2, h3, h4⟩
    refine (GlobalTheory.T.finite_places_not_primeTo_baseFrameInvariants D Z u u' F F' hG FP hAt).subset fun p hp hpr => hp ?_
    have h2 := GlobalTheory.T.datumStabilizer_preserves_termLattice_goodPlace (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_Vp_eq D p)
      (hRel p) hpr (d0 p) (τ0 p) (hτ0 p)
    rw [hA p, hstab p]
    exact congrArg _ (le_antisymm (hc p).1 (le_inf (hle p (d0 p)) h2))
  · obtain ⟨τ, hτ⟩ := hd p
    have h3 := (hc p).2.2
    have hτc := GlobalTheory.T.hermitianTerm_stabilizer_commensurable (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_Vp_eq D p)
      (hRel p) (d p) τ hτ
    rw [hstab p, hstab p, relIndex_comap_subtype _ _ _ (hle p (d p)),
      relIndex_comap_subtype _ _ _ (hle p (d0 p))]
    refine ⟨h3 (d p) τ hτ, hτc.2.2 (d0 p) (τ0 p) (hτ0 p), ?_⟩
    rw [GlobalTheory.HL.invVol, relIndex_comap_subtype _ _ _ (hle p (d p)),
      relIndex_comap_subtype _ _ _ (hle p (d0 p)), LocNG.Datum.wt, LocNG.volRel, one_div_div]

end GlobalTheory.Unfold.LocStab
