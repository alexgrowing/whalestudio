import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsComplementUnitaryMulActionLocalInnerDatumStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesLocalTermsWithDataStatement

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatLocMove

variable {D : D7}

theorem isLattice_gmap' (g : GV D) (A : LV D) (hA : Submodule.IsLattice D.host.E A) :
    Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap g A) := by
  refine ⟨hA.fg.map _, ?_⟩
  have : (Formalism.HermitianLatticesTheory.gmap g A : Set (VS D).V) = (g : (VS D).V →ₗ[D.host.E] (VS D).V) '' (A : Set (VS D).V) := rfl
  rw [this, ← Submodule.map_span, hA.span_eq_top, Submodule.map_top]
  exact LinearEquiv.range g

theorem finrank_Vp_eq (p : PlF D) : Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  obtain ⟨c, hc⟩ := h1
  simp only [Ranks.r, Ranks.rS]
  omega

end GlobalTheory.RatLocMove

namespace GlobalTheory.RatLocMove

open GlobalTheory.LocExt

variable {D : D7}

theorem localExtension_isometryFixingFrames_mem_localUnitary {u u' : D.what₂.Word}
    (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS)
    (hB : Based Z FP (Tu D u) (Tu D u') F F') (h : GV D) (hh : h ∈ H0 F F') (p : PlF D)
    (g' : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hg : Ext p h g') : g' ∈ (FP p).UW0 := by
  obtain ⟨hiso, hF, hF'⟩ := hh
  obtain rfl := locEquiv_unique p h g' hg
  refine Subgroup.subset_closure ⟨locEquiv_unitary Z p h hiso, fun b => ⟨?_, ?_⟩⟩
  · rw [(hB p).1]
    show locEquiv p h (frFac Z.δ p b • baseChange₂ D p (frame F b)) = _
    rw [map_smul, locEquiv_ext p h, hF b]
  · rw [(hB p).2.1]
    show locEquiv p h (frFac Z.δ p b • baseChange₂ D p (frame F' b)) = _
    rw [map_smul, locEquiv_ext p h, hF' b]

theorem rat_ext_moves : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → (∀ (g : GV D) (p : PlF D), ∃! g', Ext p g g') ∧ (∀ h ∈ H0 F F', ∀ p g', Ext p h g' → g' ∈ (FP p).UW0) ∧ (∀ (g : GV D) p g' (Λ : LV D), Ext p g g' → lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap g Λ) = LocNG.img g' (lattice₂ D Z.M p Λ)) ∧ ∀ h ∈ H0 F F', ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∃ y', LocOver (Formalism.HermitianLatticesTheory.gmap h Λ) y' ∧ RMoves h y y' := by
  intro D X Y u u' F F' w _ _ Z FP hB hRel
  refine ⟨fun g p => ⟨locEquiv p g, locEquiv_ext p g, fun g' h => locEquiv_unique p g g' h⟩,
    fun h hh p g' hg => localExtension_isometryFixingFrames_mem_localUnitary F F' Z FP hB h hh p g' hg, ?_, ?_⟩
  · intro g p g' Λ hg
    obtain rfl := locEquiv_unique p g g' hg
    exact (locEquiv_img Z p g Λ).symm
  · intro h hh Λ y hov
    have hmem : ∀ p, locEquiv p h ∈ (FP p).UW0 := fun p =>
      localExtension_isometryFixingFrames_mem_localUnitary F F' Z FP hB h hh p _ (locEquiv_ext p h)
    have hact := fun p => GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
      (finrank_Vp_eq p) (hRel p)
    choose act hmv _ using hact
    let y' : Dat Z FP := fun p => (act p).smul ⟨locEquiv p h, hmem p⟩ (y p)
    have hmoves : ∀ p, LocNG.Datum.Moves (locEquiv p h) (y p) (y' p) := fun p =>
      ((hmv p) ⟨locEquiv p h, hmem p⟩ (y p) (y' p)).2 rfl
    refine ⟨y', ⟨isLattice_gmap' h Λ hov.1, fun p => ?_⟩, fun p => ⟨locEquiv p h, locEquiv_ext p h, hmoves p⟩⟩
    obtain ⟨τ, hτ, hL⟩ := hov.2 p
    have hm := (GlobalTheory.T.unitaryComplement_moves_local_terms_with_data (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
      (finrank_Vp_eq p) (hRel p) (locEquiv p h) (hmem p) (y p) (y' p) τ hτ (hmoves p)).1
    refine ⟨_, hm, ?_⟩
    show LocNG.img (locEquiv p h) τ.abelian₂ = _
    rw [hL, locEquiv_img Z p h Λ]

end GlobalTheory.RatLocMove
