import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedUnimodularLatticeIffLocalCompletionsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericLocalTermsSelfDualLatticesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianOrbitUniqueLatticeIntegralFramesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesHermitianTermsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitriangularFrameChangeLocalScalingsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOntoStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDatumOfTermReadOnLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeLocalGlobalPrinciple
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLattices
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearIndependentChangedRationalFramesOfUnitrianStatement

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GlueDat

variable {D : D7}

theorem finrank_loc (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  have h3 := D.R.m_add_three_le_k
  obtain ⟨c, hc⟩ := h1
  simp only [Ranks.r, Ranks.rS]
  omega

theorem localLattice_fg (Z : LocDat D) (Λ : LV D) (h : Submodule.IsLattice D.host.E Λ) (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG := by
  have := (GlobalTheory.HL.PlacesRec.lattice_local (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL Λ)
    (LatLoc.isLattice_map _ _ h)).2.1 p
  rw [LatLoc.localLattice_eq]
  exact this.1

theorem orbit (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) {Tn T'n : ℕ}
    (F G : LFlag (VS D) D.R.rS (Tn : D.host.E)) (F' G' : LFlag (VS D) D.R.rS (T'n : D.host.E))
    (hB : Based Z FP Tn T'n F F') (hR : ∀ p, (FP p).RelG (LocNG.theta (Z.M p)))
    (hG : Tri D.host.E (frame F) (frame G)) (hG' : Tri D.host.E (frame F') (frame G')) (p : PlF D) :
    (∃ n ∈ (FP p).A.N, scaled Z p (frame G) = fun b => n ((FP p).A.f b)) ∧
    (∃ n ∈ (FP p).B.N, scaled Z p (frame G') = fun b => n ((FP p).B.f b)) := by
  obtain ⟨A, hA, hAc⟩ := hG
  obtain ⟨A', hA', hAc'⟩ := hG'
  obtain ⟨Ap, hAp, -⟩ := GlobalTheory.T.rational_unitriangular_frame_change_local_scalings D Z _ _ A hA hAc
  obtain ⟨Ap', hAp', -⟩ := GlobalTheory.T.rational_unitriangular_frame_change_local_scalings D Z _ _ A' hA' hAc'
  have hN := (hR p).2.2.2.2.2.2
  have hfA : (FP p).A.f = scaled Z p (frame F) := (hB p).1
  have hfB : (FP p).B.f = scaled Z p (frame F') := (hB p).2.1
  refine ⟨?_, ?_⟩
  · exact (GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS (FP p).A hN.2.1).2.2 (scaled Z p (frame G))
      (by rw [hfA]; exact ⟨Ap p, (hAp p).1, (hAp p).2⟩)
  · exact (GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS (FP p).B hN.2.2.2.1).2.2 (scaled Z p (frame G'))
      (by rw [hfB]; exact ⟨Ap' p, (hAp' p).1, (hAp' p).2⟩)

theorem mem_iff_of_img {α : Type*} {S S' : Set α} {f : α → α} (hf : Function.Injective f) (hS : f '' S = S')
    {a b : α} (hb : b = f a) : a ∈ S ↔ b ∈ S' := by
  subst hb; rw [← hS]; exact (hf.mem_set_image).symm

end GlobalTheory.GlueDat

open GlobalTheory.GlueDat in

theorem GlobalTheory.GlueDat.glued_data : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → ∀ Λ : LV D, (Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') ↔ ∃ y : Dat Z FP, Λ ∈ globSet G G' y) ∧ (∀ y y' : Dat Z FP, Λ ∈ globSet G G' y → Λ ∈ globSet G G' y' → y = y') ∧ (∀ y : Dat Z FP, Λ ∈ globSet G G' y → (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (y p)) ∧ {p | y p ≠ d0 p}.Finite) ∧ ∀ (y y' : Dat Z FP), ∀ h ∈ H0 F F', RMoves h y y' → (Λ ∈ globSet G G' y ↔ Formalism.HermitianLatticesTheory.gmap h Λ ∈ globSet G G' y') := by
  intro D Z FP u u' F G F' G' P d0 hk hB hS Λ
  have hOK : ∀ p, (Z.M p).OK := fun p => (Z.agree p).1
  have hR := hB.2.1
  have hO := fun p => orbit Z FP F G F' G' hB.1 hR hS.1 hS.2.1 p
  have hLM := fun p (L : Submodule (Z.M p).L.O (Vp D p)) =>
    GlobalTheory.T.generic_local_terms_selfDual_lattices (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_loc p) (hR p)
      (scaled Z p (frame G)) (scaled Z p (frame G')) (hO p).1 (hO p).2 L
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [GlobalTheory.T.glued_unimodular_lattice_iff_local_completions D Z FP u u' G G' (GlobalTheory.T.linearIndependent_changedRationalFrames_of_unitriangular D Z FP _ _ F G F' G' hB.1 hR hS.1 hS.2.1) Λ]
    constructor
    · rintro ⟨hL, hp⟩
      have : ∀ p, ∃ d, lattice₂ D Z.M p Λ ∈ locSet G G' p d := fun p =>
        (hLM p _).1.1 ⟨(hp p).1, localLattice_fg Z Λ hL p, (hp p).2.1, (hp p).2.2⟩
      choose y hy using this
      exact ⟨y, hL, hy⟩
    · rintro ⟨y, hL, hy⟩
      refine ⟨hL, fun p => ?_⟩
      obtain ⟨h1, -, h3, h4⟩ := (hLM p _).1.2 ⟨y p, hy p⟩
      exact ⟨h1, h3, h4⟩
  · intro y y' h h'
    funext p
    exact (hLM p _).2 (y p) (y' p) (h.2 p).1 (h'.2 p).1
  · intro y hy
    refine ⟨fun p hp => ?_, ?_⟩
    · obtain ⟨A, A', hA, hA', hint, hc, hc'⟩ := hS.2.2.2.2 p hp
      have := GlobalTheory.T.hermitian_orbit_unique_lattice_integral_frames (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) hk (finrank_loc p) (hR p)
        (hB.2.2.1 p hp) A A' (fun a b hab => ⟨hA.1 a b hab, hA'.1 a b hab⟩) (fun a => ⟨hA.2 a, hA'.2 a⟩) hint
        (scaled Z p (frame G)) (scaled Z p (frame G'))
        (fun j => by rw [(hB.1 p).1]; exact hc j) (fun j => by rw [(hB.1 p).2.1]; exact hc' j)
        (d0 p) (hB.2.2.2.1 p) (y p)
      exact this.2 ⟨_, (hy.2 p).1⟩
    · obtain ⟨Λ₀, hΛ₀, hΛ₀p⟩ := hB.2.2.2.2
      refine (((LatLoc.lattices_local_global D Z).1 Λ Λ₀ hy.1 hΛ₀).1.union P.finite_toSet).subset ?_
      intro p hp
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Finset.mem_coe] at hc
      apply hp
      exact (GlobalTheory.T.hermitianDatum_of_term_read_on_lattice (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_loc p) (hR p)).2
        (y p) (d0 p) _ _ (hy.2 p).1 (hΛ₀p p hc.2) (by dsimp only [tm]; rw [hc.1]) (by dsimp only [tm]; rw [hc.1])
        (fun g _ => by dsimp only [tm]; rw [hc.1])
  · intro y y' h hh hmv
    have hloc : ∀ p, ∃ g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p, g ∈ (FP p).UW0 ∧
        LocNG.Datum.Moves g (y p) (y' p) ∧
        lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap h Λ) = LocNG.img g (lattice₂ D Z.M p Λ) := by
      intro p
      obtain ⟨g, hext, hU, huniq, himg, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p h hh.1
      obtain ⟨g', hext', hm⟩ := hmv p
      obtain rfl : g' = g := huniq g' hext'
      refine ⟨g', Subgroup.subset_closure ⟨hU, fun b => ⟨?_, ?_⟩⟩, hm, (himg Λ).symm⟩
      · rw [(hB.1 p).1]
        show g' (frFac Z.δ p b • baseChange₂ D p (frame F b)) = _
        rw [map_smul, hext', hh.2.1 b]
      · rw [(hB.1 p).2.1]
        show g' (frFac Z.δ p b • baseChange₂ D p (frame F' b)) = _
        rw [map_smul, hext', hh.2.2 b]
    choose g hgU hgm hgimg using hloc
    have hset := fun p => (GlobalTheory.T.unitaryComplement_moves_hermitianTerms (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_loc p) (hR p)
      (scaled Z p (frame G)) (scaled Z p (frame G')) (hO p).1 (hO p).2 (g p) (hgU p) (y p) (y' p) (hgm p)).2
    have hlat : Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap h Λ) ↔ Submodule.IsLattice D.host.E Λ := by
      constructor
      · intro hl
        have e : Λ = Formalism.HermitianLatticesTheory.gmap h.symm (Formalism.HermitianLatticesTheory.gmap h Λ) := by
          ext x; simp [Formalism.HermitianLatticesTheory.gmap]
        rw [e]; exact LatLoc.isLattice_map _ _ hl
      · exact LatLoc.isLattice_map _ _
    show (Submodule.IsLattice D.host.E Λ ∧ ∀ p, lattice₂ D Z.M p Λ ∈ locSet G G' p (y p)) ↔
      (Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap h Λ) ∧ ∀ p, lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap h Λ) ∈ locSet G G' p (y' p))
    rw [hlat]
    refine and_congr_right fun _ => forall_congr' fun p => ?_
    have e := hgimg p
    have key : ∀ L, L ∈ LocNG.img (g p) '' locSet G G' p (y p) ↔ L ∈ locSet G G' p (y' p) :=
      fun L => Set.ext_iff.mp (hset p) L
    have hinj : Function.Injective (LocNG.img (M := Z.M p) (g p)) := fun L₁ L₂ e =>
      Submodule.map_injective_of_injective (f := ((g p : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p).restrictScalars (Z.M p).L.O))
        (g p).injective e
    exact mem_iff_of_img hinj (Set.ext key) e
