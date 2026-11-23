import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OverOfIsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UnitriangularLatticeStabiliserSubFrameAutomorphi
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalAutomorphismLocalExtensionMovesLatticesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAtBasePointOfFramesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnsignedLocalTermRowLatticeIsTerm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataGlobalTermIndependentOfRepresentativeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDatumOfTwoCongruentFramesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermDatumOrbitUniqueStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTermLocalTermMoveOfIsometryStatement

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.TermLocal

variable {D : D7}

section Tri

theorem tri_map {K W W' : Type} [CommSemiring K] [AddCommMonoid W] [Module K W] [AddCommMonoid W'] [Module K W']
    {n : ℕ} (φ : W →ₗ[K] W') {f g : Fin n → W} (h : GlobalTheory.LocOver.Tri K f g) :
    GlobalTheory.LocOver.Tri K (fun a => φ (f a)) (fun a => φ (g a)) := by
  obtain ⟨A, hA, hc⟩ := h
  refine ⟨A, hA, fun b => ?_⟩
  simp only [hc b, map_sum, map_smul]

theorem tri_trans {K W : Type} [CommSemiring K] [AddCommMonoid W] [Module K W] {n : ℕ} {f g h : Fin n → W}
    (h1 : GlobalTheory.LocOver.Tri K f g) (h2 : GlobalTheory.LocOver.Tri K g h) : GlobalTheory.LocOver.Tri K f h := by
  obtain ⟨A, ⟨hA1, hA2⟩, hcA⟩ := h1
  obtain ⟨B, ⟨hB1, hB2⟩, hcB⟩ := h2
  refine ⟨A * B, ⟨fun a c hca => ?_, fun a => ?_⟩, fun c => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    rcases lt_or_ge b a with hb | hb
    · rw [hA1 a b hb, zero_mul]
    · rw [hB1 b c (lt_of_lt_of_le hca hb), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA2, hB2, one_mul]
    · intro b _ hb
      rcases lt_or_gt_of_ne hb with hb | hb
      · rw [hA1 a b hb, zero_mul]
      · rw [hB1 b a hb, mul_zero]
    · intro hn; exact absurd (Finset.mem_univ a) hn
  · show h c = ∑ a, (A * B) a c • f a
    rw [hcB c]
    simp only [show ∀ b, g b = ∑ a, A a b • f a from hcA, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm]

end Tri

theorem isTerm_move {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Formalism.MainNotions.S.Loc.HermSp M V) {r : ℕ} (g : V ≃ₗ[E] V) (t : Formalism.MainNotions.S.Loc.Term V M r)
    (hg : Formalism.MainNotions.S.LocNG.IsUnitary H g) (ht : H.IsTerm t) : H.IsTerm (GlobalTheory.LocOver.move g t) :=
  GlobalTheory.T.isTerm_localTermMove_of_isometry H g t hg ht

theorem tri_adapt_loc (Z : LocDat D) (p : PlF D) (g : GV D) {T : D.host.E} (F₁ F₂ : LFlag (VS D) D.R.rS T)
    (g' : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) (hg : Adapt g F₁ F₂) (he : Ext p g g') :
    GlobalTheory.LocOver.Tri (D.s.atP p).Ep (GlobalTheory.LocOver.scaled Z p (frame F₂))
      (fun a => g' (GlobalTheory.LocOver.scaled Z p (frame F₁) a)) := by
  obtain ⟨A, ⟨hA1, hA2⟩, hc⟩ := GlobalTheory.Unfold.BasePt.tri_of_adapt g F₁ F₂ hg.1 hg.2
  have hu := fun a => Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a
  refine ⟨fun a b => frFac Z.δ p b * (D.s.atP p).ιE (A a b) * Ring.inverse (frFac Z.δ p a),
    ⟨fun a b hba => ?_, fun a => ?_⟩, fun b => ?_⟩
  · simp [hA1 a b hba]
  · show frFac Z.δ p a * (D.s.atP p).ιE (A a a) * Ring.inverse (frFac Z.δ p a) = 1
    rw [hA2, map_one, mul_one, Ring.mul_inverse_cancel _ (hu a)]
  · have e := hc b
    rw [Formalism.L2.SG.Saturated.frame_mapL] at e
    simp only [GlobalTheory.LocOver.scaled]
    rw [map_smul, he, e, map_sum]
    simp only [baseChange_smul₂, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [mul_assoc (frFac Z.δ p b * _), Ring.inverse_mul_cancel _ (hu a), mul_one]

theorem isLattice_gmap (g : GV D) (A : LV D) (hA : Submodule.IsLattice D.host.E A) :
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

theorem local_data_of_term : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (t : TauC Y u u') (Λ : LV D), TG F F' t Λ → ∃ y : Dat Z FP, LocOver Λ y ∧ ∀ p d, GlobalTheory.LocOver.Over (FP p) d (GlobalTheory.LocOver.locU Z p t.toTerm.lam (lf D (X.Fu u)) (Quot.out t.toTerm.cls).1 (Tu D u) (Tu D u')) ↔ LocNG.Datum.Rel d (y p) := by
  intro D X Y u u' F F' w hZ hG Z FP hB hRel t Λ hTG
  obtain ⟨hExt, -, hlat, -⟩ := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hZ hG Z FP hB hRel
  have hGt : t.G ≠ 0 := (GlobalTheory.T.term_at_base_point_of_frames D X Y u u' F F' w hZ hG t Λ hTG).1
  obtain ⟨g, hgF, hgF', hΛ⟩ := hTG
  have hrow : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 t.lam t.mem
  have hPD : Formalism.L2.SG.TermDef.PD D t.lam (lf D (X.Fu u)) u' t.frame := t.rep.2.2.2.2
  have hGv : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by rwa [Formalism.L2.SG.Pf.SatGram.gterm_G Y t] at hGt
  choose gp hgp using fun p => (hExt g p).exists
  have hu : ∀ p, LocNG.IsUnitary (locH Z p) (gp p) := fun p => GlobalTheory.Unfold.Model.ext_unitary hgF.1 (hgp p)
  have hτ := fun p => GlobalTheory.LocOver.locU_isTerm D Z u u' (X.Fu u) t.lam hrow t.frame hPD hGv p
  have hex : ∀ p, ∃ d, LocNG.IsTermOver (FP p) d
      (GlobalTheory.LocOver.move (gp p) (GlobalTheory.LocOver.locU Z p t.lam (lf D (X.Fu u)) t.frame (Tu D u) (Tu D u'))) := by
    intro p
    refine GlobalTheory.T.exists_datum_of_two_congruent_frames (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS (FP p) _
      (isTerm_move (locH Z p) (gp p) _ (hu p) (hτ p).1) (hB p).2.2.1.symm (hB p).2.2.2.symm ?_ ?_
    · rw [(hB p).1]
      exact tri_adapt_loc Z p g _ _ (gp p) hgF (hgp p)
    · rw [(hB p).2.1]
      exact tri_trans (tri_adapt_loc Z p g _ _ (gp p) hgF' (hgp p))
        (tri_map (gp p).toLinearMap (hτ p).2)
  choose y hy using hex
  refine ⟨y, ⟨?_, fun p => ⟨_, hy p, ?_⟩⟩, fun p d => ?_⟩
  · rw [hΛ]; exact isLattice_gmap g _ hrow.1.1
  · show LocNG.img (gp p) (lattice₂ D Z.M p t.lam) = _
    rw [hΛ, hlat g p (gp p) t.lam (hgp p)]
  · have hDC : Formalism.L2.SG.TermDef.DCRel t.lam (lf D (X.Fu u)) t.frame (Quot.out t.toTerm.cls).1 :=
      (Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t.lam hrow ⟨t.frame, hPD⟩ (Quot.out t.toTerm.cls)).1
        (Quot.out_eq t.toTerm.cls).symm
    refine (GlobalTheory.T.localData_globalTerm_independent_of_representative D Z u u' (X.Fu u) t.lam hrow t.frame (Quot.out t.toTerm.cls).1 hPD
      (Quot.out t.toTerm.cls).2 hGv hDC p (FP p) (hRel p) d).symm.trans ?_
    refine (GlobalTheory.LocOver.Check.over_move_iff (FP p) d _ (gp p) (hu p)).symm.trans ?_
    constructor
    · intro h
      exact GlobalTheory.T.term_datum_orbit_unique (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (finrank_Vp_eq p) (hRel p) d (y p) _ h
        (GlobalTheory.LocOver.Check.over_of_isTermOver _ _ _ (hy p))
    · intro h
      refine ⟨1, fun _ _ => rfl, y p, h, ?_⟩
      rw [GlobalTheory.LocOver.Check.move_one]
      exact hy p

end GlobalTheory.Unfold.TermLocal
