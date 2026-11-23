import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitriangularFrameChangeLocalScalings
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnsignedLocalTermRowLatticeIsTermStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDatumOfTwoCongruentFramesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameWitnessIntegralChangeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentGroupsLatticesGlobalCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTermUnitaryMoveLocalTermStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryExtensionRationalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairGramInvariantUnchangedIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdmissibilityWitnessesCongrModThetaLocalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScaledUnitriangularChangeEqLocalImageStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.MovedTermLoc

theorem uni_mul {R : Type} [CommRing R] {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) (hA : Uni A) (hB : Uni B) :
    Uni (A * B) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [hA.1 a c h, zero_mul]
    · rw [hB.1 c b (lt_of_lt_of_le hab h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA.2 a, hB.2 a, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hA.1 a c h, zero_mul]
      · rw [hB.1 c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

theorem uni_map {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (A : Matrix (Fin n) (Fin n) R)
    (hA : Uni A) : Uni (A.map f) :=
  ⟨fun a b h => by simp [Matrix.map_apply, hA.1 a b h], fun a => by simp [Matrix.map_apply, hA.2 a]⟩

theorem map_inv_of_det {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S)
    (A : Matrix (Fin n) (Fin n) R) (hA : IsUnit A.det) : (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  refine Matrix.inv_eq_right_inv ?_
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, Matrix.map_one _ f.map_zero f.map_one]

theorem chg_scaled {D : D7} (Z : LocDat D) (p : PlF D) (f g : Fin (D.R.rS + 1) → (VS D).V)
    (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E) (hg : Chg f A g) :
    Chg (scaled Z p f) (fun a b => Ring.inverse (frFac Z.δ p a) * frFac Z.δ p b * (D.s.atP p).ιE (A a b))
      (scaled Z p g) := by
  intro b
  simp only [scaled]
  rw [hg b, Formalism.L2.SG.Pf.BBTie.bt_bc_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, smul_smul]
  congr 1
  have h := Ring.inverse_mul_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit Z p a)
  linear_combination (-(frFac Z.δ p b * (D.s.atP p).ιE (A a b))) * h

set_option maxHeartbeats 1600000 in

theorem main : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (p : PlF D) (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)), AdmWit t₀.lam (gS D) (lf D (X.Fu u)) t₀.frame ξ → ∀ (N N' : G.GLV), (∀ b, N (G.f b) = ∑ a, U a b • G.f a) → (∀ b, N' (G.f' b) = ∑ a, (U' * (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))⁻¹) a b • G.f' a) → ∀ (m m' : (G.S p).GLV), (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N m → (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N' m' → ∃ (t : Loc.Term (Vp D p) (Y.M p) D.R.rS) (d : LocNG.Datum (FP p)), LocNG.IsTermOver (FP p) d t ∧ (c.c p).lat t.abelian₂ = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam) ∧ (∀ b, (c.c p).e (t.f b) = m ((G.S p).f b)) ∧ ∀ b, (c.c p).e (t.f' b) = m' ((G.S p).f' b) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv p ξ hξ N N' hN hN' m m' hm hm'
  have hR : IsRowLat D (X.Fu u) t₀.lam := (Y.rowsOK u).1 t₀.lam t₀.mem
  have hPD : Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u' t₀.frame := t₀.rep.2.2.2.2
  have hGt : Gval (lf D (X.Fu u)) t₀.frame ≠ 0 := fun h0 => hG ((GlobalTheory.T.frame_pair_gram_invariant_unchanged_isometry D _ _ _ _ ρ U U' hMv).symm.trans h0)
  obtain ⟨g, hgE, hgU⟩ := GlobalTheory.T.exists_unitary_extension_rational_isometry D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p ρ hMv.1
  obtain ⟨hT0, -⟩ := GlobalTheory.T.unsignedLocalTerm_row_lattice_isTerm D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t₀.lam hR t₀.frame hPD hGt p
  set ξ0 := admXi D t₀.lam (lf D (X.Fu u)) t₀.frame with hξ0
  set t0 := locU (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p t₀.lam (lf D (X.Fu u)) t₀.frame (Tu D u) (Tu D u') with ht0
  have hTg := GlobalTheory.T.isTerm_unitary_move_localTerm (Y.M p) (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS g t0 hgU hT0

  have hUu : Uni U := ⟨fun a b h => (hMv.2.1 a b).1 h, fun a => (hMv.2.1 a a).2 rfl⟩
  have hU'u : Uni U' := ⟨fun a b h => (hMv.2.2.1 a b).1 h, fun a => (hMv.2.2.1 a a).2 rfl⟩
  have hξ0u : Uni ξ0 := admissibility_witness_unitriangular t₀.lam (lf D (X.Fu u)) t₀.frame
  have hξ0i : Uni ξ0⁻¹ := inv_unitri _ hξ0u.1 hξ0u.2
  have hξu : Uni ξ := ⟨hξ.1, hξ.2.1⟩
  have hξi : Uni ξ⁻¹ := inv_unitri _ hξu.1 hξu.2
  have hξ0w : AdmWit t₀.lam (gS D) (lf D (X.Fu u)) t₀.frame ξ0 := by
    rw [hξ0]; unfold admXi; rw [dif_pos hPD.2.1]; exact hPD.2.1.choose_spec
  set alg := algebraMap (𝓞 D.host.E) D.host.E with halg
  set B0 := U' * (ξ0⁻¹).map alg with hB0
  set B1 := U' * (ξ.map alg)⁻¹ with hB1
  set C := (ξ0 * ξ⁻¹).map alg with hC
  have hB0u : Uni B0 := uni_mul _ _ hU'u (uni_map _ _ hξ0i)
  have hCu : Uni C := uni_map _ _ (uni_mul _ _ hξ0u hξi)
  have hBC : B0 * C = B1 := by
    rw [hB0, hB1, hC, Matrix.map_mul, ← map_inv_of_det alg ξ (Formalism.L2.SG.Pf.BBTie.bt_unitri_det _ hξu.1 hξu.2),
      Matrix.mul_assoc, ← Matrix.mul_assoc ((ξ0⁻¹).map alg), ← Matrix.map_mul,
      Matrix.nonsing_inv_mul _ (Formalism.L2.SG.Pf.BBTie.bt_unitri_det _ hξ0u.1 hξ0u.2),
      Matrix.map_one _ alg.map_zero alg.map_one, Matrix.one_mul]

  have hf : ∀ b, (move g t0).f b = scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (fun b => ∑ a, U a b • frame F00 a) b := by
    intro b
    show g (frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p b • baseChange₂ D p (frame (lf D (X.Fu u)) b)) = frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p b • baseChange₂ D p _
    rw [map_smul, hgE]
    exact congrArg (fun x => frFac _ p b • baseChange₂ D p x) (hMv.2.2.2.1 b)
  have hf' : ∀ b, (move g t0).f' b = scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (fun b => ∑ a, B0 a b • frame F'0 a) b := by
    intro b
    show g (frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p b • baseChange₂ D p (frameAct (frame t₀.frame) ξ0⁻¹ b)) = frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p b • baseChange₂ D p _
    rw [map_smul, hgE]
    congr 2
    simp only [frameAct, map_sum, map_smul, hMv.2.2.2.2, Finset.smul_sum, smul_smul, hB0, Matrix.mul_apply,
      Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.map_apply, mul_comm]
  have hTri1 : Tri (D.s.atP p).Ep (FP p).A.f (move g t0).f := by
    obtain ⟨Ap, hAp, -⟩ := tri_scaled D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) (frame F00) (fun b => ∑ a, U a b • frame F00 a) U hUu (fun b => rfl)
    rw [(hAt p).1.1]
    exact ⟨Ap p, (hAp p).1, fun b => by rw [hf b]; exact (hAp p).2 b⟩
  have hTri2 : Tri (D.s.atP p).Ep (FP p).B.f (move g t0).f' := by
    obtain ⟨Ap, hAp, -⟩ := tri_scaled D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) (frame F'0) (fun b => ∑ a, B0 a b • frame F'0 a) B0 hB0u (fun b => rfl)
    rw [(hAt p).1.2.1]
    exact ⟨Ap p, (hAp p).1, fun b => by rw [hf' b]; exact (hAp p).2 b⟩
  obtain ⟨d, hd⟩ := GlobalTheory.T.exists_datum_of_two_congruent_frames (Y.M p) (Y.agree p).1 (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS (FP p) (move g t0) hTg
    (hAt p).1.2.2.1.symm (hAt p).1.2.2.2.symm hTri1 hTri2

  set A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
    fun a b => Ring.inverse (frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p a) * frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p b * (D.s.atP p).ιE (C a b) with hA'
  set tf' := scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (fun b => ∑ a, B1 a b • frame F'0 a) with htf'
  have hChg1 : Chg (move g t0).f (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) (move g t0).f := by
    intro b
    simp [Matrix.one_apply]
  have hChg2 : Chg (move g t0).f' A' tf' := by
    have hc : Chg (fun b => ∑ a, B0 a b • frame F'0 a) C (fun b => ∑ a, B1 a b • frame F'0 a) := by
      intro b
      rw [← hBC]
      simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      rw [mul_comm]
    have h := chg_scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p _ _ C hc
    intro b
    refine (h b).trans ?_
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hf' a]
  have hfin : Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
    rw [finrank_Vp]
    obtain ⟨j, hj⟩ := D.R.m_even
    have := D.R.two_le_m
    simp only [Ranks.r, Ranks.rS]
    omega
  have hA'u : Uni A' := by
    refine ⟨fun a b h => ?_, fun a => ?_⟩
    · simp [hA', hCu.1 a b h]
    · show Ring.inverse (frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p a) * frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p a * (D.s.atP p).ιE (C a a) = 1
      rw [hCu.2 a, map_one, mul_one, Ring.inverse_mul_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p a)]
  have hcong := GlobalTheory.T.admissibility_witnesses_congr_mod_theta_local D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) u u' (X.Fu u) t₀.lam t₀.frame hR hPD ξ0 ξ hξ0w hξ p
  have hint : ∀ a b, (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b ∈ (Y.M p).L.O ∧
      A' a b ∈ (Y.M p).L.O ∧ (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b - A' a b ∈
        Submodule.span (Y.M p).L.O {algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Formalism.MainNotions.S.LocNG.theta (Y.M p))} := by
    intro a b
    rcases lt_or_ge b a with h | h
    · have e0 : A' a b = 0 := by simp [hA', hCu.1 a b h]
      rw [e0, Matrix.one_apply_ne (ne_of_lt h).symm, sub_zero]
      exact ⟨Subring.zero_mem _, Subring.zero_mem _, Submodule.zero_mem _⟩
    · obtain ⟨k, hkO, hkb⟩ := Formalism.L2.SG.Pf.BBTie.bt_frFac_step (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (Formalism.L2.SG.Pf.locDiffC_holds D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) a b h
      have e1 : A' a b = k * (D.s.atP p).ιE (C a b) := by
        show Ring.inverse (frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p a) * frFac (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D).δ p b * (D.s.atP p).ιE (C a b) = _
        rw [hkb, mul_comm k, ← mul_assoc, Ring.inverse_mul_cancel _ (Formalism.L2.SG.Pf.BBTie.bt_frFac_unit (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p a), one_mul]
      have hCO : (D.s.atP p).ιE (C a b) ∈ (Y.M p).L.O := Formalism.L2.SG.Pf.BBTie.bt_iota_int (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p ((ξ0 * ξ⁻¹) a b)
      have hAO : A' a b ∈ (Y.M p).L.O := by rw [e1]; exact Subring.mul_mem _ hkO hCO
      refine ⟨?_, hAO, ?_⟩
      · by_cases hab : a = b
        · subst hab; rw [Matrix.one_apply_eq]; exact Subring.one_mem _
        · rw [Matrix.one_apply_ne hab]; exact Subring.zero_mem _
      · rcases eq_or_lt_of_le h with hab | hab
        · subst hab
          rw [hA'u.2 a, Matrix.one_apply_eq, sub_self]; exact Submodule.zero_mem _
        · have hc := hcong a b
          rw [Matrix.one_apply_ne (ne_of_lt hab), sub_zero] at hc
          rw [Matrix.one_apply_ne (ne_of_lt hab), zero_sub, e1, ← neg_mul]
          have := Submodule.smul_mem _ (⟨-k, Subring.neg_mem _ hkO⟩ : (Y.M p).L.O) hc
          exact this
  have hT := GlobalTheory.T.hermitian_frame_witness_integral_change (Y.M p) (Y.agree p).1 (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS D.R.k (FP p) hfin (hAt p).2 d (move g t0) hd
    1 A' (move g t0).f tf' (⟨fun a b h => Matrix.one_apply_ne (ne_of_lt h).symm, fun a => Matrix.one_apply_eq a⟩)
    hA'u hint hChg1 hChg2
  have hlat := (GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv).2.2.2.2.1 ρ hMv.1 p g
    t₀.lam hgE
  have hfc := GlobalTheory.T.scaled_unitriangular_change_eq_local_image D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G c p N m hm U
  have hfc' := GlobalTheory.T.scaled_unitriangular_change_eq_local_image D (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G c p N' m' hm' B1
  refine ⟨⟨(move g t0).abelian₂, (move g t0).f, tf', (move g t0).T, (move g t0).T'⟩, d, hT, hlat.symm, fun b => ?_,
    fun b => ?_⟩
  · show (c.c p).e ((move g t0).f b) = _
    rw [hf b]; exact hfc.1 hN b
  · exact hfc'.2 hN' b

end GlobalTheory.HL.MovedTermLoc
