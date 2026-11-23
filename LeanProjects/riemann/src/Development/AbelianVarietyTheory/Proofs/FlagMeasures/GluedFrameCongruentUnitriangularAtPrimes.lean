import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfA
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalUnitriangularOfLocalCongruence
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitAndSmulCompletedLatticeLeAtLevelPrimeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFlagFrameVectorMemRowLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAdaptedIsometryFrameUpperTriangularExpansioStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameScaleIsUnitAtPrimeOverLevelStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermFamiliesCongrModUnitriangularStatement
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Unfold.GluedCong

theorem bc_eq (D : D7) (Z : LocDat D) (p : PlF D) (v : (VS D).V) :
    (GlobalTheory.HL.placesOf Z).bc p ((VS D).frame.equivFun v) = baseChange₂ D p v := by
  funext i; rfl

theorem lat_eq (D : D7) (Z : LocDat D) (p : PlF D) (L : LV D) :
    (GlobalTheory.HL.placesOf Z).lat p (L.map (((VS D).frame.equivFun : (VS D).V →ₗ[D.host.E] (Fin (nV D) → D.host.E)).restrictScalars (𝓞 D.host.E))) = lattice₂ D Z.M p L := by
  unfold GlobalTheory.HL.Places.lat lattice₂
  congr 1
  ext z
  simp only [Set.mem_image, Submodule.map_coe, SetLike.mem_coe]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v, hv, (bc_eq D Z p v).symm⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨_, ⟨v, hv, rfl⟩, bc_eq D Z p v⟩

theorem smul_mem_gmap (D : D7) (γ : GV D) (I : Ideal (𝓞 D.host.E))
    (L : LV D) (v : (VS D).V) (s : 𝓞 D.host.E) (h : s • v ∈ I • L) :
    s • γ v ∈ I • Formalism.HermitianLatticesTheory.gmap γ L := by
  have hg1 : I • Formalism.HermitianLatticesTheory.gmap γ L = (I • L).map ((γ : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) := by
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [Submodule.map_smul'']
  rw [hg1]
  refine Submodule.mem_map.2 ⟨s • v, h, ?_⟩
  exact (γ : (VS D).V →ₗ[D.host.E] (VS D).V).map_smul_of_tower s v

set_option maxHeartbeats 1000000 in

theorem glued_loc_cong : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ g g', Adapt g (lf D (X.Fu u)) F → Adapt g' (lf D (X.Fu u')) F' → IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) → IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap g'⁻¹ Λ) → ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, frame (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ)) := by
  intro D X Y u u' F F' w hw hG Z FP hB hR Λ y hL g g' hA hA' hr hr' P hP
  obtain ⟨sg, hsp, hdict⟩ := GlobalTheory.T.split_and_smul_completedLattice_le_at_level_prime D Z P hP
  have hL0 := hL
  obtain ⟨hlat, hloc⟩ := hL
  obtain ⟨τ, hτ, hτL⟩ := hloc (below D P)
  obtain ⟨B, hB1, hB2, hBy⟩ := GlobalTheory.T.local_adaptedIsometry_frame_upperTriangular_expansion D (lf D (X.Fu u)) F g hA Z (below D P) (FP (below D P)).A.f (hB (below D P)).1
  obtain ⟨B', hB1', hB2', hBx⟩ := GlobalTheory.T.local_adaptedIsometry_frame_upperTriangular_expansion D (lf D (X.Fu u')) F' g' hA' Z (below D P) (FP (below D P)).B.f (hB (below D P)).2.1
  have hU := GlobalTheory.T.frameScale_isUnit_at_prime_over_level D (Tu D u) (Tu D u') (X.Fu u) F F' Z FP hB Λ y hL0 g hA hr P hP
  have hmemg : ∀ (γ : GV D) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T), IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap γ⁻¹ Λ) →
      ∀ a, γ (frame (lf D F0) a) ∈ Λ := by
    intro γ T F0 h a
    obtain ⟨v, hv, hve⟩ := Submodule.mem_map.1 (GlobalTheory.T.fixedFlag_frameVector_mem_rowLattice D F0 _ h a)
    have e : γ (frame (lf D F0) a) = v := by
      rw [← hve]
      show γ (γ⁻¹ v) = v
      exact γ.apply_symm_apply v
    rw [e]; exact hv
  have hyL : ∀ a, baseChange₂ D (below D P) (g (frame (lf D (X.Fu u)) a)) ∈ τ.abelian₂ := fun a => by
    rw [hτL]; exact Submodule.subset_span ⟨_, hmemg g (X.Fu u) hr a, rfl⟩
  have hxL : ∀ a, baseChange₂ D (below D P) (g' (frame (lf D (X.Fu u')) a)) ∈ τ.abelian₂ := fun a => by
    rw [hτL]; exact Submodule.subset_span ⟨_, hmemg g' (X.Fu u') hr' a, rfl⟩
  obtain ⟨ξp, hξO, hξ1, hξ2, hξc⟩ := GlobalTheory.T.term_families_congr_mod_unitriangular (locH Z (below D P)) (FP (below D P)) (y (below D P)) τ sg hsp hτ
    (fun b => baseChange₂ D (below D P) (g (frame (lf D (X.Fu u)) b))) (fun b => baseChange₂ D (below D P) (g' (frame (lf D (X.Fu u')) b))) B B' hB1 hB1'
    (fun a => by rw [hB2, hB2'])
    (fun a => by
      rw [hB2]
      exact ⟨(hU a).2, frFac Z.δ (below D P) a, (hU a).1, Ring.mul_inverse_cancel _ (Formalism.L2.SG.Pf.ScalarFramePf.isUnit_frFac Z (below D P) a)⟩)
    hBy hBx hyL hxL
  have hfg : (Λ.map (((VS D).frame.equivFun : (VS D).V →ₗ[D.host.E] (Fin (nV D) → D.host.E)).restrictScalars (𝓞 D.host.E))).FG := hlat.fg.map _
  have hpos : 0 < gS D := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  obtain ⟨ξ, hu1, hu2, hPP⟩ := GlobalTheory.HL.LocCongApprox.loc_cong_approx (GlobalTheory.HL.placesOf Z) (nV D) D.R.rS _ hfg
    (gS D) hpos (below D P) (fun a => (VS D).frame.equivFun (g (frame (lf D (X.Fu u)) a)))
    (fun b => (VS D).frame.equivFun (g' (frame (lf D (X.Fu u')) b))) ξp hξO hξ1 hξ2
    (fun a => by
      rw [lat_eq, bc_eq, ← hτL]
      exact hyL a)
    (fun b => by
      rw [← Submodule.map_smul'', lat_eq]
      have h1 := hdict Λ _ (hτL ▸ hξc b)
      simp only [bc_eq]
      exact h1)
  refine ⟨ξ, hu1, hu2, fun b => ?_⟩
  have h := hPP P rfl b
  obtain ⟨v, hv⟩ : ∃ v, v = g' (frame (lf D (X.Fu u')) b) - ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) • g (frame (lf D (X.Fu u)) a) := ⟨_, rfl⟩
  have hφv : (VS D).frame.equivFun (g' (frame (lf D (X.Fu u')) b)) - ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) • (VS D).frame.equivFun (g (frame (lf D (X.Fu u)) a)) = (VS D).frame.equivFun v := by
    rw [hv, map_sub, map_sum]
    simp only [map_smul]
  rw [hφv] at h
  obtain ⟨s, hs, hsv⟩ := h
  rw [← Submodule.map_smul''] at hsv
  obtain ⟨z, hz, hzv⟩ := Submodule.mem_map.1 hsv
  have hzs : z = s • v := by
    apply ((VS D).frame.equivFun).injective
    have e1 : (VS D).frame.equivFun z = s • (VS D).frame.equivFun v := hzv
    rw [e1]
    exact (((VS D).frame.equivFun : (VS D).V →ₗ[D.host.E] (Fin (nV D) → D.host.E)).map_smul_of_tower s v).symm
  have hiso : g⁻¹ * g' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (inv_mem hA.1) hA'.1
  have hfr : frame (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) b = (g⁻¹ * g') (frame (lf D (X.Fu u')) b) := by
    unfold mapLF
    rw [dif_pos hiso]
    simp only [frame, Formalism.MainNotions.S.FlagG.fvec, mapFlag]
    exact (congrFun (Fin.comp_snoc (⇑(g⁻¹ * g')) _ _) b).symm
  have htarget : frame (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b = g⁻¹ v := by
    rw [hfr, hv, map_sub, map_sum, LinearEquiv.mul_apply]
    unfold frameAct
    refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun a _ => ?_)
    exact (((g⁻¹ : GV D).map_smul _ _).trans (congrArg _ (g.symm_apply_apply _))).symm
  have hsv' : s • v ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ := by
    rw [← hzs]; exact hz
  refine ⟨s, hs, ?_⟩
  rw [htarget]
  exact smul_mem_gmap D g⁻¹ (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)}) Λ v s hsv'

end GlobalTheory.Unfold.GluedCong
