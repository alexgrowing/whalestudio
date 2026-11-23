import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralRowFrameMapIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlueFrameCongruencesUnitriangularIntegralStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedFrameCongruentUnitriangularAtPrimesStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.AdmGlued

theorem gS_pos (D : D7) : 0 < gS D :=
  Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos

theorem mem_localization_of_mem' {D : D7} (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) {L : LV D} {x : (VS D).V}
    (hx : x ∈ L) : x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L) :=
  ⟨1, P.asIdeal.primeCompl.one_mem, by simpa using hx⟩

theorem localization_mono {D : D7} (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) {L M : LV D} (h : L ≤ M) :
    (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal L) ≤ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M) := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, h hx⟩

theorem frame_mem_locP {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LV D) (h : IsRowLat D F0 Λ)
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (a : Fin (D.R.rS + 1)) : frame (lf D F0) a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
  obtain ⟨-, ⟨-, -, hlift, hconv⟩, -⟩ := h
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have hz : (lf D F0).fl.z ∈ Λ := hlift.1
    have e : frame (lf D F0) (Fin.last D.R.rS) = (lf D F0).fl.z := by simp [frame, FlagG.fvec]
    rw [e]
    exact mem_localization_of_mem' P hz
  · obtain ⟨c, -, hc1, heq⟩ := hconv.1 P
    have e : frame (lf D F0) i.castSucc = (lf D F0).fl.e i := by simp [frame, FlagG.fvec]
    rw [e]
    have hmem : (lf D F0).fl.e i ∈ Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • (lf D F0).fl.e a) := by
      have := Submodule.subset_span (R := 𝓞 D.host.E) ⟨i, rfl⟩ (s := Set.range fun a => c a • (lf D F0).fl.e a)
      simpa [hc1 hP i] using this
    have h1 := mem_localization_of_mem' P hmem
    rw [← heq] at h1
    exact localization_mono P inf_le_left h1

theorem glued_frame_PD : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∀ g g', Adapt g (lf D (X.Fu u)) F → Adapt g' (lf D (X.Fu u')) F' → IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) → IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap g'⁻¹ Λ) → Formalism.L2.SG.TermDef.PD D (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) (lf D (X.Fu u)) u' (mapLF (g⁻¹ * g') (lf D (X.Fu u'))) := by
  intro D X Y u u' F F' w hw hG Z FP hB hR Λ y hL g g' hA hA' hr hr'
  have hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hA.1
  have hg' : g' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hA'.1
  have hβ : g⁻¹ * g' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (inv_mem hg) hg'
  have hmap : Formalism.HermitianLatticesTheory.gmap (g⁻¹ * g') (Formalism.HermitianLatticesTheory.gmap g'⁻¹ Λ) = Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ := by
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [← Submodule.map_comp]
    congr 1
    ext x
    simp
  have hmapL : mapLF (g⁻¹ * g') (lf D (X.Fu u')) = Formalism.L2.SG.Saturated.mapL (g⁻¹ * g') hβ (lf D (X.Fu u')) := by
    unfold mapLF; rw [dif_pos hβ]; rfl
  obtain ⟨-, ⟨-, -, hlift', hconv'⟩, hX'⟩ := id hr'
  refine ⟨?_, ?_, ?_⟩
  · have h1 := (Formalism.L2.SG.Pf.IsLift_mapL (g⁻¹ * g') hβ _ _).2 hlift'
    rw [hmap, ← hmapL] at h1
    exact h1
  · exact GlobalTheory.T.glue_frame_congruences_unitriangular_integral (VS D) D.R.rS _ (gS D) (gS_pos D) _ _
      (fun P hP a => frame_mem_locP _ _ hr P hP a)
      (fun P hP => GlobalTheory.T.gluedFrame_congruent_unitriangular_at_primes D X Y u u' F F' w hw hG Z FP hB hR Λ y hL g g' hA hA' hr hr' P hP)
  · exact GlobalTheory.FrameIsom.frameOK_mapLF D (g⁻¹ * g') hβ _ _ hmap _ _ ⟨hconv', hX'⟩

end GlobalTheory.Unfold.AdmGlued
