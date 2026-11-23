import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralRowFrameMapIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlueFrameCongruencesUnitriangularIntegralStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedReferenceFrameCongruentUnitriangularStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.AdmFrame

theorem frame_mem_locP (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hL : IsLift Λ (lf D F0)) (hF : FrameOK D Λ (lf D F0))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal)
    (a : Fin (D.R.rS + 1)) : frame (lf D F0) a ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
  haveI := P.isPrime
  induction a using Fin.lastCases with
  | last =>
    refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
    simp only [one_smul, frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]
    exact hL.1
  | cast i =>
    obtain ⟨c, -, hc1, hc⟩ := hF.1.1 P
    have hci : c i = 1 := hc1 hP i
    have hmem : (lf D F0).fl.e i ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ (lf D F0)) := by
      rw [hc]
      refine ⟨1, P.asIdeal.primeCompl.one_mem, ?_⟩
      rw [one_smul]
      have : (lf D F0).fl.e i = c i • (lf D F0).fl.e i := by rw [hci, one_smul]
      rw [this]
      exact Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨s, hs, hx⟩ := hmem
    refine ⟨s, hs, ?_⟩
    simp only [frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]
    exact (inf_le_left : XLam Λ (lf D F0) ≤ Λ) hx

theorem lift_transport (D : D7) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V) (h : Formalism.HermitianLatticesTheory.gmap γ Λ₁ = Λ₂) {T : D.host.E}
    (F : LFlag (VS D) D.R.rS T) (hL : IsLift Λ₁ F) : IsLift Λ₂ (mapLF γ F) := by
  unfold mapLF
  rw [dif_pos hγ]
  refine ⟨?_, ?_⟩
  · rw [← h]
    exact ⟨F.fl.z, hL.1, rfl⟩
  · show γ F.zt = γ F.fl.z
    rw [hL.2]

theorem exists_admissible_integralFrame_of_localTerms_alt : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ n m, n ∈ NRat (lf D (X.Fu u)) → m ∈ NRat (lf D (X.Fu u')) → Formalism.HermitianLatticesTheory.gmap (n⁻¹ * t₀.lin * m) t₀.lam' = t₀.lam → (∃ d, G.IsTerm d (c.lat (ρ * n) t₀.lam)) → Formalism.L2.SG.TermDef.PD D t₀.lam (lf D (X.Fu u)) u' (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) := by
  intro D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv n m hn hm hlam hterm
  have hγ : n⁻¹ * t₀.lin * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn.1) t₀.rep.2.2.1) hm.1
  have hrow' : IsRowLat D (X.Fu u') t₀.lam' := (Y.rowsOK u').1 _ t₀.mem'
  have hrow : IsRowLat D (X.Fu u) t₀.lam := (Y.rowsOK u).1 _ t₀.mem
  have hpd' := Formalism.L2.SG.TermDef.pd_self (X.Fu u') t₀.lam' hrow'
  have hpd := Formalism.L2.SG.TermDef.pd_self (X.Fu u) t₀.lam hrow
  refine ⟨lift_transport D _ hγ _ _ hlam _ hpd'.1, ?_, GlobalTheory.T.integralRowFrame_map_isometry D _ hγ _ _ hlam _ _ hpd'.2.2⟩
  have hloc := GlobalTheory.T.movedReferenceFrame_congruent_unitriangular D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv n m hn hm hlam hterm
  obtain ⟨ξ, h1, h2, h3⟩ := GlobalTheory.T.glue_frame_congruences_unitriangular_integral (VS D) D.R.rS t₀.lam (gS D) (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)
    (frame (lf D (X.Fu u))) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))))
    (fun P hP a => frame_mem_locP D (X.Fu u) t₀.lam hpd.1 hpd.2.2 P hP a) hloc
  exact ⟨ξ, h1, h2, h3⟩

end GlobalTheory.HL.AdmFrame
