import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermFramesCongrModThetaUnitriangularStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovesToGivesIntegralMatricesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalScalarEqOneAtPlaceOverTypePrimesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThetaSmulCompletedLatticeIffTypePrimeMulStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameMemRowLatticesOfWordStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGlobalUnitriangularOfLocalCongruenceStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.LocCong

theorem bc_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    (A : GlobalTheory.HL.Places F E sig) {N r : ℕ} (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (B : Fin (r + 1) → E) (v : Fin (r + 1) → Fin N → E) :
    A.bc p (∑ a, B a • v a) = ∑ a, (A.loc p).ιE (B a) • A.bc p (v a) := by
  funext i
  simp [GlobalTheory.HL.Places.bc, Finset.sum_apply, map_sum, smul_eq_mul]

theorem loc_cong : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ n m, n ∈ NRat (lf D (X.Fu u)) → m ∈ NRat (lf D (X.Fu u')) → Formalism.HermitianLatticesTheory.gmap (n⁻¹ * t₀.lin * m) t₀.lam' = t₀.lam → (∃ d, G.IsTerm d (c.lat (ρ * n) t₀.lam)) → ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • t₀.lam)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hFP G c t₀ ρ U U' hMov n m hn hm hgm hterm P hP
  obtain ⟨d, hlat, hloc⟩ := hterm
  obtain ⟨B, B', hB1, hB2, hB1', hB2', hBB⟩ := GlobalTheory.T.moves_to_gives_integral_matrices D X Y u u' F00 F'0 t₀ ρ U U' hMov n m hn hm
  have hc1 := GlobalTheory.T.localScalar_eq_one_at_place_over_typePrimes D X Y F00 F'0 FP G c P hP
  have hSf : ∀ a, (G.S (below D P)).f a = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).bc (below D P) (G.f a) := by
    intro a
    have := G.f_eq (below D P) a
    rw [hc1] at this
    simpa using this
  have hSf' : ∀ a, (G.S (below D P)).f' a = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).bc (below D P) (G.f' a) := by
    intro a
    have := G.f'_eq (below D P) a
    rw [hc1] at this
    simpa using this
  have hiso : n⁻¹ * t₀.lin * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hn.1) t₀.rep.2.2.1) hm.1
  have hfr : ∀ b, frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b = (n⁻¹ * t₀.lin * m) (frame (lf D (X.Fu u')) b) := by
    intro b
    unfold mapLF
    rw [dif_pos hiso]
    simp only [frame, Formalism.MainNotions.S.FlagG.fvec, mapFlag]
    exact (congrFun (Fin.comp_snoc (⇑(n⁻¹ * t₀.lin * m)) _ _) b).symm
  have hyin : ∀ a, frame (lf D (X.Fu u)) a ∈ t₀.lam := fun a => GlobalTheory.T.fixedFrame_mem_rowLattices_of_word D X Y u t₀.lam t₀.mem a
  have hxin : ∀ b, frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b ∈ t₀.lam := by
    intro b
    rw [hfr b, ← hgm]
    exact Submodule.mem_map_of_mem (GlobalTheory.T.fixedFrame_mem_rowLattices_of_word D X Y u' t₀.lam' t₀.mem' b)
  have hy : ∀ b, c.e ((ρ * n) (frame (lf D (X.Fu u)) b)) = ∑ a, B a b • G.f a := by
    intro b
    rw [LinearEquiv.mul_apply, (hBB b).1, map_sum]
    simp only [map_smul, c.f_eq]
  have hx : ∀ b, c.e ((ρ * n) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b)) = ∑ a, B' a b • G.f' a := by
    intro b
    rw [LinearEquiv.mul_apply, (hBB b).2, map_sum]
    simp only [map_smul, c.f'_eq]
  have hmemc : ∀ v ∈ t₀.lam, c.e ((ρ * n) v) ∈ c.lat (ρ * n) t₀.lam := fun v hv =>
    Submodule.mem_map.2 ⟨v, hv, rfl⟩
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).lf
  haveI := ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).char0
  obtain ⟨ξp, hξO, hξ1, hξ2, hξT⟩ := GlobalTheory.T.term_frames_congr_mod_theta_unitriangular _ D.R.rS D.R.k (G.S (below D P)) (d (below D P))
    ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat (below D P) (c.lat (ρ * n) t₀.lam)) (hloc (below D P))
    (fun b => (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).bc (below D P) (c.e ((ρ * n) (frame (lf D (X.Fu u)) b))))
    (fun b => (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).bc (below D P) (c.e ((ρ * n) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b))))
    (fun a b => ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE (B a b)) (fun a b => ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc (below D P)).ιE (B' a b))
    (fun a b h => by simp [hB1 a b h]) (fun a => by simp [hB2 a])
    (fun a b h => by simp [hB1' a b h]) (fun a => by simp [hB2' a])
    (fun b => by simp only [hy, bc_sum, hSf])
    (fun b => by simp only [hx, bc_sum, hSf'])
    (fun a => Submodule.subset_span ⟨_, hmemc _ (hyin a), rfl⟩)
    (fun b => Submodule.subset_span ⟨_, hmemc _ (hxin b), rfl⟩)
  have hfg : (c.lat (ρ * n) t₀.lam).FG := hlat.fg
  have hpos : 0 < gS D := by
    unfold gS
    exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  obtain ⟨ξ, hu1, hu2, hPP⟩ := GlobalTheory.T.exists_global_unitriangular_of_local_congruence (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) _ D.R.rS (c.lat (ρ * n) t₀.lam) hfg
    (gS D) hpos (below D P)
    (fun b => c.e ((ρ * n) (frame (lf D (X.Fu u)) b)))
    (fun b => c.e ((ρ * n) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b))) ξp hξO hξ1 hξ2
    (fun a => Submodule.subset_span ⟨_, hmemc _ (hyin a), rfl⟩)
    (fun b => (GlobalTheory.T.theta_smul_completedLattice_iff_typePrimeMul D X Y F00 F'0 FP G c P hP (c.lat (ρ * n) t₀.lam) _).1 (hξT b))
  refine ⟨ξ, hu1, hu2, fun b => ?_⟩
  have h := hPP P rfl b
  set v := frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b - frameAct (frame (lf D (X.Fu u))) ξ b with hv
  have hφ : c.e ((ρ * n) (frame (mapLF (n⁻¹ * t₀.lin * m) (lf D (X.Fu u'))) b)) -
      ∑ a, ((ξ a b : 𝓞 D.host.E) : D.host.E) • c.e ((ρ * n) (frame (lf D (X.Fu u)) a)) = c.e ((ρ * n) v) := by
    rw [hv, map_sub, map_sub]
    simp only [frameAct, map_sum, map_smul]
  rw [hφ] at h
  have hmap : Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • c.lat (ρ * n) t₀.lam =
      (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • t₀.lam).map
        ((((ρ * n).trans c.e : (VS D).V ≃ₗ[D.host.E] G.V) : (VS D).V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)) := by
    unfold GCoord.lat
    rw [Submodule.map_smul'']
  rw [hmap] at h
  obtain ⟨s, hs, hsv⟩ := h
  refine ⟨s, hs, ?_⟩
  obtain ⟨z, hz, hzv⟩ := Submodule.mem_map.1 hsv
  have hinj : Function.Injective ((((ρ * n).trans c.e : (VS D).V ≃ₗ[D.host.E] G.V) : (VS D).V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)) :=
    ((ρ * n).trans c.e).injective
  have : z = s • v := by
    apply hinj
    rw [hzv, LinearMap.map_smul]
    rfl
  rw [← this]
  exact hz

end GlobalTheory.HL.LocCong
