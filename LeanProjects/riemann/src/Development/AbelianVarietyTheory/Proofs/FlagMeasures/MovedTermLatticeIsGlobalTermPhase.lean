import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermsOrbitsHeightsAmplitudesInCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDatumEquivariantFlagIsometriesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiOfEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedRowLatticeTermIsLatticeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularFrameChangeFromLinearAutStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SimpleRootCoefEqSuperdiagonalSumFramesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularMulInvSuperdiagonalSumSubStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalScalarMulEqDifferentGenMulThetaStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermWeightEqCharacterMulInvStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTermLatticeIsLocalTermAtPlaceStatement

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.MovedTermPhase

theorem exists_termFrame_admissibilityWitness : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t : TauC Y u u'), ∃ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), AdmWit t.lam (gS D) (lf D (X.Fu u)) t.frame ξ := by
  intro D X Y u u' t
  exact t.rep.2.2.2.2.2.1

theorem psiInf_exp : ∀ {E : Type} [Field E] [NumberField E] (g : ℕ) (x y : E), Complex.exp (-(2 * Real.pi * Complex.I * ((Algebra.trace ℚ E (x / g) : ℚ) : ℂ))) = (Formalism.L2.SG.PairVal.psiInf g x)⁻¹ ∧ Formalism.L2.SG.PairVal.psiInf g (x - y) = Formalism.L2.SG.PairVal.psiInf g x * (Formalism.L2.SG.PairVal.psiInf g y)⁻¹ := by
  intro E _ _ g x y
  refine ⟨?_, ?_⟩
  · have hx : x / (g : E) = ((g : ℚ)⁻¹) • x := by
      rw [Algebra.smul_def, div_eq_inv_mul]
      simp
    rw [Formalism.L2.SG.PairVal.psiInf, ← Complex.exp_neg, hx, LinearMap.map_smul, smul_eq_mul]
    congr 1
    push_cast
    ring
  · simp only [Formalism.L2.SG.PairVal.psiInf, map_sub]
    rw [← div_eq_mul_inv, ← Complex.exp_sub]
    congr 1
    push_cast
    ring

theorem main : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → G.IsTerm (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) ∧ ∀ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E), AdmWit t₀.lam (gS D) (lf D (X.Fu u)) t₀.frame ξ → G.om (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) = (Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp U))⁻¹ * Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp U') * (Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))))⁻¹ := by
  intro D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  obtain ⟨hg0, hcg⟩ := GlobalTheory.T.localScalar_mul_eq_differentGen_mul_theta D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  have hlat := GlobalTheory.T.movedRowLattice_term_isLattice D X Y u u' _ F00 F'0 FP G c t₀ ρ
  have hU := hMv.2.1
  have hU' := hMv.2.2.1

  have hext : ∀ (N : G.GLV) p, ∃ m : (G.S p).GLV, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N m :=
    fun N p => ((GlobalTheory.HL.RatExt.rational_extend (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) _ p).2.2.1 N).exists

  have key : ∀ ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E),
      AdmWit t₀.lam (gS D) (lf D (X.Fu u)) t₀.frame ξ →
      ∃ N N' : G.GLV, (∀ b, N (G.f b) = ∑ a, U a b • G.f a) ∧
        (∀ b, N' (G.f' b) = ∑ a, (U' * (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))⁻¹) a b • G.f' a) ∧
        ∀ p (m m' : (G.S p).GLV), (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N m →
          (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p N' m' →
          (G.S p).IsTerm ((G.S p).datOf ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)))
              ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)) ∧
            (G.S p).om ((G.S p).datOf ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)))
              ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat ρ t₀.lam)) =
              (G.S p).psi m * ((G.S p).psi' m')⁻¹ := by
    intro ξ hξ
    have hξl : ∀ i j, j < i → (ξ.map (algebraMap (𝓞 D.host.E) D.host.E)) i j = 0 := by
      intro i j hij
      simp [Matrix.map_apply, hξ.1 i j hij]
    have hξd : ∀ i, (ξ.map (algebraMap (𝓞 D.host.E) D.host.E)) i i = 1 := by
      intro i
      simp [Matrix.map_apply, hξ.2.1 i]
    obtain ⟨hBl, hBd, -⟩ := GlobalTheory.T.unitriangular_mul_inv_superdiagonalSum_sub U' _ (fun i j h => (hU' i j).1 h) (fun i => (hU' i i).2 rfl) hξl hξd
    obtain ⟨⟨N, hN⟩, -⟩ := GlobalTheory.T.unitriangularFrameChange_from_linearAut (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G U
      (fun i j h => (hU i j).1 h) (fun i => (hU i i).2 rfl)
    obtain ⟨-, ⟨N', hN'⟩⟩ := GlobalTheory.T.unitriangularFrameChange_from_linearAut (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G
      (U' * (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))⁻¹) hBl hBd
    refine ⟨N, N', hN, hN', ?_⟩
    intro p m m' hm hm'
    obtain ⟨t, d, hto, hlatEq, hf, hf'⟩ := GlobalTheory.T.movedTerm_lattice_isLocalTerm_at_place D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U'
      hMv p ξ hξ N N' hN hN' m m' hm hm'
    obtain ⟨h1, -⟩ := GlobalTheory.T.terms_orbits_heights_amplitudes_in_coordinates (Y.M p) (Y.agree p).1 (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p)
      D.R.rS D.R.k (FP p) (G.S p) (c.c p)
    obtain ⟨hT, hom, -⟩ := h1 d t hto
    rw [hlatEq] at hT hom
    have : IsNonarchimedeanLocalField ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp :=
      ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).lf
    have : CharZero ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).Fp :=
      ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).loc p).char0
    have hd := (GlobalTheory.T.hermitian_lattice_datum_equivariant_flag_isometries ((placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).L p) D.R.rS D.R.k (G.S p)).1 _ _ hT
    rw [hd] at hT hom
    have hpsi := GlobalTheory.T.localTermWeight_eq_character_mul_inv (Y.M p) (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS D.R.k (FP p) (G.S p)
      (c.c p) d t hto m m' hf hf'
    exact ⟨hT, hom ▸ hpsi⟩

  have hsig : ∀ x, D.conjF x = star x := fun x => by
    rw [D.conjF_eq]
    exact (Formalism.BasicNotions.bridge_star_holds _ D.host x).symm
  have hprod := fun (n : G.GLV) (m : ∀ p, (G.S p).GLV)
      (hx : ∀ p, (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).Ext p n (m p)) =>
    GlobalTheory.HL.PhaseProduct.main (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G D.sp.cm hsig
      (fun p => Units.mk0 (Y.δ p) (Y.agree p).2.1) (gS D) hg0
      (fun p y => (Y.agree p).2.2.2.2.1 y)
      (fun p => hcg p) n m hx
  obtain ⟨ξ₀, hξ₀⟩ := exists_termFrame_admissibilityWitness D X Y u u' t₀
  refine ⟨⟨hlat, fun p => ?_⟩, ?_⟩
  · obtain ⟨N, N', -, -, hloc⟩ := key ξ₀ hξ₀
    obtain ⟨m, hm⟩ := hext N p
    obtain ⟨m', hm'⟩ := hext N' p
    exact (hloc p m m' hm hm').1
  · intro ξ hξ
    obtain ⟨N, N', hN, hN', hloc⟩ := key ξ hξ
    choose m hm using hext N
    choose m' hm' using hext N'
    obtain ⟨hP, -, hfin⟩ := hprod N m hm
    obtain ⟨-, hP', hfin'⟩ := hprod N' m' hm'
    have hom : G.om (G.datOf (c.lat ρ t₀.lam)) (c.lat ρ t₀.lam) =
        ∏ᶠ p, ((G.S p).psi (m p) * ((G.S p).psi' (m' p))⁻¹) :=
      finprod_congr fun p => (hloc p (m p) (m' p) (hm p) (hm' p)).2
    have hs1 : (Function.mulSupport fun p => (G.S p).psi (m p)).Finite :=
      hfin.subset fun p hp => Or.inl hp
    have hs2 : (Function.mulSupport fun p => ((G.S p).psi' (m' p))⁻¹).Finite :=
      hfin'.subset fun p hp => Or.inr fun h => (Function.mem_mulSupport.1 hp) (by simp [h])
    rw [hom, finprod_mul_distrib hs1 hs2, finprod_inv_distrib, hP, hP',
      (GlobalTheory.T.simpleRootCoef_eq_superdiagonal_sum_frames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G U N).1 hN,
      (GlobalTheory.T.simpleRootCoef_eq_superdiagonal_sum_frames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k G _ N').2 hN',
      (psiInf_exp (gS D) _ 0).1, (psiInf_exp (gS D) _ 0).1, inv_inv]
    have hξl : ∀ i j, j < i → (ξ.map (algebraMap (𝓞 D.host.E) D.host.E)) i j = 0 := by
      intro i j hij
      simp [Matrix.map_apply, hξ.1 i j hij]
    have hξd : ∀ i, (ξ.map (algebraMap (𝓞 D.host.E) D.host.E)) i i = 1 := by
      intro i
      simp [Matrix.map_apply, hξ.2.1 i]
    rw [(GlobalTheory.T.unitriangular_mul_inv_superdiagonalSum_sub U' _ (fun i j h => (hU' i j).1 h) (fun i => (hU' i i).2 rfl) hξl hξd).2.2,
      (psiInf_exp (gS D) _ _).2, mul_assoc]

end GlobalTheory.HL.MovedTermPhase
