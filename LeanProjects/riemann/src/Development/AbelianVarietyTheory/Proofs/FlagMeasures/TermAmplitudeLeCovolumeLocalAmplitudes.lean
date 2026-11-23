import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalHaarMeasuresPullbackRealGroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalIntegralTensorBoundHypProofStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisingConstantsProductHypProofStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FormAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelCharPfRat
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEqMeas
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopTermLem
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpFibreConstOf

noncomputable section
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem factC_of (hP : PullC) (hTn : TensC) (hC : ConstC) : FactC := by
  intro D X Y u C hB hG hcov t hrel μ ν K hμν hK
  obtain ⟨μR, νl, hνl, hH, hQ, hμR, hmap⟩ := hP D X Y u C t μ ν hμν
  have hFA := Formalism.L2.SG.Pf.formAllC_holds D X Y u u t μR (Measure.pi νl) K
    (Formalism.L2.SG.Pf.RelChar.relCharC_holds D X Y u u t hrel) hH hQ hK.1 hK.2
  have hT := hTn D X u t.pt.1 νl hνl
  obtain ⟨hc, hconst⟩ := hC D X Y u C hB hG hcov
  have hloc : ∀ τ, Real.sqrt (hsNormSq ((locS hB u u τ).J (ν τ) (gamT C t τ))) =
      (cOf hB u τ)⁻¹ * Real.sqrt (hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ))
        Formalism.L2.SG.RealObj.Jv (νl (vOf X τ)) (X.Wloc u (vOf X τ)) (X.Wloc u (vOf X τ)) (t.pt.1 (vOf X τ)))) := by
    intro τ
    rw [← hmap τ]
    unfold gamT
    rw [Formalism.L2.SG.Pf.LocJEq.locJ_map_eq' C hB u u τ]
    refine (congrArg Real.sqrt (Formalism.L2.SG.Pf.LTL.hsNormSq_smul _ _)).trans ?_
    rw [(hc τ).2, mul_one, map_inv₀, Complex.normSq_ofReal, Real.sqrt_mul', Real.sqrt_inv,
      Real.sqrt_mul_self (hc τ).1.le]
    · rfl
    · exact Formalism.L2.SG.Pf.LTL.hsNormSq_nonneg _
  have hv : ‖(Y.tO u u).vec t‖ = wt t * ‖Formalism.L2.SG.PackageTie.hsEmb
      (ampN (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t)‖ := by
    show ‖Formalism.L2.SG.TermOp.vec (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t‖ = _
    unfold Formalism.L2.SG.TermOp.vec
    rw [← norm_smul_of_nonneg (show 0 ≤ wt t from Real.sqrt_nonneg _) (Formalism.L2.SG.PackageTie.hsEmb
      (ampN (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t)), ← Complex.coe_smul]
    refine Eq.trans ?_ (PiLp.norm_toLp_single 2
      (fun _ : {Λ // Λ ∈ Y.what₂ u} × {Λ' // Λ' ∈ Y.what₂ u} => Formalism.L2.SG.PackageTie.HS (X.Vpi u) (X.Vpi u))
      ((⟨t.lam, t.mem⟩, ⟨t.lam', t.mem'⟩) : {Λ // Λ ∈ Y.what₂ u} × {Λ' // Λ' ∈ Y.what₂ u}) _)
    congr 2
    funext q
    simp only [Pi.single_apply]
  have hs0 : 0 ≤ scl (Y.FN u) (Y.FN u) (X := X) (u := u) (u' := u) * X.volK2 := by
    unfold scl HidaSetting.volK2
    positivity
  have hamp : ‖Formalism.L2.SG.PackageTie.hsEmb (ampN (Y.cs u) (Y.cs u) (Y.FN u) (Y.FN u) t)‖ =
      (scl (Y.FN u) (Y.FN u) (X := X) (u := u) (u' := u) * X.volK2) * ((μR K).toReal *
        ‖Formalism.L2.SG.PackageTie.hsEmb (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          OO (Measure.pi νl) Set.univ (X.Wu u) (X.Wu u) t.pt.1)‖) := by
    unfold ampN
    rw [map_smul, map_smul, norm_smul, norm_smul, Formalism.L2.SG.Pf.FibreCounting.norm_chiN, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hs0, hFA, ← Complex.coe_smul, map_smul, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have hprod : ∏ τ, Real.sqrt (hsNormSq ((locS hB u u τ).J (ν τ) (gamT C t τ))) =
      (∏ τ, cOf hB u τ)⁻¹ * ∏ v, Real.sqrt (hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
        Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (t.pt.1 v))) := by
    rw [Finset.prod_congr rfl fun τ _ => hloc τ, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    congr 1
    exact Fintype.prod_equiv X.pl.symm _ _ (fun τ => rfl)
  have hPc : 0 < ∏ τ, cOf hB u τ := Finset.prod_pos fun τ _ => (hc τ).1
  rw [hv, hamp, ← hμR K hK.1, hprod]
  set N := ‖Formalism.L2.SG.PackageTie.hsEmb (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          OO (Measure.pi νl) Set.univ (X.Wu u) (X.Wu u) t.pt.1)‖ with hN
  set Pv := ∏ v, Real.sqrt (hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v)
        Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u v) (t.pt.1 v))) with hPv
  set Pc := ∏ τ, cOf hB u τ with hPcd
  set s := scl (Y.FN u) (Y.FN u) (X := X) (u := u) (u' := u) * X.volK2 with hsd
  set a := wt t with had
  set m := (μR K).toReal with hmd
  set cv := (covN C Y u).toReal with hcv
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  have hcv0 : 0 ≤ cv := ENNReal.toReal_nonneg
  have hPv0 : 0 ≤ Pv := Finset.prod_nonneg fun v _ => Real.sqrt_nonneg _
  have hNP : N ≤ Pv := hT
  have hSJ : 0 ≤ Pc⁻¹ * Pv := mul_nonneg (inv_nonneg.2 hPc.le) hPv0
  calc a * (s * (m * N)) * cv = (a * m * cv * s) * N := by ring
    _ ≤ (a * m * cv * s) * (Pc * (Pc⁻¹ * Pv)) := by
        rw [mul_inv_cancel_left₀ hPc.ne']
        exact mul_le_mul_of_nonneg_left hNP (by positivity)
    _ = (a * (m * (Pc⁻¹ * Pv))) * (s * Pc * cv) := by ring
    _ ≤ (a * (m * (Pc⁻¹ * Pv))) * 1 := mul_le_mul_of_nonneg_left hconst (by positivity)
    _ = a * (m * (Pc⁻¹ * Pv)) := mul_one _

theorem factC_holds : FactC := factC_of GlobalTheory.T.localHaarMeasures_pullback_realGroup GlobalTheory.T.orbitalIntegralTensorBoundHyp_proof GlobalTheory.T.normalisingConstantsProductHyp_proof

end GlobalTheory.TypeAsm
