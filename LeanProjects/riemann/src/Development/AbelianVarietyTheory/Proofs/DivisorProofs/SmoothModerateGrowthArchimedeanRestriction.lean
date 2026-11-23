import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BridgeSIsBridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedRepLocalFactorFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParameterSkewHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralRealLineDerivative
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupTwoModelsRationalRealUnipotentDictio
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
open Matrix
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HCFinSmooth
open Formalism.MainNotions.S (AutInst uMat)

def tauOf (I : AutInst) (v : InfinitePlace I.F) : EmbOver I.E v := ⟨I.φ v, RingHom.ext (I.φ_over v)⟩

theorem infEmb_comp_compInf (I : AutInst) (v : InfinitePlace I.F) :
    (infEmb (tauOf I v)).comp (compInf I.F I.E v) = Formalism.L2.SG.AdBridge.thetaV I v := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Formalism.L2.SG.AdBridge.thetaV_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem archMat_bridge (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) :
    GlobalTheory.Orb.archMat I.cm.sig I.J (tauOf I v) (projArch I.cm.sig I.J v (GlobalTheory.HCFinU.bridgeS I I.cm.sig rfl x)) =
      I.P v * uMat (x.1 v) * (I.P v)⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  rw [((GlobalTheory.HCFinU.bridgeS_isBridge I) x).1 v, Formalism.L2.SG.AdBridge.ofHAInf, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hd,
    GlobalTheory.Orb.archMat_apply, matHom_projArch, ← infEmb_comp_compInf]
  ext i j
  rfl
end GlobalTheory.HCFinSmooth

namespace GlobalTheory.HCFinSmooth
open Formalism.MainNotions.S (AutInst uMat)

theorem mem_infPts_bridge (I : AutInst) (y : I.Ginf) :
    GlobalTheory.HCFinU.bridgeS I I.cm.sig rfl (y, 1) ∈ infPts I.cm.sig I.J := by
  have h := ((GlobalTheory.HCFinU.bridgeS_isBridge I) (y, 1)).2
  show _ = _
  apply Units.ext
  ext i j
  have h2 := congrFun (congrFun h i) j
  simp only [Formalism.L2.SG.AdBridge.ofHAFin, Matrix.map_apply, GlobalTheory.BridgeDict.tauF_apply] at h2
  have h3 := congrArg (Algebra.TensorProduct.comm I.F _ _).symm h2
  rw [AlgEquiv.symm_apply_apply] at h3
  have h4 : I.fmat 1 = 1 := rfl
  rw [h4] at h3
  refine Eq.trans (?_ : _ = (Algebra.TensorProduct.map (sndA I.F) (AlgHom.id I.F I.E))
    (Formalism.L2.SG.AdBridge.hmat I (GlobalTheory.HCFinU.bridgeS I I.cm.sig rfl (y, 1)) i j)) (h3.symm.trans ?_)
  · rfl
  · by_cases e : i = j
    · subst e; simp
    · simp [e]
end GlobalTheory.HCFinSmooth

namespace GlobalTheory.HCFinSmooth
open Formalism.MainNotions.S (AutInst uMat)
open GlobalTheory.ThKAdmAut (opNorm_le_exp dOp_nonneg)

theorem isCMExt_inst (I : AutInst) : IsCMExt I.F I.E I.cm.sig :=
  (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND I.F I.E I.cm).1

theorem normInf_bridge_le (I : AutInst) (x : I.Ginf) (v : InfinitePlace I.F) :
    (normInf I.F v (matHom _ I.cm.sig I.J (projArch I.cm.sig I.J v (GlobalTheory.HCFinU.bridgeS I I.cm.sig rfl (x, 1)))).1 : ℝ) ≤
      max 1 ((opNorm (I.P v) : ℝ) * opNorm (I.P v)⁻¹) * Real.exp (GlobalTheory.Count.dOp (uMat (x v))) := by
  rw [normInf_eq_opNorm (isCMExt_inst I) (tauOf I v)]
  have h1 := archMat_bridge I (x, 1) v
  rw [GlobalTheory.Orb.archMat_apply] at h1
  rw [h1]
  have h2 : (opNorm (I.P v * uMat (x v) * (I.P v)⁻¹) : ℝ) ≤ opNorm (I.P v) * opNorm (uMat (x v)) * opNorm (I.P v)⁻¹ := by
    exact_mod_cast (opNorm_mul_le _ _).trans (mul_le_mul' (opNorm_mul_le _ _) le_rfl)
  refine h2.trans ?_
  rw [mul_right_comm]
  exact mul_le_mul (le_max_right _ _) (opNorm_le_exp _) (NNReal.coe_nonneg _) (by positivity)

theorem height_bridge_le (I : AutInst) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : I.Ginf,
      (height I.cm.sig I.J (GlobalTheory.HCFinU.bridgeS I I.cm.sig rfl (y, 1)) : ℝ) ≤ C * Real.exp (GlobalTheory.Dec.dSum I y) := by
  refine ⟨∏ v, max 1 ((opNorm (I.P v) : ℝ) * opNorm (I.P v)⁻¹), by positivity, fun y => ?_⟩
  have hfin : ∀ v, htFin I.F v (matHom _ I.cm.sig I.J (proj I.cm.sig I.J v (GlobalTheory.HCFinU.bridgeS I I.cm.sig rfl (y, 1)))) = 1 :=
    fun v => by rw [mem_infPts_iff_forall.1 (mem_infPts_bridge I y) v, map_one, htFin_one]
  rw [height_eq, finprod_eq_one_of_forall_eq_one hfin, mul_one, GlobalTheory.Dec.dSum, Real.exp_sum,
    ← Finset.prod_mul_distrib, NNReal.coe_prod]
  refine Finset.prod_le_prod (fun _ _ => NNReal.coe_nonneg _) fun v _ => ?_
  rw [htInf, htOf, NNReal.coe_max, NNReal.coe_max]
  refine max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_exp (dOp_nonneg _)))
    (max_le (normInf_bridge_le I y v) ?_)
  have h3 := normInf_bridge_le I y⁻¹ v
  have h4 : GlobalTheory.Count.dOp (uMat (y⁻¹ v)) = GlobalTheory.Count.dOp (uMat (y v)) := by
    rw [← GlobalTheory.Count.Cartan.dOp_inv (y v).2]
    exact congrArg GlobalTheory.Count.dOp (Matrix.coe_units_inv _)
  have h5 : GlobalTheory.HCFinU.bridgeS I I.cm.sig rfl (y⁻¹, 1) = (GlobalTheory.HCFinU.bridgeS I I.cm.sig rfl (y, 1))⁻¹ := by
    rw [← map_inv, Prod.inv_mk, inv_one]
  rw [h4, h5, map_inv, map_inv] at h3
  exact h3
end GlobalTheory.HCFinSmooth

namespace GlobalTheory.HCFinSmooth
open Formalism.MainNotions.S (AutInst uMat)

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem isRealLine_bridge (I : AutInst) {γ : ℝ → I.Ginf} (hγ : GlobalTheory.ThKAdmAut.IsLine I γ) :
    IsRealLine I.cm.sig I.J fun t => GlobalTheory.HCFinU.bridgeS I I.cm.sig rfl (γ t, 1) := by
  classical
  have hcm := isCMExt_inst I
  obtain ⟨v, Y, hY⟩ := hγ
  have hu : IsUnit (I.P v) := I.P_unit v
  have hZ : ∀ t : ℝ, GlobalTheory.Orb.archMat I.cm.sig I.J (tauOf I v)
      (projArch I.cm.sig I.J v (GlobalTheory.HCFinU.bridgeS I I.cm.sig rfl (γ t, 1))) =
        NormedSpace.exp (t • (I.P v * Y * (I.P v)⁻¹)) := fun t => by
    rw [archMat_bridge, (hY t).1, ← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.exp_conj _ _ hu]
  refine ⟨v, tauOf I v, I.P v * Y * (I.P v)⁻¹,
    GlobalTheory.ThK.OneParamLie.lie_of_archMat_eq_exp I.F I.E I.cm.sig hcm _ _ _ _ _ _ hZ, fun t => ⟨_, ?_, hZ t⟩⟩
  refine GAd_ext _ _ (fun w => ?_) fun u => ?_
  · by_cases e₁ : w = v
    · subst e₁; rw [projArch_embArch_self]
    · rw [projArch_embArch_ne _ _ e₁]
      apply GlobalTheory.ThK.ZFinDerPol.archMat_inj hcm I.J (tauOf I w)
      have hd := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit w)
      rw [archMat_bridge, map_one]
      show I.P w * uMat (γ t w) * (I.P w)⁻¹ = 1
      rw [(hY t).2 w e₁]
      show I.P w * 1 * (I.P w)⁻¹ = 1
      rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]
  · rw [proj_embArch]
    exact mem_infPts_iff_forall.1 (mem_infPts_bridge I (γ t)) u
end GlobalTheory.HCFinSmooth

namespace GlobalTheory.HCFinSmooth
open Formalism.MainNotions.S (AutInst uMat)

theorem smoothInf_growth_bridge : ∀ (I : Formalism.MainNotions.S.AutInst) (s : I.E →ₐ[I.F] I.E) (hs : s = I.cm.sig) (φ : GlobalTheory.AdelicU.GAd s I.J → ℂ), GlobalTheory.SiegelSet.IsSmoothModerate s I.J φ → ∀ xf : I.Gf, GlobalTheory.Dec.SmoothInf I (fun y => φ (GlobalTheory.HCFinU.bridgeS I s hs (y, xf))) ∧ ∃ C N : ℝ, ∀ y, ‖φ (GlobalTheory.HCFinU.bridgeS I s hs (y, xf))‖ ≤ C * Real.exp (N * GlobalTheory.Dec.dSum I y) := by
  intro I s hs φ hφ xf
  subst hs
  set e := GlobalTheory.HCFinU.bridgeS I I.cm.sig rfl with he
  refine ⟨GlobalTheory.ThKAdmAut.smoothInf_of_lines fun k γ hγ x => ?_, ?_⟩
  · have h1 := hφ.smooth k (fun i t => e (γ i t, 1)) (fun i => isRealLine_bridge I (hγ i)) (e (x, xf))
    convert h1 using 2 with t
    have h2 : ((x * (List.ofFn fun i => γ i (t i)).prod, xf) : I.GA) =
        (x, xf) * MonoidHom.inl _ _ (List.ofFn fun i => γ i (t i)).prod := by simp
    have h3 := map_list_prod (e.toMonoidHom.comp (MonoidHom.inl I.Ginf I.Gf)) (List.ofFn fun i => γ i (t i))
    rw [List.map_ofFn] at h3
    rw [h2, map_mul]
    congr 2
  · obtain ⟨N, hN⟩ := hφ.growth
    obtain ⟨C, hC⟩ := hN [] (by simp)
    obtain ⟨C', hC0, hC'⟩ := height_bridge_le I
    refine ⟨max C 0 * (C' * height I.cm.sig I.J (e (1, xf))) ^ N, N, fun y => ?_⟩
    have h1 : ‖φ (e (y, xf))‖ ≤ C * (height I.cm.sig I.J (e (y, xf)) : ℝ) ^ N := hC (e (y, xf))
    have h2 : (height I.cm.sig I.J (e (y, xf)) : ℝ) ≤
        C' * height I.cm.sig I.J (e (1, xf)) * Real.exp (GlobalTheory.Dec.dSum I y) := by
      have e1 : e (y, xf) = e (y, 1) * e (1, xf) := by rw [← map_mul]; simp
      have h3 : (height I.cm.sig I.J (e (y, xf)) : ℝ) ≤ height I.cm.sig I.J (e (y, 1)) * height I.cm.sig I.J (e (1, xf)) := by
        rw [e1]; exact_mod_cast height_mul_le _ _ _ _
      refine h3.trans ?_
      rw [mul_right_comm]
      exact mul_le_mul_of_nonneg_right (hC' y) (NNReal.coe_nonneg _)
    have hCm : C * (height I.cm.sig I.J (e (y, xf)) : ℝ) ^ N ≤ max C 0 * (height I.cm.sig I.J (e (y, xf)) : ℝ) ^ N :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    refine h1.trans (hCm.trans ?_)
    rw [Real.exp_nat_mul, mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) h2 _) (le_max_right _ _)

end GlobalTheory.HCFinSmooth

theorem _root_.GlobalTheory.T.smooth_moderate_growth_archimedean_restriction : ∀ (I : Formalism.MainNotions.S.AutInst) (s : I.E →ₐ[I.F] I.E) (hs : s = I.cm.sig) (φ : GlobalTheory.AdelicU.GAd s I.J → ℂ), GlobalTheory.SiegelSet.IsSmoothModerate s I.J φ → ∀ xf : I.Gf, GlobalTheory.Dec.SmoothInf I (fun y => φ (GlobalTheory.HCFinU.bridgeS I s hs (y, xf))) ∧ ∃ C N : ℝ, ∀ y, ‖φ (GlobalTheory.HCFinU.bridgeS I s hs (y, xf))‖ ≤ C * Real.exp (N * GlobalTheory.Dec.dSum I y) :=
  GlobalTheory.HCFinSmooth.smoothInf_growth_bridge
