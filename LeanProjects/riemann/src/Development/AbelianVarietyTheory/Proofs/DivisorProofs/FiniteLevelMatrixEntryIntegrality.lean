import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BridgeSIsBridge
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
open Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HCFinLevel

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem infinitePart_eq_zero_of_forall_component_eq_zero (I : Formalism.MainNotions.S.AutInst) (z : AF I.F ⊗[I.F] I.E)
    (hz : ∀ v, Formalism.L2.SG.AdBridge.thetaV I v z = 0) :
    Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E) z = 0 := by
  have hc : ∀ k, fstA I.F ((Formalism.L2.SG.Pf.alg_B I).repr z k) = 0 := by
    intro k
    funext v
    have := Formalism.L2.SG.Pf.alg_inf_inj I v _ _ (by rw [← Formalism.L2.SG.Pf.alg_theta]; exact hz v)
    fin_cases k
    · exact this.1
    · exact this.2
  rw [Formalism.L2.SG.Pf.alg_y_eq I z, map_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Algebra.TensorProduct.map_tmul, hc k, TensorProduct.zero_tmul]

open Formalism.L2.SG.AdBridge in

theorem map_fst_eq_one (I : Formalism.MainNotions.S.AutInst) (M : Matrix (Fin I.n) (Fin I.n) (AF I.F ⊗[I.F] I.E))
    (hB : ∀ v, (1 : Matrix (Fin I.n) (Fin I.n) ℂ) = (I.P v)⁻¹ * M.map (thetaV I v) * I.P v) :
    M.map (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E)) = 1 := by
  have hM : ∀ v, M.map (thetaV I v) = 1 := by
    intro v
    have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    have h : I.P v * 1 * (I.P v)⁻¹ = I.P v * ((I.P v)⁻¹ * M.map (thetaV I v) * I.P v) * (I.P v)⁻¹ :=
      congrArg (fun Q => I.P v * Q * (I.P v)⁻¹) (hB v)
    rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hP] at h
    have e : I.P v * ((I.P v)⁻¹ * M.map (thetaV I v) * I.P v) * (I.P v)⁻¹ = M.map (thetaV I v) := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hP, Matrix.mul_one,
        Matrix.mul_nonsing_inv_cancel_left _ _ hP]
    exact e.symm.trans h.symm
  ext i j
  rw [Matrix.map_apply]
  have h0 := infinitePart_eq_zero_of_forall_component_eq_zero I (M i j - (1 : Matrix (Fin I.n) (Fin I.n) _) i j) (by
    intro v
    have := congrFun (congrFun (hM v) i) j
    rw [Matrix.map_apply] at this
    rw [map_sub, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp)
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem main : ∀ (I : Formalism.MainNotions.S.AutInst) (s : I.E →ₐ[I.F] I.E) (hs : s = I.cm.sig) (U : Subgroup (GlobalTheory.AdelicU.GAd s I.J)), IsOpen (U : Set (GlobalTheory.AdelicU.GAd s I.J)) → ∃ g : ℕ, 1 ≤ g ∧ ∀ k ∈ I.Kg g, GlobalTheory.HCFinU.bridgeS I s hs (1, k) ∈ U ∧ ((Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) s I.J (GlobalTheory.HCFinU.bridgeS I s hs (1, k)) : Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E))).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA I.F) (AlgHom.id I.F I.E)) = 1 := by
  intro I s hs U hU
  subst hs
  have hc : Continuous fun k : I.Gf => GlobalTheory.HCFinU.bridgeS I I.cm.sig rfl (1, k) :=
    (GlobalTheory.HCFinU.bridgeS I I.cm.sig rfl).continuous.comp (continuous_const.prodMk continuous_id)
  have hO : IsOpen ((fun k : I.Gf => GlobalTheory.HCFinU.bridgeS I I.cm.sig rfl (1, k)) ⁻¹' (U : Set _)) := hU.preimage hc
  have h1 : (fun k : I.Gf => GlobalTheory.HCFinU.bridgeS I I.cm.sig rfl (1, k)) ⁻¹' (U : Set _) ∈ nhds (1 : I.Gf) := by
    refine hO.mem_nhds ?_
    show GlobalTheory.HCFinU.bridgeS I I.cm.sig rfl (1, 1) ∈ U
    have : ((1, 1) : I.GA) = 1 := rfl
    rw [this, map_one]; exact U.one_mem
  obtain ⟨g, hg1, hgU⟩ := I.topf_basis _ h1
  refine ⟨g, hg1, fun k hk => ⟨hgU hk, ?_⟩⟩
  have hb := (GlobalTheory.HCFinU.bridgeS_isBridge I (1, k)).1
  refine map_fst_eq_one I _ fun v => ?_
  have h2 := hb v
  have h3 : Formalism.MainNotions.S.uMat ((1 : I.Ginf) v) = 1 := by simp [Formalism.MainNotions.S.uMat]
  exact h3.symm.trans h2

end GlobalTheory.HCFinLevel
