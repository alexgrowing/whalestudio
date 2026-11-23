import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeries
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormRationality
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTestFunctionOfFockVacuumThetaFunction
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionTranslatesThetaByUnitScalar
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeakWeilRepCarriesDerivativesVacuaFockVectors
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.RealColAct

open GlobalTheory.Ker.ColChange

theorem pureTensor_compAt {D : D7} {S T : HSp D} (C : Ctx S T) (h : GA D S) {B : C.Bas} (hB : C.IsB B)
    {f : WO S T → ℂ} (hf : C.IsTh f) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) B f Q =
      C.fvec B f (ColChange.sub C h Q) := by
  have hU : ∀ τ, (compAt C.θ τ (Formalism.L2.Theta.mt S h))⁻¹ = (compAt C.θ τ (Formalism.L2.Theta.mt S h))ᴴ := fun τ =>
    Matrix.inv_eq_left_inv (GlobalTheory.Ker.ColChange.compAt_unitary C h τ)
  have key : ∀ g : WO S T → ℂ, C.IsTh g → ∀ v : FVar D T.rank S.rank,
      aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) B v g =
        ∑ l, (if (v.2.1 : ℕ) < C.X.p0 then conj (compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2)
            else compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2) •
          aPlusAll (heisO C.ψ S T) C.θ (fun τ => cplxO 1 (C.sB B τ)) (fun _ => 1) B (v.1, v.2.1, l) g := by
    rintro g hg ⟨τ, i, j⟩
    have hc : ∀ z : Matrix (Fin T.rank) (Fin S.rank) ℂ, aPlus (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z g =
        ((fockScale D τ : ℂ)⁻¹) • crea (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) z g := by
      intro z
      rw [GlobalTheory.Ker.FockAlg.aPlus_eq C]
      unfold crea
      rw [sub_eq_add_neg, neg_smul]
    change aPlus (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) (unitMap (compAt C.θ τ (Formalism.L2.Theta.mt S h)) (B τ) i j) g =
      ∑ l, (if (i : ℕ) < C.X.p0 then conj (compAt C.θ τ (Formalism.L2.Theta.mt S h) l j)
            else compAt C.θ τ (Formalism.L2.Theta.mt S h) l j) •
        aPlus (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) (unitMap 1 (B τ) i l) g
    simp only [hc]
    rw [GlobalTheory.Ker.ColChange.unitMap_expand, GlobalTheory.Ker.ColChange.crea_sum C hg, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [GlobalTheory.Ker.ColChange.crea_smul C hg τ (C.sB B τ) (unitMap 1 (B τ) i l) ((i : ℕ) < C.X.p0)
      (GlobalTheory.Ker.ColChange.sB_unitMap C hB τ i l), hU τ, Matrix.conjTranspose_apply, smul_smul, smul_smul]
    congr 1
    split_ifs <;> simp [Complex.star_def, mul_comm]
  have Lc := fun P : MvPolynomial (FVar D T.rank S.rank) ℂ =>
    GlobalTheory.Ker.FockAlg.fock_vec_laws D S T C B hB (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) f hf P
  have L1 := fun P : MvPolynomial (FVar D T.rank S.rank) ℂ =>
    GlobalTheory.Ker.FockAlg.fock_vec_laws D S T C B hB (fun _ => 1) f hf P
  have hX : ∀ v : FVar D T.rank S.rank, ColChange.sub C h (MvPolynomial.X v) =
      ∑ l, (if (v.2.1 : ℕ) < C.X.p0 then conj (compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2)
          else compAt C.θ v.1 (Formalism.L2.Theta.mt S h) l v.2.2) • MvPolynomial.X (v.1, v.2.1, l) := fun v =>
    MvPolynomial.aeval_X _ v
  show pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun τ => compAt C.θ τ (Formalism.L2.Theta.mt S h)) B f Q =
    pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun _ => 1) B f (ColChange.sub C h Q)
  induction Q using MvPolynomial.induction_on
  next a =>
    have e : (MvPolynomial.C a : MvPolynomial (FVar D T.rank S.rank) ℂ) = a • 1 := by
      rw [MvPolynomial.smul_eq_C_mul, mul_one]
    rw [e, map_smul, map_smul, map_smul, map_one (ColChange.sub C h), (Lc 1).2.2.1, (L1 1).2.2.1]
  next p q hp hq =>
    rw [map_add, map_add, map_add, hp, hq]
  next p v hp =>
    rw [mul_comm p, (Lc p).2.1 v, hp, key _ (L1 (ColChange.sub C h p)).1 v, map_mul, hX, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, map_smul, (L1 (ColChange.sub C h p)).2.1]

theorem om_real_fvec : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ B, C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → ∀ h ∈ GinfC S, ∃ c : ℂ, c ≠ 0 ∧ ∀ Q Q' : MvPolynomial (FVar D T.rank S.rank) ℂ, C.toH Q' = Harm.colActHom (GlobalTheory.Ker.ColChange.colU C h) (C.toH Q) → om (h, 1) (C.fvec B f Q) = c • C.fvec B f Q' := by
  intro D S T C om hom B hB f hf hF h hh
  obtain ⟨φ, hφ, hfφ⟩ := GlobalTheory.Ker.exists_test_of_fock D S T C B hB f hf hF
  obtain ⟨c, hc, hcφ⟩ := GlobalTheory.Ker.RealScalar.om_real_Th D S T C om hom h hh 1 (one_mem _) B hB
  have h1 : C.mvB 1 B = B := GlobalTheory.Ker.ONBasis.mvB_fin C B (one_mem _)
  have hom1 : om (h, 1) f = c • f := by rw [hfφ, hcφ φ hφ, h1]
  refine ⟨c, fun h0 => by simp [h0] at hc, fun Q Q' hQ => ?_⟩
  have hQ' : Q' = ColChange.sub C h Q := C.toH_bijective.1 (by
    rw [hQ]; exact (DFunLike.congr_fun (GlobalTheory.Ker.ColChange.toH_sub C h) Q).symm)
  rw [hQ', GlobalTheory.Ker.WeakMove.om_fvec C hom h 1 hf B Q, h1, hom1,
    pureTensor_compAt C h hB (GlobalTheory.Ker.FockAlg.th_smul C c hf) Q]
  exact (GlobalTheory.Ker.FockAlg.fock_vec_laws D S T C B hB (fun _ => 1) f hf (ColChange.sub C h Q)).2.2.2.2.1 c

end GlobalTheory.Ker.RealColAct

end
