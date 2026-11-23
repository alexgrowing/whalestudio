import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceRep

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct ContDiff

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7}

def algEntry (V : HSp D) (τ : D.what₂.Tau) (m j : Fin V.rank) : AlgInf V →ₗ[ℝ] ℂ where
  toFun u := (u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) τ m j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem contDiff_expEntry (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D}
    (R : RealPoints θ V) (τ : D.what₂.Tau) (m j : Fin V.rank) :
    ContDiff ℝ ∞ fun X : LieN V => algEntry V τ m j (NormedSpace.exp (jInf V X)) := by
  haveI : CompleteSpace (AlgInf V) := FiniteDimensional.complete ℝ (AlgInf V)
  haveI : FiniteDimensional ℝ (LieN V) := FiniteDimensional.of_injective (jInf V) (isLieData R).inj
  have h1 : ContDiff ℝ ∞ (NormedSpace.exp : AlgInf V → AlgInf V) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact (LinearMap.toContinuousLinearMap (algEntry V τ m j)).contDiff.comp
    (h1.comp (LinearMap.toContinuousLinearMap (jInf V)).contDiff)

theorem realEntries_mul_exp (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D}
    (R : RealPoints θ V) (g : GA D V) (X : LieN V) (p : D.what₂.Tau × Fin V.rank × Fin V.rank) :
    realEntries θ V (g * expMap (jInf V) (secInf θ V) X) p =
      ∑ m, infMat D.sp.cm.sig V.gram (θ p.1) g p.2.1 m * algEntry V p.1 m p.2.2 (NormedSpace.exp (jInf V X)) := by
  have h2 := (isExpFam_expInf R X).2 p.1
  change infMat D.sp.cm.sig V.gram (θ p.1) (g * expInf θ V X) p.2.1 p.2.2 = _
  rw [R.2.2.2.1, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  change infMat D.sp.cm.sig V.gram (θ p.1) (expInf θ V X) m p.2.2 = (NormedSpace.exp (jInf V X) : AlgInf V) p.1 m p.2.2
  rw [exp_algInf, h2]
  rfl

theorem polyFun_mem_smF : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
    RealPoints θ V → ∀ P : PolyE V, polyFun θ V P ∈ SmF θ V := by
  intro D θ V R P g
  have hc : ∀ p : D.what₂.Tau × Fin V.rank × Fin V.rank,
      ContDiff ℝ ∞ fun X : LieN V => realEntries θ V (g * expMap (jInf V) (secInf θ V) X) p := by
    intro p
    simp only [realEntries_mul_exp θ R]
    exact ContDiff.sum fun m _ => contDiff_const.mul (contDiff_expEntry θ R p.1 m p.2.2)
  change ContDiff ℝ ∞ fun X : LieN V => MvPolynomial.eval (realEntries θ V (g * expMap (jInf V) (secInf θ V) X)) P
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p n hp => simpa only [map_mul, MvPolynomial.eval_X] using hp.mul (hc n)

end GlobalTheory.CentralOps

end
