import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CommonModel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PWdModel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetCo
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetRingS
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetBasis
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetWdLift
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetWeil
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetSpan
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetCoLift
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetCommon
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

namespace UpperTheory.Gal.crystallineComparison

private theorem roots_prod {W : Type} [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W] (M : End ℂ W) :
    M.charpoly.roots.prod = LinearMap.det M := by
  classical
  let b := Module.finBasis ℂ W
  rw [← LinearMap.charpoly_toMatrix M b, ← LinearMap.det_toMatrix b M, Matrix.det_eq_prod_roots_charpoly]

set_option maxHeartbeats 1600000 in
theorem detWD_of (hW : WdModel) (hC : CommonModel) (hE : DetE) : DetWD := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj a r c hdet hr hc g hg
  obtain ⟨LL, r', c', m₁, m₂, hs, p₁, p₂⟩ := hC l P AI hT E Ω _ O Bw a r c hr hc
  have hd : ∀ x, Matrix.GeneralLinearGroup.det (c' x) = Matrix.GeneralLinearGroup.det (r' x) := by
    intro x
    have e := congrArg Units.val (hdet x)
    rw [← m₁.2, ← m₂.2] at e
    refine Units.ext ((algebraMap ↥LL.1 (Om l)).injective ?_)
    simp only [Matrix.GeneralLinearGroup.val_det_apply] at e ⊢
    rw [RingHom.map_det, RingHom.map_det]
    exact e
  have k := hE l P AI hT ι E Ω A w h O Bw hj a LL r' c' hd hs p₁ p₂ g hg
  have e₁ := (hW l P ι E Ω A w h O Bw hj a r LL r' m₁ p₁ g).1
  have e₂ := (hW l P ι E Ω A w h O Bw hj 1 c LL c' m₂ p₂ g).1
  haveI := p₁.finite
  haveI := p₂.finite
  exact ((congrArg (fun p : Polynomial ℂ => p.roots.prod) e₁).trans ((roots_prod _).trans (k.trans (roots_prod _).symm))).trans
    (congrArg (fun p : Polynomial ℂ => p.roots.prod) e₂).symm

theorem detWD_holds : DetWD :=
  detWD_of wdModel_of detCommon_of
    (detOne_of detCo_of detRingS_of (detCore_of detUnit_of detBasis_of) (detMem_of detCo_of) detWeil_of (detSpan_of detCo_of)
      (detCoLift_of detCo_of detWdLift_of))

end UpperTheory.Gal.crystallineComparison
