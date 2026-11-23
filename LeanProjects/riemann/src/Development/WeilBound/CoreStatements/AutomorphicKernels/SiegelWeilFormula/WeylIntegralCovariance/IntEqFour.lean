import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WeylIntegralCovariance.IntegralCovGen

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.TW.Twp

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

open PositivityTheory.SiegelWeilFormula.TBij.Adp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem int_eq_four (d : SD σ) (ν : Measure (Mx F E d.m d.n)) (hν : d.IsCov ν) (ε : ℤˣ) (f : Mx F E d.m d.n → ℂ)
    (Y : Matrix (Fin d.m) (Fin d.n) E) :
    ∫ Z, d.B.ψ (((ε : ℤ) : AF F) * d.tt (d.gram (incM F Y) Z)) * f Z ∂ν =
      GroundTheory.Automorphic.GJMatrix.adelicFourierPi F (fun c => f (d.cmb c))
        (fun q => algebraMap F (AF F) (Lm d ε (rc d Y) q)) := by
  rw [integral_cov d ν hν, GroundTheory.Automorphic.GJMatrix.adelicFourierPi]
  congr 1
  funext c
  rw [pair_eq d ε Y (d.cmb c), crd_cmb, GlobalTheory.AdelicSvN.Weyl.isStd_eq d.ok.good.std, mul_comm]

theorem poisson : Poisson := by
  intro F E _ _ _ _ _ σ d ν hν ε f hf
  have hg : (fun c => f (d.cmb c)) ∈ schA F (Ix d) := Submodule.mem_comap.1 hf
  have hθ := GlobalTheory.TowU.FourWeyl.theta_four hg
  refine (tsum_congr fun X => int_eq_four d ν hν ε f X).trans ?_
  refine ((rc d).toEquiv.tsum_eq (fun a => GroundTheory.Automorphic.GJMatrix.adelicFourierPi F (fun c => f (d.cmb c))
      (fun q => algebraMap F (AF F) (Lm d ε a q)))).trans ?_
  refine ((LinearEquiv.ofInjectiveEndo (Lm d ε) (Lm_inj d ε)).toEquiv.tsum_eq
      (fun a => GroundTheory.Automorphic.GJMatrix.adelicFourierPi F (fun c => f (d.cmb c)) (fun q => algebraMap F (AF F) (a q)))).trans ?_
  refine hθ.trans ?_
  show ∑' ξ : Ix d → F, f (d.cmb fun q => algebraMap F (AF F) (ξ q)) = _
  have e : ∀ X : Matrix (Fin d.m) (Fin d.n) E, f (incM F X) = f (d.cmb fun q => algebraMap F (AF F) (rc d X q)) := by
    intro X
    congr 1
    rw [← cmb_crd d (incM F X)]
    congr 1
    funext q
    rw [crd_incM]
    rfl
  simp_rw [e]
  exact ((rc d).toEquiv.tsum_eq (fun a => f (d.cmb fun q => algebraMap F (AF F) (a q)))).symm

end PositivityTheory.SiegelWeilFormula.TW.Twp

end
