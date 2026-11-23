import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp.DetImMeas

theorem measurableSet_det_im_pos : ∀ (κ : Type) [Fintype κ] (p q : κ → ℕ) (ρ₀ : κ), MeasurableSet {b : ∀ ρ, UpqT (p ρ) (q ρ) | 0 < (UpqT.mat (b ρ₀)).det.im} := by
  intro κ _ p q ρ₀
  haveI : BorelSpace (UpqT (p ρ₀) (q ρ₀)) := (GlobalTheory.UpqTopology.upq_lcsc (p ρ₀) (q ρ₀)).2.2.2.2.1
  have hc : Continuous fun g : UpqT (p ρ₀) (q ρ₀) => (UpqT.mat g).det.im :=
    Complex.continuous_im.comp ((continuous_id.matrix_det).comp GlobalTheory.UpqTopology.continuous_mat)
  have hm : Measurable fun b : (∀ ρ, UpqT (p ρ) (q ρ)) => (UpqT.mat (b ρ₀)).det.im :=
    hc.measurable.comp (measurable_pi_apply ρ₀)
  exact measurableSet_lt measurable_const hm

end GlobalTheory.CovTop.VolUp.DetImMeas
