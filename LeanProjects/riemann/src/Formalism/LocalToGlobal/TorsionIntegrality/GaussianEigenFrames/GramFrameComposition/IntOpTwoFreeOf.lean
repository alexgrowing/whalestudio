import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementH
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.LocNormFreeProof
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.JetsLin
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.ThmBGaussFreeOf
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.MulRing
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.NormLtOne
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactTer
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussSharpTranslateHolds

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual Th alphaQ kernel4 opU taylorMv)
open Formalism.L2.Th1.Top (IsLatH thetaZ)
open Formalism.L2.Th1.E (IntCurve Unif)
open Formalism.L2.Th1.G (linSub)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)
open Formalism.L2.Th1.CM (omegaK)

namespace GramFrameCompositionTwoFacts

theorem conj_omegaK (d : ℕ) : conj (omegaK d) = (1 - Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2 := by
  rw [omegaK, map_div₀, map_add, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

end GramFrameCompositionTwoFacts

open GramFrameCompositionTwoFacts

open Formalism.L2.Th1.G JL Formalism.G in
theorem JetsLinZ_proof : JetsLinZ := by
  intro K _ _ _ n _ T γ hT ν _ M Cm hC hM
  have k1 : JetsIn (unitBall K) (linSub γ (Formalism.L2.Th1.G.tens4 T)) := (jets_in_norm_holds K _ _).1 hT
  have k2 : JetsIn (unitBall K) (linSub Cm (linSub γ (Formalism.L2.Th1.G.tens4 T))) := jetsIn_linSub hC k1
  have e : (fun (w : Fin 4 × n) (x : Fin 4 × ν) => ∑ w', γ w w' * Cm w' x) = four M := by
    funext w x
    exact hM w.1 w.2 x.1 x.2
  rw [linSub_linSub, e, linSub_tens4] at k2
  exact jets_fourth_holds K (unitBall K) ν (linSub M T) fourth_root_mem k2

end Formalism.L2.Th1.GD
