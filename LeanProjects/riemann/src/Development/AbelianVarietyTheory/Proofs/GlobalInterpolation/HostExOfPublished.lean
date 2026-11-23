import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Jutila
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.PageThm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsExcRat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.QuadraticHeckeZeroEstimates
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HostExistenceOfChoicesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesAndLevelPrimeStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QdChoiceOfHyp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SmallPrimeOneOfTzRat
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThinChoiceOfZeroDensityStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TopsChoiceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem hostEx_of_zeroFreeRegion :
    GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → GlobalTheory.Mem.An.TZRat → GlobalTheory.Mem.An.PageThm → GlobalTheory.Mem.An.Jutila → GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → HostEx :=
  fun hZ hC hL hN hD hR hP hJ hQ =>
    GlobalTheory.T.host_existence_of_choices (GlobalTheory.EX.qdChoice_of_explicitFormula hZ hC hL hN hD hR hP hJ)
      (GlobalTheory.T.thin_choice_of_zero_density hZ hC hL hN hD) (GlobalTheory.T.norm_primes_and_level_prime hQ).1
      (GlobalTheory.EX.smallPrimeOne_of_tzRat hR) GlobalTheory.T.tops_choice

end GlobalTheory.EX
