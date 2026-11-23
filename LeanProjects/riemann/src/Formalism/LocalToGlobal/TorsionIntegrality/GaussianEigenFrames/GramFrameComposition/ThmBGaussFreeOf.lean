import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementD
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OneLetterGaussSharpTranslateHolds
import Formalism.GaussJetBounds.FinalB
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.H (cmL CmOK matH stdH stdLat blk4 pow4 imgLat relIdx IsIsom IsSelfDual Th alphaQ kernel4 TransInt
  opU taylorMv)
open Formalism.L2.Th1.Top (IsLatH phC)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer expSer)
open Formalism.L2.Th1.G (linSub toZ phSum betaPair)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair jetPairPoly minorProd)

namespace GramFrameLocalizationLemmas

theorem data {a₀ : ℕ} {b₀ c₀ : ℤ} {dK : ℕ} (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0)
    (hcm : CmOK a₀ b₀ c₀ dK) :
    Squarefree dK ∧ dK % 4 = 3 ∧ Formalism.L2.Th1.CM.HasCMBy dK (cmL a₀ b₀ dK ha hdK lam hlam) := by
  obtain ⟨h4, -, h8, hp⟩ := hcm

  have hb : Odd b₀ := by
    rcases Int.even_or_odd b₀ with ⟨k, hk⟩ | hk
    · exfalso
      subst hk
      have h4' : (dK : ℤ) = 4 * ((a₀ : ℤ) * c₀ - k * k) := by linear_combination (-1 : ℤ) * h4
      obtain ⟨m, hm⟩ : (4 : ℤ) ∣ (dK : ℤ) := ⟨_, h4'⟩
      omega
    · exact hk
  refine ⟨(Nat.prime_iff.mp hp).squarefree, by omega, ?_⟩
  exact Formalism.L2.Th1.F.hasCMByScale dK _ lam hlam
    (Formalism.L2.Th1.F.cmPairHasCMBy a₀ b₀ c₀ dK ha hdK h4 hb)

end GramFrameLocalizationLemmas

open GramFrameLocalizationLemmas Formalism.L2.Th1.Top.CAux

end Formalism.L2.Th1.GD
