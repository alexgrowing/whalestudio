import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicGLInductionOverPlaces
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteOfTrivOutside
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruenceElementDecompose
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicGL_induction_over_places : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (N : ℕ), 0 < N → ∀ p : GAf L n → Prop, (∀ κ, NG.Cong L n N κ → p κ) → (∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n), TrivOutside {v} x → TrivOutside {v}ᶜ y → p y → p (x * y)) → ∀ g, p g := by
  first | exact @GlobalTheory.PlaceInd.induction_places | exact GlobalTheory.PlaceInd.induction_places | (intros; apply GlobalTheory.PlaceInd.induction_places <;> assumption)
