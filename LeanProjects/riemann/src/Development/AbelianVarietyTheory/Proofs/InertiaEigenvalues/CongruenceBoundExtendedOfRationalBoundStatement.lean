import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceBoundExtendedOfRationalBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruenceBound_extended_of_rationalBound : ∀ (D : D7) (i : D.nd.Loc) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), π ∈ D.nd.Z i → (∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1) → (Br.sFin D.loc D.nbr i (fun _ => ρ) π → (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) → D.nd.vcc i π ≤ Br.sPi D.loc D.nbr i (fun _ => ρ) π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) + (padicValNat (D.nd.l i) (hE D.host) : ℚ) + (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1})) → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.vCC D i π ≤ GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.sPi D i π ρ + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.shaSum D i + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.vClass D i + GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.epsQ D i := by
  first | exact @GlobalTheory.Proof.congruenceBound_extended_of_rationalBound.congBound_of_rational | exact GlobalTheory.Proof.congruenceBound_extended_of_rationalBound.congBound_of_rational | (intros; apply GlobalTheory.Proof.congruenceBound_extended_of_rationalBound.congBound_of_rational <;> assumption)
