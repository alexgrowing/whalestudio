import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRepresentativesOfSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_representatives_of_support : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) (α : GA D V), IsPrimeIdem P e f → SuppF V f α → ∃ R : Finset (GA D V), (∀ γ ∈ R, SuppF V f γ) ∧ IsCosetRep V {k | k ∈ KsphC V ∅ ∧ SuppF V f k} α R := by
  first | exact @GlobalTheory.LocalReps.exists_isCosetRep | exact GlobalTheory.LocalReps.exists_isCosetRep | (intros; apply GlobalTheory.LocalReps.exists_isCosetRep <;> assumption)
