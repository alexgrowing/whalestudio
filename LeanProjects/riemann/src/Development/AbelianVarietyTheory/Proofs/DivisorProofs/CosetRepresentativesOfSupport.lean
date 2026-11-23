import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankWeightComponentEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOperatorOffDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommuteAtSubgroup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult Formalism.IndefR.Links GlobalTheory.SphPar
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.LocalReps.exists_isCosetRep : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) (α : GA D V), IsPrimeIdem P e f → SuppF V f α → ∃ R : Finset (GA D V), (∀ γ ∈ R, SuppF V f γ) ∧ IsCosetRep V {k | k ∈ KsphC V ∅ ∧ SuppF V f k} α R := by
  intro D V P e f α hP hα
  rcases id hP with ⟨he, rfl⟩ | ⟨rfl, -⟩
  · exact (GlobalTheory.SplitPlace.split_local V P e he).2.1 α hα
  · exact (GlobalTheory.InertDoubleCoset.inert_double_cosets V P f hP
      (GlobalTheory.SphericalComm.exists_unif_of_not_dvd P (GlobalTheory.HeckeOrthSum.not_dvd_different D P)) α hα).2.1
