import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.CasselmanShalikaStandardVector
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GluePlaces
import GroundTheory.GlobalFields.SemilocalAlgebras.NormTrace
import GroundTheory.GlobalFields.SemilocalAlgebras.Finite
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.StdThetaExists

variable {K : Type} [Field K] [NumberField K]

theorem finrank_eq_two_of_unique (h2 : Module.finrank ℚ K = 2) (v : Pl) (w : PlK K)
    [i : w.asIdeal.LiesOver v.asIdeal] (hu : ∀ w' : PlK K, w'.asIdeal.LiesOver v.asIdeal → w' = w) :
    Module.finrank (Qv v) (Kv K w) = 2 := by
  haveI : Unique (SemiLocal.PlacesOver K v) := ⟨⟨⟨w, i⟩⟩, fun x => Subtype.ext (hu x.1 x.2)⟩
  have hs := (SemiLocal.sum_finrank_eq K v).trans h2
  rw [Fintype.sum_unique] at hs
  have : (default : SemiLocal.PlacesOver K v) = ⟨w, i⟩ := Subsingleton.elim _ _
  rw [this] at hs
  exact hs

end GlobalTheory.CompanionTheory.StdThetaExists
