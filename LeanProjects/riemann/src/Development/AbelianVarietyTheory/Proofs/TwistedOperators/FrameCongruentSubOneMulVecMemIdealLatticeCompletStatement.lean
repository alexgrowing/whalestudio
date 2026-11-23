import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameCongruentSubOneMulVecMemIdealLatticeComplet
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralBasisCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLatti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameCongruent_sub_one_mulVec_mem_idealLatticeCompletion : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p S n),
  β.IsLat L (Submodule.pi Set.univ fun _ : n => (1 : Submodule 𝒪[k] k)) → ∀ (𝔪 : Ideal (𝓞 D.host.E)) (d : ℕ),
  (∃ m ∈ 𝔪, ∀ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d, ∃ c ∈ 𝒪[k], (z : k) = c * p.pr (incA D ((m : 𝓞 D.host.E) : D.host.E))) →
  ∀ k₀ : GL n 𝒪[k], (∀ i j, (k₀.1 - 1) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d) →
  ∀ y : Fin S.rank → AE D, y ∈ latV S L (· = p.v) →
  (fun i => p.e * ((mt S (β.gl (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)) - 1) *ᵥ y) i) ∈ latV S (𝔪 • L) (· = p.v) := by
  first | exact @GlobalTheory.FinPl.FrameCong.sub_one_mulVec_mem | exact GlobalTheory.FinPl.FrameCong.sub_one_mulVec_mem | (intros; apply GlobalTheory.FinPl.FrameCong.sub_one_mulVec_mem <;> assumption)
