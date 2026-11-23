import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefIsPsEffAndBigTensNef
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory

theorem IsAmpleLB.tens_of_isNef : GlobalTheory.Published.NefNumerics → ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k), IsProjOver f → ∀ A N : LB X, GlobalTheory.IsAmpleLB A → (letI := GlobalTheory.algebraΓOfHom f; GlobalTheory.IsNef k N) → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens A N) := by
  intro h k _ X f hf A N hA hN
  letI := GlobalTheory.algebraΓOfHom f
  refine IsAmpleLB.tens_of_forall_isPsEff k X f hf A N hA hN.isLB fun Z hZ => ?_
  haveI := isIntegral_red hZ
  letI := algebraΓAlong k (redι Z)
  have hi := appTop_algebraMap_along k (redι Z)
  have hp : IsProjOver (strHom k X) := by rwa [strHom_eq (f := f) fun _ => rfl]
  have hp' : IsProjOver (strHom k (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    obtain ⟨n, e, he, hs⟩ := hp
    exact ⟨n, redι Z ≫ e, inferInstance, by rw [Category.assoc, hs, comp_strHom hi]⟩
  exact IsNef.isPsEff h k _ hp' _ (hN.pull_of_isClosedImmersion (redι Z) hi)

end GlobalTheory
