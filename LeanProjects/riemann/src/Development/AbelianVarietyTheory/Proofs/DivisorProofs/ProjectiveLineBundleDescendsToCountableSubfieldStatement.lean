import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLineBundleDescendsToCountableSubfield
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projectiveLineBundle_descends_to_countable_subfield : ∀ (K : Type) [Field K] (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∀ (L : LB X), L.IsLB → ∃ (K₁ : Subfield K) (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (ψ : X ⟶ X₁) (L₁ : LB X₁), Countable K₁ ∧ IsProjOver p₁ ∧ IsPullback ψ p p₁ (spMap (algebraMap K₁ K)) ∧ L₁.IsLB ∧ LBIso L (L₁.pull ψ) := by
  first | exact @GlobalTheory.ProjCountableDescent.projLB_descends_to_countable_subfield | exact GlobalTheory.ProjCountableDescent.projLB_descends_to_countable_subfield | (intros; apply GlobalTheory.ProjCountableDescent.projLB_descends_to_countable_subfield <;> assumption)
