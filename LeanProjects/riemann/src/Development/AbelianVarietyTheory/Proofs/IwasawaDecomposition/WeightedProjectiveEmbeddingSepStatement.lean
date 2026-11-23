import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightedProjectiveEmbeddingSep
import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_projective_embedding_sep : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R), IsProper f → ∀ (ι : Type) [Fintype ι] (L : ι → LB X) (hL : ∀ i, (L i).IsLB) (M : ι → ℕ) (t : ∀ i, Fin (M i + 1) → (L i).Sec) (ht : ∀ i, ⨆ m, nonzeroLocus (t i m) = ⊤), (∀ (K : Type) [Field K] [IsAlgClosed K] (a a' : Sp K ⟶ X), a ≫ f = a' ≫ f → (∀ i, a ≫ GlobalTheory.ProjSpace.toProj f (t i) (ht i) = a' ≫ GlobalTheory.ProjSpace.toProj f (t i) (ht i)) → a = a') → ∀ (w : ι → ℕ), (∀ i, 1 ≤ w i) → ∀ (N : LB X) (hN : N.IsLB), GlobalTheory.CechPic.cls N hN = ∑ i, w i • GlobalTheory.CechPic.cls (L i) (hL i) → GlobalTheory.IsAmpleLB N := by
  first | exact @GlobalTheory.AmpleSeparateOverRing.isAmpleLB_of_separating | exact GlobalTheory.AmpleSeparateOverRing.isAmpleLB_of_separating | (intros; apply GlobalTheory.AmpleSeparateOverRing.isAmpleLB_of_separating <;> assumption)
