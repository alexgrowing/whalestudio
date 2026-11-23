import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.FinrankKaehlerAffineChart
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.finrank_kaehler_affine_chart : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) [Smooth f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (U : X.Opens) (c : ∀ i, (L i).ι) (hc : ∀ i, U ≤ (L i).U (c i)) (x : X) (K : Type) [Field K] [Algebra Γ(X, U) K], IsAffineOpen U → x ∈ U → (∀ a : Γ(X, U), algebraMap Γ(X, U) K a ≠ 0 ↔ x ∈ X.basicOpen a) → (letI : Algebra R Γ(X, U) := (cstOn f U).toAlgebra; Module.finrank K (K ⊗[Γ(X, U)] Ω[Γ(X, U)⁄R]) = d ∧ LinearIndependent K (fun i : {i : Fin s // algebraMap Γ(X, U) K (resG X (hc i) ((σ i).f (c i))) = 0} => (1 : K) ⊗ₜ[Γ(X, U)] KaehlerDifferential.D R Γ(X, U) (resG X (hc i) ((σ i).f (c i))))) → ∃ C : SncChart f d L σ, x ∈ C.U := by
  first | exact @_root_.GlobalTheory.LogPair.ChartPt.exists_chart | exact _root_.GlobalTheory.LogPair.ChartPt.exists_chart | (intros; apply _root_.GlobalTheory.LogPair.ChartPt.exists_chart <;> assumption)
