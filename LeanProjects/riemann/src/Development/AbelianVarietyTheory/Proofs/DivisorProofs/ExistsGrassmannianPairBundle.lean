import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairBundle
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsCokerIsoTr
import Development.AutomorphicArithmetic.DivisorFrames.VectorBundleSubbundleUniversal
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.VB
theorem _root_.GlobalTheory.T.exists_grassmannian_pair_bundle : ∀ (B : Scheme.{0}) (E : B.Modules) (n m₁ m₂ : ℕ), GlobalTheory.VB.IsVB E n → m₁ ≤ m₂ → m₂ ≤ n →
    ∃ (G : Scheme.{0}) (γ : G ⟶ B) (S P : G.Modules) (s : S ⟶ P) (j : P ⟶ (Scheme.Modules.pullback γ).obj E),
      GlobalTheory.VB.IsVB S m₁ ∧ GlobalTheory.VB.IsVB P m₂ ∧ GlobalTheory.VB.IsSubbundle s ∧ GlobalTheory.VB.IsSubbundle j ∧
      GlobalTheory.VB.IsVB (Limits.cokernel j) (n - m₂) ∧ GlobalTheory.OmitFlag.IsPairBundle γ E m₁ m₂ s j :=
  UpperTheory.vector_bundle_subbundle_universal UpperTheory.Grass.exists_grass
