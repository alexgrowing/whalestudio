import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleUniqueUpToIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEachStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagBundleProjVectorBundleStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

namespace GlobalTheory.FlagProj

theorem isProjOver_of_isFlagBundle : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsProjOver q → (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → IsProjOver (π ≫ q) := by
  intro k _ _ B Y q π ι _ E r fl hq hE hY
  obtain ⟨Y₀, π₀, fl₀, h₀, hp₀⟩ := GlobalTheory.T.flag_bundle_product_of_each k B q ι E r hq fun a => GlobalTheory.T.exists_flag_bundle_proj_vector_bundle k B q (E a) (r a) hq (hE a)
  obtain ⟨e, he⟩ := GlobalTheory.T.flag_bundle_unique_up_to_iso B Y Y₀ π π₀ ι E r fl fl₀ hY h₀
  obtain ⟨N, φ, hφ, w⟩ := hp₀
  exact ⟨N, e.hom ≫ φ, inferInstance, by rw [Category.assoc, w, ← Category.assoc, he]⟩

end GlobalTheory.FlagProj
