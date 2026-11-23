import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleTransportAlongIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleBaseChangeAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackFreeModuleIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleLocalTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalFlagBundleExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleGluesFromCoverStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

namespace GlobalTheory.FlagExist

theorem main : ∀ (B : Scheme.{0}) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl := by
  intro B ι _ E r hE
  refine GlobalTheory.T.flag_bundle_glues_from_cover B ι E r hE fun x => ?_
  obtain ⟨U, hx, hU⟩ := GlobalTheory.T.vector_bundle_local_trivial B ι E r hE x
  have e := fun a => Classical.choice (hU a)
  obtain ⟨Y, π, fl, h⟩ := GlobalTheory.T.universal_flag_bundle_exists ι r
  let g : U.toScheme ⟶ Sp ℤ := U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Int.castRingHom _))
  have h1 := GlobalTheory.T.isFlagBundle_pullback' _ _ _ π g ι _ r fl h
  have f := fun a => Classical.choice (GlobalTheory.T.pullback_free_module_iso U.toScheme (Sp ℤ) g (r a))
  exact ⟨U, hx, _, _, _, GlobalTheory.T.flag_bundle_transport_along_iso _ _ _ ι _ (fun a => (Scheme.Modules.pullback U.ι).obj (E a)) r _ (fun a => f a ≪≫ (e a).symm) h1⟩

end GlobalTheory.FlagExist
