import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFlag
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

theorem GlobalTheory.VB.exists_common_trivialization : ∀ (B : Scheme.{0}) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → ∀ x : B, ∃ U : B.Opens, x ∈ U ∧ ∀ a, Nonempty ((Scheme.Modules.pullback U.ι).obj (E a) ≅ GlobalTheory.QCoh.freeModule (X := U.toScheme) (Fin (r a))) := by
  intro B ι _ E r hE x
  choose U e hx he using fun a => hE a x
  let V : B.Opens := Finset.univ.inf U
  have hxV : x ∈ V := by
    show x ∈ ((Finset.univ.inf U : B.Opens) : Set B)
    rw [TopologicalSpace.Opens.coe_finset_inf]; simpa using hx
  have hV (a : ι) : V ≤ U a := Finset.inf_le (Finset.mem_univ a)
  refine ⟨V, hxV, fun a => ⟨?_⟩⟩
  have hle : V.ι ''ᵁ ⊤ ≤ U a := (V.ι_image_le ⊤).trans (hV a)
  exact ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app (E a)).symm ≪≫
    ((GlobalTheory.VB.isFrame_freeFrame _ _).iso
      ((GlobalTheory.VB.isFrame_restrict_iff V.ι _).2 ((he a).res hle))).symm
