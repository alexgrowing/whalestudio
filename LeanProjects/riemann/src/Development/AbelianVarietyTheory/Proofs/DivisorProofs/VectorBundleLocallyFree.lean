import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

namespace GlobalTheory.VB

theorem exists_open_isVB_free_finite (B : Scheme.{0}) (ι : Type) [Finite ι] (E : ι → B.Modules) (r : ι → ℕ) :
    (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → ∀ b : B, ∃ U : B.Opens, b ∈ U ∧ ∀ a,
      Nonempty ((Scheme.Modules.pullback U.ι).obj (E a) ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin (r a))) := by
  intro hE b
  have := Fintype.ofFinite ι
  choose V e hb he using fun a => hE a b
  refine ⟨Finset.univ.inf V, ?_, fun a => ?_⟩
  · rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_finset_inf]
    simpa using hb
  · have hle : Finset.univ.inf V ≤ V a := Finset.inf_le (Finset.mem_univ a)
    set U := Finset.univ.inf V
    have hU : U.ι ''ᵁ ⊤ ≤ V a := (U.ι_image_le ⊤).trans hle
    exact ⟨((Scheme.Modules.restrictFunctorIsoPullback U.ι).app (E a)).symm ≪≫
      ((GlobalTheory.VB.isFrame_freeFrame U.toScheme (Fin (r a))).iso
        ((GlobalTheory.VB.isFrame_restrict_iff U.ι _).2 ((he a).res hU))).symm⟩

end GlobalTheory.VB
