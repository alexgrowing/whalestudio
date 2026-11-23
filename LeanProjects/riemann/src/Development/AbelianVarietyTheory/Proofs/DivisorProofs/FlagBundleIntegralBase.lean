import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProjectionSurjective
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.VB

open GlobalTheory.QCoh

namespace GlobalTheory.FlagBase

theorem isIntegral_base : ∀ (Y Y₁ : Scheme.{0}) (ρ : Y ⟶ Y₁) (E₁ : Y₁.Modules)
    (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2),
    IsIntegral Y → GlobalTheory.VB.IsVB E₁ 2 → IsFlagBundle ρ (fun _ : Unit => E₁) (fun _ => 2) (fun _ => fl₁) →
      IsIntegral Y₁ := by
  intro Y Y₁ ρ E₁ fl₁ hY hE hfl
  have hsurj : Function.Surjective ρ :=
    GlobalTheory.FlagSurj.isFlagBundle_surjective Y₁ Y ρ Unit (fun _ => E₁) (fun _ => 2) (fun _ => fl₁) (fun _ => hE) hfl
  have : IrreducibleSpace Y₁ := Function.Surjective.irreducibleSpace ρ.continuous hsurj
  have : IsReduced Y₁ := by
    refine @isReduced_of_isReduced_stalk Y₁ ?_
    intro x
    obtain ⟨U, e, hb, he⟩ := hE x
    have hfr := (isFrame_restrict_iff U.ι _).2 (he.res (U.ι_image_le ⊤))
    let φ : freeModule U.toScheme (Fin 2) ≅ (Scheme.Modules.pullback U.ι).obj E₁ :=
      (isFrame_freeFrame _ _).iso hfr ≪≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).app E₁
    obtain ⟨g', ⟨w, -⟩, -⟩ := hfl U.toScheme U.ι (fun _ => (GlobalTheory.FlagSurj.freeFlag U.toScheme 2).ofIso φ)
    let x' : U.toScheme := ⟨x, hb⟩
    have hopen : IsOpenImmersion (g' ≫ ρ) := w ▸ inferInstance
    have hiso : IsIso ((g' ≫ ρ).stalkMap x') := (IsOpenImmersion.iff_isIso_stalkMap.1 hopen).2 x'
    have h1 : Function.Injective ((g' ≫ ρ).stalkMap x').hom :=
      (ConcreteCategory.bijective_of_isIso ((g' ≫ ρ).stalkMap x')).1
    rw [Scheme.Hom.stalkMap_comp] at h1
    have hinj : Function.Injective (ρ.stalkMap (g' x')).hom :=
      Function.Injective.of_comp (f := (g'.stalkMap x').hom) h1
    have hred : _root_.IsReduced (Y₁.presheaf.stalk (ρ (g' x'))) := isReduced_of_injective _ hinj
    have hx : ρ (g' x') = x := by
      have h : (g' ≫ ρ) x' = U.ι x' := by rw [w]
      exact (Scheme.Hom.comp_apply g' ρ _).symm.trans (h.trans (Scheme.Opens.ι_apply U _))
    exact hx ▸ hred
  exact isIntegral_of_irreducibleSpace_of_isReduced Y₁

end GlobalTheory.FlagBase
