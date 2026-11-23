import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.SpreadingModels

namespace GlobalTheory.CompanionTheory.SpreadingModels

theorem perfAll_of_models
    (hBase : ∀ {R₀ R : Type} [CommRing R₀] [CommRing R] (φ : R₀ →+* R) {Y₀ Y : Scheme.{0}}
      (f₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)) (f : Y ⟶ Spec (CommRingCat.of R)) (π : Y ⟶ Y₀),
      IsPullback π f f₀ (Spec.map (CommRingCat.ofHom φ)) → ∀ (M₀ : LB Y₀), M₀.IsLB → Perf f₀ M₀ →
        Nonempty (Perf f (M₀.pull π)))
    (hIso : ∀ {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) {M M' : LB Y},
      M.IsLB → M'.IsLB → ∀ (w : LB.Iso M M'), w.IsGen → Perf f M' → Nonempty (Perf f M))
    (hModel : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)), Smooth f → IsProper f →
      ∀ M : LB Y, M.IsLB → HasModel f M) : PerfAll := by
  intro R _ Y f hs hp M hM
  obtain ⟨R₀, _, _, φ, Y₀, f₀, π, hp₀, hf₀, hsq, M₀, hM₀, w, hw⟩ := hModel R Y f hs hp M hM
  haveI := hp₀
  haveI := hf₀
  obtain ⟨P₀⟩ := GlobalTheory.ProperFinite.nonempty_perf_of_isProper f₀ hM₀
  obtain ⟨P⟩ := hBase φ f₀ f π hsq M₀ hM₀ P₀
  exact hIso f hM (Geo.Tor.pull_isLB hM₀ π) w hw P

end GlobalTheory.CompanionTheory.SpreadingModels
