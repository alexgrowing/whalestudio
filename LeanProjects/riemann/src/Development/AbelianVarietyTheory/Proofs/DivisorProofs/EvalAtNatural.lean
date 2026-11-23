import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EvalNat

theorem evalAt_natural : ∀ {X : Scheme.{0}} {C C' : Type} [CommRing C] [CommRing C'] (φ : C →+* C') (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U), ∃ h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U, (∀ f : Γ(X, U), evalAt (spMap φ ≫ x) U h' f = φ (evalAt x U h f)) ∧ ∀ (U' : X.Opens) (i : U ≤ U') (h'' : ⊤ ≤ x ⁻¹ᵁ U') (f : Γ(X, U')), evalAt x U' h'' f = evalAt x U h ((X.presheaf.map (homOfLE i).op).hom f) := by
  intro X C C' _ _ φ x U h
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun p _ ↦ h (Set.mem_univ ((spMap φ) p))
  refine ⟨h', fun f ↦ ?_, fun U' i h'' f ↦ ?_⟩
  · have e : (spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of C')).hom =
        x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom ≫ CommRingCat.ofHom φ := by
      rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc,
        ← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]
      congr 2
    exact congrArg (fun t ↦ t.hom f) e
  · have e : x.appLE U' ⊤ h'' = X.presheaf.map (homOfLE i).op ≫ x.appLE U ⊤ h := by
      rw [Scheme.Hom.map_appLE]
    unfold evalAt
    rw [e]
    rfl

end GlobalTheory.EvalNat
