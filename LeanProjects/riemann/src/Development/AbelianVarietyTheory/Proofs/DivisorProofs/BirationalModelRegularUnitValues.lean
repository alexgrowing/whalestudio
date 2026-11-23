import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem model_regAt_unitAt_values : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → (∀ (y : Y) (f : X.functionField), RegAt (π y) f → RegAt y (φ f)) ∧ (∀ (y : Y) (f : X.functionField), UnitAt (π y) f → UnitAt y (φ f)) ∧ (∀ (U : X.Opens) (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ π ⁻¹ᵁ U) (a : Γ(X, U)), φ (fnOf U h a) = fnOf (π ⁻¹ᵁ U) h' (π.app U a)) ∧ ∀ (σ : k →+* ℂ) (z : CxPts q σ) (f : X.functionField), RegAt (π (under z)) f → ratVal (φ f) z = ratVal f (GlobalTheory.Points.PtsOver.map π hπ _ z) := by
  intro k _ X Y _ _ p q π hπ φ hM
  have h3 : ∀ (U : X.Opens) (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ π ⁻¹ᵁ U) (a : Γ(X, U)),
      φ (fnOf U h a) = fnOf (π ⁻¹ᵁ U) h' (π.app U a) := by
    intro U h h' a
    have e1 := algebraMap_germ (X := X) (show π (genericPoint Y) ∈ U from h') a
    have e2 := algebraMap_germ (X := Y) h' (π.app U a)
    rw [← e1, hM.compat, ← e2]
    congr 1
    exact Scheme.Hom.germ_stalkMap_apply π U (genericPoint Y) h' a
  refine ⟨?_, ?_, h3, ?_⟩
  · rintro y f ⟨a, rfl⟩
    exact ⟨π.stalkMap y a, (hM.compat y a).symm⟩
  · rintro y f ⟨a, ha, rfl⟩
    exact ⟨π.stalkMap y a, ha.map _, (hM.compat y a).symm⟩
  · intro σ z f hf
    obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
    have hz : z ∈ ptsIn q σ (π ⁻¹ᵁ U) := mem_ptsIn.2 hU
    have hz' : GlobalTheory.Points.PtsOver.map π hπ _ z ∈ ptsIn p σ U := mem_ptsIn.2 (by first | exact hU | simpa [Function.comp_apply] using hU)
    rw [h3 U _ (gen_mem (show under z ∈ π ⁻¹ᵁ U from hU)) a, ratVal_fnOf hz, ratVal_fnOf hz',
      ev_app π hπ]

end GlobalTheory.HSNef
