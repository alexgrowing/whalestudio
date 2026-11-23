import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem pullHH1_clAll : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (hc : Closed1 (OAff s) = ⊤) (hc' : Closed1 (OAff s') = ⊤) (w : GlobForm s), pullHH1 h (clAll (OAff s) hc w) = clAll (OAff s') hc' (GlobalTheory.CechDR.pullForm h w) := by
  intro R R' _ _ X X' s s' σ φ h hc hc' w
  let ω : ClosedForm s := ⟨w, by rw [show ClosedForm s = ⊤ from hc]; exact Submodule.mem_top⟩
  let ω' : ClosedForm s' := ⟨GlobalTheory.CechDR.pullForm h w, by rw [show ClosedForm s' = ⊤ from hc']; exact Submodule.mem_top⟩
  have e : IsPull1 h (clForm s ω) (clForm s' ω') := IsPullForm.cl (isPullForm_pullForm h w)
  have k : clAll (OAff s) hc w = clForm s ω := rfl
  have k' : clAll (OAff s') hc' (GlobalTheory.CechDR.pullForm h w) = clForm s' ω' := rfl
  rw [k, k']
  exact e.eq_pullHH1.symm

end GlobalTheory.AbCoh
