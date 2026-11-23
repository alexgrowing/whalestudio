import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

namespace GlobalTheory.GramAdj

theorem exists_endo_of_adjoint :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (β : D.La → D.La → ℤ), (∀ x y z, β (x + y) z = β x z + β y z) → (∀ x y z, β x (y + z) = β x y + β x z) → (∀ (s : 𝓞 E) x y, β (s • x) y = β x (H.bar s • y)) → ∃ γ : D.La →+ D.La, (∀ (s : 𝓞 E) x, γ (s • x) = s • γ x) ∧ ∀ x y, β x y = D.EF (γ x) y := by
  intro E _ _ _ H D β hl hr hs
  let f : D.La → (D.La →ₗ[ℤ] ℤ) := fun x => (AddMonoidHom.mk' (β x) (hr x)).toIntLinearMap
  have hf : ∀ x y, f x y = β x y := fun _ _ => rfl
  let e := Equiv.ofBijective D.EF D.unimod
  have he : ∀ g, D.EF (e.symm g) = g := fun g => e.apply_symm_apply g
  have key : ∀ x y, D.EF (e.symm (f x)) y = β x y := fun x y => by rw [he, hf]
  have hadd : ∀ x x', e.symm (f (x + x')) = e.symm (f x) + e.symm (f x') := by
    intro x x'
    apply D.unimod.1
    ext y
    simp only [map_add, LinearMap.add_apply, key, hl]
  refine ⟨AddMonoidHom.mk' (fun x => e.symm (f x)) hadd, ?_, ?_⟩
  · intro s x
    show e.symm (f (s • x)) = s • e.symm (f x)
    apply D.unimod.1
    ext y
    rw [key, hs, ← key, D.adj]
  · intro x y
    show β x y = D.EF (e.symm (f x)) y
    rw [key]

end GlobalTheory.GramAdj
