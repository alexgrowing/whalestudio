import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrankStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_factor_of_isogeny : ∀ (K : Type) [Field K] (A B C : AbVar K) (q : A ⟶ B) (f : A ⟶ C), IsIsogeny q → (∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ q.hom = 1 → x ≫ f.hom = 1) → ∃ g : B ⟶ C, q ≫ g = f := by
  intro K _ A B C q f hq hker
  have hflat : Flat q.hom.left := (GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B q hq).2.1
  have hfin : IsFinite q.hom.left := hq.1
  have hsurj : Surjective q.hom.left := hq.2
  have hqc : QuasiCompact q.hom.left := inferInstance
  obtain ⟨⟨ψ, hψ, hc⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ A.X B.X C.X q.hom f.hom
    inferInstance inferInstance hflat hsurj hqc hker
  exact ⟨Hom.mk ψ, hom_ext (by simpa using hc)⟩

end GlobalTheory.AV.AbVar
