import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndependenceFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndependenceGenericOfSpecialStatement

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LN GlobalTheory.TorRef
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorRef

theorem exists_valuationSubring_factor (R : Type) [CommRing R] [IsLocalRing R] (k : Type) [Field k] (φ : R →+* k) :
    ∃ (V : ValuationSubring k) (g : R →+* V), IsLocalHom g ∧ V.subtype.comp g = φ := by
  obtain ⟨A, h, hl⟩ := IsLocalRing.exists_factor_valuationRing φ
  exact ⟨A, φ.codRestrict A.toSubring h, hl, by ext x; rfl⟩

theorem indepSpreadSt : IndepSpreadSt := by
  intro E _ _ _ H R _ _ t N n b hres k _ φ
  obtain ⟨V, g, hg, hφ⟩ := exists_valuationSubring_factor R k φ
  have hF : Flat t.G.hom := by
    have := t.semi.smooth
    infer_instance
  have h1 := GlobalTheory.T.independence_field_extension R t.G t.PP.L N n b _ _ (residue R) (ResidueField.map g) t.PP.isLB hres
  rw [ResidueField.map_comp_residue] at h1
  have h2 := GlobalTheory.T.independence_generic_of_special R t.G t.PP.L N n b k V g hF t.PP.isLB h1
  rwa [hφ] at h2

end GlobalTheory.TorRef
