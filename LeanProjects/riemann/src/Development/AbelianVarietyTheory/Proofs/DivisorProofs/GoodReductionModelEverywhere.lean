import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGlobalModelGoodLevelAllPrimes
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValuationExtension

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory.FlatDegreeCompare

theorem hasModel_of_goodAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (k : Type) [Field k] [NumberField k] (j : c.F →+* k) (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom)), 1 ≤ D.p + D.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → ∀ 𝔭 : HeightOneSpectrum (𝓞 k), HasModel o.t 𝔭 := by
  intro E _ _ _ H D l c k _ _ j o e hg hA 𝔭
  obtain ⟨Xo⟩ := Moduli.moduli_scheme_exists E H D l e
  obtain ⟨f, ⟨hf, ⟨m⟩⟩, -⟩ := Xo.rep _ _ inferInstance o
  obtain ⟨Y⟩ := (GlobalTheory.Reg.modelAt_and_nonempty_global_model E H D l Xo c e hg hA).2
  let y : Sp k ⟶ Xo.XF c := pullback.lift f (spMap j) hf
  have hy : y ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  let oV : 𝓞 c.F →+* AdelicDegreeTameRamification.valRing k 𝔭 :=
    (j.comp (algebraMap (𝓞 c.F) c.F)).codRestrict (AdelicDegreeTameRamification.valRing k 𝔭) fun a =>
      𝔭.valuation_le_one (K := k) (RingOfIntegers.mapRingHom j a)
  obtain ⟨⟨yt, ⟨-, hyt⟩, -⟩, h⟩ := ValuativeExtension.valuation_extension E H D l Xo c _ _ Y
    (AdelicDegreeTameRamification.valRing k 𝔭) k oV j y rfl (pullback.lift_snd _ _ _)
  obtain ⟨G, ⟨n⟩⟩ := h yt
  obtain ⟨m₁, -⟩ := ObjMaps.exists_sab_cancel (g := y) Y.m0.toSABMap (hy ▸ m.toSABMap)
  obtain ⟨m₂, -⟩ := ObjMaps.exists_sab_comp Y.m m₁
  obtain ⟨m₃, -⟩ := ObjMaps.exists_sab_cancel (g := spMap (algebraMap (AdelicDegreeTameRamification.valRing k 𝔭) k)) n (hyt ▸ m₂)
  exact ⟨G.G, inferInstance, m₃.φ, G.semi, m₃.cart⟩

end GlobalTheory.FlatDegreeCompare
