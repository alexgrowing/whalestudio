import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KernelFiniteFlatHolds
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGrpObjOfFlatClosed
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem kernel_finiteFlat_subgroup : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L → ∃ (H : Over (Sp R)) (_ : GrpObj H)
    (i : H ⟶ A), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Flat H.hom ∧
    ∀ (T : Over (Sp R)) (x : T ⟶ A), GlobalTheory.MemKL A L x ↔ ∃ z : T ⟶ H, z ≫ i = x := by
  intro R _ _ A _ hA L hL ha
  obtain ⟨Z, i, hci, hfin, hflat, hZ⟩ := GlobalTheory.kernelFiniteFlat_holds R A hA L hL ha
  haveI : IsClosedImmersion i.left := hci
  have hmono : Mono i := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono i.left))
  have hmem : ∀ (T : Over (Sp R)) (z : T ⟶ Z), GlobalTheory.MemKL A L (z ≫ i) := fun T z => (hZ T _).2 ⟨z, rfl⟩
  have e1 : (1 : 𝟙_ (Over (Sp R)) ⟶ A) = η[A] := by
    show toUnit _ ≫ η[A] = η[A]
    rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  obtain ⟨o, ho⟩ := (hZ _ η[A]).1 (e1 ▸ memKL_one hL _)
  have e2 : (i ⊗ₘ i) ≫ μ[A] = (fst Z Z ≫ i) * (snd Z Z ≫ i) := by
    show (i ⊗ₘ i) ≫ μ[A] = lift (fst Z Z ≫ i) (snd Z Z ≫ i) ≫ μ[A]
    rw [lift_fst_comp_snd_comp]
  obtain ⟨m, hm⟩ := (hZ _ ((i ⊗ₘ i) ≫ μ[A])).1 (e2 ▸ GlobalTheory.UU.InK.mul hL (hmem _ _) (hmem _ _))
  have e3 : i ≫ GrpObj.inv = (𝟙 Z ≫ i)⁻¹ := by
    rw [Category.id_comp]; rfl
  obtain ⟨n, hn⟩ := (hZ _ (i ≫ GrpObj.inv)).1 (e3 ▸ GlobalTheory.UU.InK.inv hL (hmem _ _))
  obtain ⟨G, hG⟩ := GlobalTheory.exists_grpObj_of_mono i o m n ho hm hn
  exact ⟨Z, G, i, hG, hmono, hfin, hflat, hZ⟩

end GlobalTheory
