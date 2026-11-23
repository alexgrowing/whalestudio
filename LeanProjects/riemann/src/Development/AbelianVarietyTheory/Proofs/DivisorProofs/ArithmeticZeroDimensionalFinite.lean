import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
open CategoryTheory AlgebraicGeometry GlobalTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem IsArithVar.moduleFinite_int_of_spec : ∀ (k : Type) [CommRing k] (k' : Type) [CommRing k'] [IsDomain k'] [Algebra k k'],
    IsArithVar (spMap (algebraMap k k')) 0 → Module.Finite ℤ k' := by
  intro k _ k' _ _ _ hX
  obtain ⟨N, j, _, hj⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper (spMap (algebraMap k k')) := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
  have hf : IsFinite (spMap (algebraMap k k') ≫ spMap (Int.castRingHom k)) :=
    IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  rw [← Spec.map_preimage (spMap (algebraMap k k') ≫ _), IsFinite.SpecMap_iff,
    RingHom.ext_int (Spec.preimage (spMap (algebraMap k k') ≫ spMap (Int.castRingHom k))).hom
      (algebraMap ℤ k'), RingHom.finite_algebraMap] at hf
  exact hf

end GlobalTheory
