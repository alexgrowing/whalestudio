import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CoefRestrictSmallCoverInjectiveStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.PdChern

theorem restrict_triv_eq_zero : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (L : LB X), L.IsLB → ∀ z : SecondDeRham s, IsChern (dp0 R) s L z → (CoefMap.restrict (O (dp0 R) s) (IsTriv s).ι).pull2 z = 0 := by
  intro R _ X s L hL z hz
  obtain ⟨i, hi, u, ℓ, -, hℓ, hz⟩ := hz
  obtain ⟨c, rfl⟩ := H2.mk_surjective _ z
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hz
  obtain ⟨f, hf⟩ := hz
  apply GlobalTheory.T.coef_restrict_small_cover_injective R X s L.ι L.U hL.cover
  rw [map_zero, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero]
  let P : ObjectProperty (IsTriv s).FullSubcategory :=
    fun T : (IsTriv s).FullSubcategory => IsSmall (dp0 R) s L.U T.obj
  let F : P.FullSubcategory ⥤ (IsSmall (dp0 R) s L.U).FullSubcategory :=
    ObjectProperty.lift _ (P.ι ⋙ (IsTriv s).ι) (fun T => T.property)
  refine ⟨fun T T' φ => f (F.obj T) (F.obj T') (F.map φ), ?_⟩
  funext T T' T'' φ ψ
  have h := congrFun (congrFun (congrFun (congrFun (congrFun hf (F.obj T)) (F.obj T'))
    (F.obj T'')) (F.map φ)) (F.map ψ)
  have h0 : (ℓ.1 (F.obj T) (F.obj T') (F.obj T'') (F.map φ) (F.map ψ) : T''.obj.obj.B) = 0 := by
    have hm : (ℓ.1 (F.obj T) (F.obj T') (F.obj T'') (F.map φ) (F.map ψ) : T''.obj.obj.B) ∈
      T''.obj.obj.J := (hℓ (F.obj T) (F.obj T') (F.obj T'') (F.map φ) (F.map ψ)).1
    have e : T''.obj.obj.J = ⊥ := T''.obj.property
    rw [e] at hm
    exact Ideal.mem_bot.1 hm
  exact h.trans (sub_eq_self.2 h0)

end GlobalTheory.CompanionTheory.PdChern
