import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem injective_of_flat_of_range_subset_genericPoints :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (X : Scheme.{0}) (s : X ⟶ Sp R) (x : Sp K ⟶ X) (β : R →+* K), Flat s → Set.range x ⊆ genericPoints X → x ≫ s = spMap β → Function.Injective β := by
  intro R K _ _ _ X s x β hs hx hxs
  set pt : Sp K := IsLocalRing.closedPoint K with hpt
  have hp : x pt ∈ genericPoints X := hx ⟨_, rfl⟩
  let g₀ : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  have hg₀ : g₀ ⤳ s (x pt) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨y, hy, e⟩ := Flat.generalizingMap s hg₀
  have h₁ : closure ({x pt} : Set X) ⊆ closure {y} :=
    specializes_iff_closure_subset.mp hy
  have h₂ : closure ({y} : Set X) ⊆ closure {x pt} :=
    hp.2 isIrreducible_singleton.closure h₁
  have hyx : y = x pt :=
    (hy.antisymm (specializes_iff_closure_subset.mpr h₂)).eq
  have h₃ : (x ≫ s) pt = g₀ := by
    rw [Scheme.Hom.comp_apply, ← hyx, e]
  rw [hxs] at h₃
  have h₄ : (spMap β pt).asIdeal = RingHom.ker β := by
    show Ideal.comap β (IsLocalRing.maximalIdeal K) = _
    rw [IsLocalRing.maximalIdeal_eq_bot]
    rfl
  rw [h₃] at h₄
  exact (RingHom.injective_iff_ker_eq_bot β).mpr h₄.symm

end GlobalTheory
