import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory

theorem ringHom_integers_injective_of_charZero :
    ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K]
    (χ : 𝓞 E →+* K), Function.Injective χ := by
  intro E _ _ K _ _ χ
  rw [injective_iff_map_eq_zero]
  intro o ho
  by_contra hne
  have hdvd := Algebra.dvd_algebraMap_intNorm_self ℤ (𝓞 E) o
  have hn : Algebra.intNorm ℤ (𝓞 E) o ≠ 0 := Algebra.intNorm_ne_zero.mpr hne
  have h2 := map_dvd χ hdvd
  rw [ho, zero_dvd_iff] at h2
  have h3 : χ (algebraMap ℤ (𝓞 E) (Algebra.intNorm ℤ (𝓞 E) o)) = ((Algebra.intNorm ℤ (𝓞 E) o : ℤ) : K) := by
    simp
  rw [h3] at h2
  exact hn (by exact_mod_cast h2)

end GlobalTheory
