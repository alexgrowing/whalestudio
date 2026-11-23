import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsInfiniteAdelicCharNeOne
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FactorialTendstoZero
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnitaryAnnihilator

open Matrix NumberField IsDedekindDomain GlobalTheory.WeilM MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.AdeleAnn

open GroundTheory.Global

variable {F : Type} [Field F] [NumberField F]

theorem exists_infiniteAdelicChar_ne_one (w : InfinitePlace F) :
    ∃ z : w.Completion, infiniteAdelicChar F w z ≠ 1 :=
  _root_.UpperTheory.Reformulated.B.Rd3.exists_infiniteAdelicChar_ne_one w

theorem eq_zero_of_forall_adelicChar_mul {y : AdeleRing (𝓞 F) F}
    (h : ∀ z, adelicChar F (y * z) = 1) : y = 0 := by
  classical
  refine Prod.ext (α := InfiniteAdeleRing F) (β := FiniteAdeleRing (𝓞 F) F) ?_ ?_
  · funext w
    by_contra hw
    have hw' : y.1 w ≠ 0 := hw
    obtain ⟨z, hz⟩ := exists_infiniteAdelicChar_ne_one w
    apply hz
    rw [infiniteAdelicChar_apply', ← h (infinitePlaceIncl w ((y.1 w)⁻¹ * z))]
    congr 1
    refine Prod.ext (α := InfiniteAdeleRing F) (β := FiniteAdeleRing (𝓞 F) F) ?_ ?_
    · funext u
      change (infinitePlaceIncl w z).1 u = y.1 u * (infinitePlaceIncl w ((y.1 w)⁻¹ * z)).1 u
      rw [infinitePlaceIncl_fst, infinitePlaceIncl_fst]
      by_cases hu : u = w
      · subst hu
        rw [Pi.single_eq_same, Pi.single_eq_same, mul_inv_cancel_left₀ hw']
      · rw [Pi.single_eq_of_ne hu, Pi.single_eq_of_ne hu, mul_zero]
    · rw [adeleRing_mul_snd, infinitePlaceIncl_snd, infinitePlaceIncl_snd, mul_zero]
  · refine Subtype.ext (funext fun v => ?_)
    by_contra hv
    have hv' : y.2 v ≠ 0 := hv
    apply localAdelicChar_ne_one (K := F) v
    refine DFunLike.ext _ _ fun z => ?_
    rw [AddChar.one_apply, localAdelicChar_apply, ← h (finitePlaceIncl v ((y.2 v)⁻¹ * z))]
    congr 1
    refine Prod.ext (α := InfiniteAdeleRing F) (β := FiniteAdeleRing (𝓞 F) F) ?_ ?_
    · rw [adeleRing_mul_fst, finitePlaceIncl_apply, finitePlaceIncl_apply, finiteAdeleInr_fst,
        finiteAdeleInr_fst, mul_zero]
    · refine Subtype.ext (funext fun u => ?_)
      change finiteAdeleSingleAdd v z u = y.2 u * finiteAdeleSingleAdd v ((y.2 v)⁻¹ * z) u
      by_cases hu : u = v
      · subst hu
        rw [finiteAdeleSingleAdd_apply_self, finiteAdeleSingleAdd_apply_self,
          mul_inv_cancel_left₀ hv']
      · rw [finiteAdeleSingleAdd_apply_of_ne hu, finiteAdeleSingleAdd_apply_of_ne hu, mul_zero]

theorem norm_eq_one (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hc : Continuous ψ)
    (hF : ∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) (x : AdeleRing (𝓞 F) F) :
    ‖ψ x‖ = 1 :=
  _root_.UpperTheory.Reformulated.B.AdelicCharacterNormOne.norm_eq_one ψ hc hF x

theorem unitary_and_annihilator_eq : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), Continuous ψ → ψ ≠ 1 → (∀ a : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) a) = 1) → (∀ x, ‖ψ x‖ = 1) ∧ ∀ x : AdeleRing (𝓞 F) F, (∀ a : F, ψ (x * algebraMap F (AdeleRing (𝓞 F) F) a) = 1) → ∃ b : F, x = algebraMap F (AdeleRing (𝓞 F) F) b :=
  _root_.UpperTheory.Reformulated.B.UnitaryAnnihilator.unitary_and_annihilator_eq

end GlobalTheory.CompanionTheory.AdeleAnn
