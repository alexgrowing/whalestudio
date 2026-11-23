import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrEll

theorem star'_star'_of_invol {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e)
    {n : ℕ} (P : PPol σ n) (l : Fld P) : star' P (star' P l) = l := by
  have h : ((star' P : Fld P →+* Fld P).comp (star' P : Fld P →+* Fld P)) = RingHom.id (Fld P) := by
    refine AdjoinRoot.ringHom_ext (p := P.1) ?_ ?_
    · ext e
      change star' P (star' P (algebraMap E (Fld P) e)) = algebraMap E (Fld P) e
      rw [star'_algebraMap, star'_algebraMap, hσ]
    · change star' P (star' P (alpha P)) = alpha P
      rw [star'_alpha, map_inv₀, star'_alpha, inv_inv]
  exact RingHom.congr_fun h l

theorem trace_star'_eq : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (P : PPol σ n) (l : Fld P), Algebra.trace E (Fld P) (star' P l) = σ (Algebra.trace E (Fld P) l) := by
  intro F E _ _ _ σ hσ n P l
  let e₁ : E ≃+* E := RingEquiv.ofRingHom (σ : E →+* E) (σ : E →+* E) (RingHom.ext hσ) (RingHom.ext hσ)
  let e₂ : Fld P ≃+* Fld P := RingEquiv.ofRingHom (star' P : Fld P →+* Fld P) (star' P : Fld P →+* Fld P)
    (RingHom.ext (star'_star'_of_invol hσ P)) (RingHom.ext (star'_star'_of_invol hσ P))
  have he : RingHom.comp (algebraMap E (Fld P)) (e₁ : E →+* E) = RingHom.comp (e₂ : Fld P →+* Fld P) (algebraMap E (Fld P)) := by
    ext e
    exact (star'_algebraMap P e).symm
  have h := Algebra.trace_eq_of_equiv_equiv e₁ e₂ he l
  change _ = σ (Algebra.trace E (Fld P) (star' P l)) at h
  rw [h, hσ]

end GlobalTheory.TrEll
