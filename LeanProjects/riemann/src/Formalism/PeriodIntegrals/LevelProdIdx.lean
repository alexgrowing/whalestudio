import Mathlib
import Formalism.SatakeDualWeyl.StatementC

open Matrix NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace PI

open Formalism.UG in
def LevelProdIdx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Lb : Submodule (𝓞 E) (Fin n → E))
    (Uloc : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GL (Fin n) (E ⊗[F] v.adicCompletion F)))
    (U : Subgroup (GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))),
    Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin n → E)) = ⊤ →
    (∀ x, x ∈ U ↔ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) x ∈ Uloc v) →
    (∀ v, Uloc v ≤ levelVL σ J v Lb) →
    {v | Uloc v ≠ levelVL σ J v Lb}.Finite →
    (∀ v, (Uloc v).relIndex (levelVL σ J v Lb) ≠ 0) →
    U ≤ levelAfL σ J Lb ∧ U.relIndex (levelAfL σ J Lb) ≠ 0

end PI
