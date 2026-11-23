import Mathlib
import Formalism.LocalToGlobal.Columns.GoodXgFin

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV

section E

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [CharZero K]

def XgESet (σ : K →+* ℂ) (e : MonoidAlgebra ℂ G) : Set (G → K) :=
  {χ | IsAbsIrrChar χ ∧ ∑ g : G, e.coeff g * σ (χ g) = σ (χ 1)}

theorem XgESet_finite (σ : K →+* ℂ) (e : MonoidAlgebra ℂ G) : (XgESet σ e).Finite :=
  (absIrrChar_finite (G := G) (K := K)).subset fun _ h => h.1

def XgE (σ : K →+* ℂ) (e : MonoidAlgebra ℂ G) : Finset (G → K) := (XgESet_finite σ e).toFinset

theorem mem_XgE {σ : K →+* ℂ} {e : MonoidAlgebra ℂ G} {χ : G → K} :
    χ ∈ XgE σ e ↔ IsAbsIrrChar χ ∧ ∑ g : G, e.coeff g * σ (χ g) = σ (χ 1) :=
  Set.Finite.mem_toFinset _

theorem XgE_irr {σ : K →+* ℂ} {e : MonoidAlgebra ℂ G} : ∀ χ ∈ XgE σ e, IsAbsIrrChar χ :=
  fun _ h => (mem_XgE.1 h).1

end E

end Formalism.L2.Col
