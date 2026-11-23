import Mathlib
import GroundTheory.AutomorphicForms.DefiniteClassNumber.IsIntegralVecCoordsOfRatCoordsSingle

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

section Sums

variable {H : Matrix ι ι E}

end Sums

def basisOfCard {k M : Type*} [Field k] [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    {n : Type*} [Fintype n] {v : n → M} (hli : LinearIndependent k v)
    (hcard : Fintype.card n = finrank k M) : Basis n k M :=
  Basis.mk hli (by
    have h1 := (linearIndependent_iff_card_eq_finrank_span.1 hli)
    refine (Submodule.eq_top_of_finrank_eq ?_).ge
    rw [← hcard, h1]
    rfl)

theorem basisOfCard_apply {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    [FiniteDimensional k M] {n : Type*} [Fintype n] {v : n → M} (hli : LinearIndependent k v)
    (hcard : Fintype.card n = finrank k M) (i : n) : basisOfCard hli hcard i = v i :=
  Basis.mk_apply _ _ _

section Reconstruct

variable {H : Matrix ι ι E}

omit [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E] [DecidableEq ι] [Fintype ι]
  [Fintype κ] in
theorem linearIndependent_ratCoords {E : Type*} [CommRing E] [Algebra K E] {N : ℕ}
    {b : Basis κ K E} {x : Fin N → ι → K ⊗[K] E}
    (hli : LinearIndependent ℝ fun i => ratEmb b (x i)) :
    LinearIndependent ℚ fun i => ratCoords b (x i) := by
  rw [Fintype.linearIndependent_iff] at *
  intro g hg i
  have := hli (fun i => (g i : ℝ)) (by
    funext j
    have := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    simp only [ratEmb]
    exact_mod_cast this) i
  exact_mod_cast this

end Reconstruct

end GroundTheory.Automorphic
