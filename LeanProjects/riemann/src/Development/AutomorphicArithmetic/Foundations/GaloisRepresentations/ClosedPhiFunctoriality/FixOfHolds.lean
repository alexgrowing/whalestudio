import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IsOp2One
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem fix_aux {A S : Type} [CommSemiring A] [Semiring S] [Algebra A S] (φ : S →ₐ[A] S) (x y : ℕ) (c : S)
    (h : (φ ^ y) c = (φ ^ x) c) : (φ ^ ((x : ℤ) - y).natAbs) ((φ ^ y) c) = (φ ^ y) c := by
  rcases le_total x y with hxy | hxy
  · have e : ((x : ℤ) - y).natAbs = y - x := by omega
    rw [e, h, ← AlgHom.mul_apply, ← pow_add, Nat.sub_add_cancel hxy, h]
  · have e : ((x : ℤ) - y).natAbs = x - y := by omega
    rw [e, ← AlgHom.mul_apply, ← pow_add, Nat.sub_add_cancel hxy, h]

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.fixOf_holds :
    FixOf := by
  intro l _ E Ω _ _ _ _ _ w A h O _ _ _ Bw hj g c hc
  obtain ⟨a, b, hσ⟩ := g.2
  have hal : (alpha l g) = ((resDeg l w * a : ℕ) : ℤ) - ((resDeg l w * b : ℕ) : ℤ) := by
    rw [alpha, deg_eq hσ]; push_cast; ring
  obtain ⟨c', rfl⟩ := (Algebra.IsAlgebraic.algHom_bijective (frobUr l ^ (resDeg l w * b))).2 c
  have h1 := weilToGK_frobUr hj g hσ c'
  rw [mem_GK.mp (weilToGK Bw h g).2 _ hc] at h1
  rw [hal]
  exact fix_aux _ _ _ _ (Subtype.ext h1)
