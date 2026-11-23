import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LaTIsPrime

open NumberField ReciprocityTheory.ChartRestriction.G.T0

namespace GlobalTheory

open MvPolynomial

theorem injective_of_injective_comp_aeval_of_trdeg_le {k A κ ι : Type} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [CommRing κ] [Finite ι] (b : ι → A)
    (hA : Algebra.trdeg k A ≤ Cardinal.mk ι) (χ : A →+* κ)
    (hχ : Function.Injective (fun q : MvPolynomial ι k => χ (aeval b q))) :
    Function.Injective χ := by
  have hb : AlgebraicIndependent k b := by
    rw [algebraicIndependent_iff_injective_aeval]
    exact Function.Injective.of_comp (f := χ) hχ
  have hT := hb.isTranscendenceBasis_of_trdeg_le_of_finite hA
  have := hT.isAlgebraic
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hne
  have hmem : a ∈ RingHom.ker χ := ha
  refine Ideal.comap_ne_bot_of_algebraic_mem hne hmem
    (Algebra.IsAlgebraic.isAlgebraic (R := Algebra.adjoin k (Set.range b)) a) (eq_bot_iff.2 fun y hy => ?_)
  rw [Ideal.mem_comap, RingHom.mem_ker] at hy
  rw [Ideal.mem_bot]
  obtain ⟨y, hy'⟩ := y
  have hr := hy'
  rw [Algebra.adjoin_range_eq_range_aeval] at hr
  obtain ⟨q, rfl⟩ := hr
  have h0 : χ (aeval b q) = 0 := hy
  have hq : q = 0 := hχ (show χ (aeval b q) = χ (aeval b 0) by rw [map_zero, map_zero]; exact h0)
  subst hq
  apply Subtype.ext
  simp

private def elimEmb (D N : ℕ) (j0 : Fin (N + 1)) :
    Fin (N + 1) ⊕ (Fin D × Fin N) → TVar D N
  | Sum.inl j => (0, j)
  | Sum.inr q => (q.1.succ, j0.succAbove q.2)

private noncomputable def elimImg {F : Type} [Field F] (D N : ℕ) (j0 : Fin (N + 1))
    (xx : Fin (N + 1) → F) (p : TVar D N) : MvPolynomial (Fin (N + 1) ⊕ (Fin D × Fin N)) F :=
  Fin.cases (motive := fun _ => MvPolynomial (Fin (N + 1) ⊕ (Fin D × Fin N)) F)
    (X (Sum.inl p.2))
    (fun i => Fin.insertNth (α := fun _ => MvPolynomial (Fin (N + 1) ⊕ (Fin D × Fin N)) F) j0
      (-∑ j : Fin N, X (Sum.inr (i, j)) * C (xx (j0.succAbove j)))
      (fun j => X (Sum.inr (i, j))) p.2) p.1

end GlobalTheory
