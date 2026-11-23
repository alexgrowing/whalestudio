import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GapCondExample

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv.DegFormula

theorem finite_det {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V] [Module K V]
    {L : C.I → AddSubgroup V} (b₀ : Module.Basis (Fin (Module.finrank K V)) K V)
    (b : C.I → Module.Basis (Fin (Module.finrank K V)) K V) (hL : IsBun C L)
    (h : ∀ i, IsLatOf C i (b i) (L i)) : {i | C.v i (b₀.det (b i)) ≠ 1}.Finite := by
  obtain ⟨c, hc⟩ := hL.2
  refine (hc.union (C.fin _ (b₀.isUnit_det c).ne_zero)).subset fun i hi => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
  refine hi ?_
  rw [← Module.Basis.det_mul_det _ c, map_mul, Inhab.v_det C hn.1 (h i), hn.2, mul_one]

theorem deg_formula : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (n : ℕ)
    (b₀ : Module.Basis (Fin n) K V) (b : C.I → Module.Basis (Fin n) K V), IsBun C L →
    (∀ i, IsLatOf C i (b i) (L i)) → {i | C.v i (b₀.det (b i)) ≠ 1}.Finite ∧
      deg C L = ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (b₀.det (b i))) := by
  intro K _ C V _ _ _ L n b₀ b hL h
  have hn : n = Module.finrank K V := by
    simpa using (Module.finrank_eq_card_basis b₀).symm
  subst hn
  have hf := finite_det C b₀ b hL h
  refine ⟨hf, ?_⟩
  rw [Inhab.deg_eq C b h]
  have hx : (Module.finBasis K V).det b₀ ≠ 0 := ((Module.finBasis K V).isUnit_det b₀).ne_zero
  have key : ∀ i, (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det (b i))) =
      (C.w i : ℤ) * WithZero.log (C.v i ((Module.finBasis K V).det b₀)) +
        (C.w i : ℤ) * WithZero.log (C.v i (b₀.det (b i))) := by
    intro i
    rw [← Module.Basis.det_mul_det _ b₀, map_mul,
      WithZero.log_mul ((Valuation.ne_zero_iff _).2 hx)
        ((Valuation.ne_zero_iff _).2 (b₀.isUnit_det (b i)).ne_zero), mul_add]
  simp only [key]
  rw [finsum_add_distrib ((C.fin _ hx).subset fun i hi h1 => hi (by simp [h1]))
    (hf.subset fun i hi h1 => hi (by simp [h1])), C.prod _ hx, zero_add]

end GlobalTheory.CompanionTheory.Ar.Crv.DegFormula
