import Mathlib

open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Cmp.RegularTensor

open Polynomial

theorem natDegree_minpoly_eq_of_closed {k F A : Type*} [Field k] [Field F] [Field A] [Algebra k F]
    [Algebra F A] [Algebra k A] [IsScalarTower k F A]
    (h : ∀ x : F, IsAlgebraic k x → x ∈ Set.range (algebraMap k F))
    {θ : A} (hθ : IsIntegral k θ) : (minpoly F θ).natDegree = (minpoly k θ).natDegree := by
  have hF : IsIntegral F θ := hθ.tower_top
  have hd : minpoly F θ ∣ (minpoly k θ).map (algebraMap k F) :=
    minpoly.dvd_map_of_isScalarTower k F θ
  have h1 := integralClosure.mem_lifts_of_monic_of_dvd_map F (minpoly.monic hθ)
    (minpoly.monic hF) hd
  have h2 : minpoly F θ ∈ lifts (algebraMap k F) := by
    rw [lifts_iff_coeff_lifts] at h1 ⊢
    intro n
    obtain ⟨y, hy⟩ := h1 n
    rw [← hy]
    exact h _ (IsIntegral.isAlgebraic y.2)
  obtain ⟨q, hq, hdeg, hm⟩ := lifts_and_natDegree_eq_and_monic h2 (minpoly.monic hF)
  apply le_antisymm
  · have := natDegree_le_of_dvd hd ((minpoly.monic hθ).map _).ne_zero
    rwa [natDegree_map] at this
  · rw [← hdeg]
    refine natDegree_le_of_dvd (minpoly.dvd k θ ?_) hm.ne_zero
    rw [← aeval_map_algebraMap F, hq, minpoly.aeval]

theorem main : ∀ (k Ω L : Type) [Field k] [CharZero k] [Field Ω] [Field L] [Algebra k Ω] [Algebra k L] [FiniteDimensional k L], (∀ x : Ω, IsAlgebraic k x → x ∈ Set.range (algebraMap k Ω)) → IsField (TensorProduct k Ω L) := by
  intro k Ω L _ _ _ _ _ _ _ h
  let A := AlgebraicClosure Ω
  let ψ : L →ₐ[k] A := IsAlgClosed.lift
  let pb := Field.powerBasisOfFiniteOfSeparable k L
  let m : Ω ⊗[k] L →ₐ[Ω] A :=
    Algebra.TensorProduct.lift (Algebra.ofId Ω A) ψ fun _ _ => Commute.all _ _
  let b := Algebra.TensorProduct.basis Ω pb.basis
  have hd : (minpoly Ω (ψ pb.gen)).natDegree = pb.dim := by
    rw [natDegree_minpoly_eq_of_closed h (pb.isIntegral_gen.map ψ),
      minpoly.algHom_eq ψ ψ.toRingHom.injective, pb.natDegree_minpoly]
  have li : LinearIndependent Ω (m.toLinearMap ∘ b) := by
    have h1 := (linearIndependent_pow (K := Ω) (ψ pb.gen)).comp (Fin.cast hd.symm)
      (Fin.cast_injective _)
    convert h1 using 1
    funext i
    simp [m, b]
  have hinj : Function.Injective m := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h2 : Finsupp.linearCombination Ω (m.toLinearMap ∘ b) (b.repr x) = 0 := by
      rw [← Finsupp.apply_linearCombination, b.linearCombination_repr]
      exact hx
    exact b.repr.map_eq_zero_iff.1 (linearIndependent_iff.1 li _ h2)
  have : IsDomain (Ω ⊗[k] L) := hinj.isDomain m.toRingHom
  exact Algebra.TensorProduct.isField_of_isAlgebraic k Ω L (Or.inr inferInstance)

end GlobalTheory.CompanionTheory.Ar.Cmp.RegularTensor
