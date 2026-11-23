import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StGramDetermines

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]

namespace GramDetermines

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in

theorem sesq_linearCombination (h : HermitianForm F E W) {n : ℕ} {e e' : Fin n → W}
    (hG : ∀ a b, h.toSesq (e a) (e b) = h.toSesq (e' a) (e' b)) (c d : Fin n → E) :
    h.toSesq (Fintype.linearCombination E e' c) (Fintype.linearCombination E e' d) =
      h.toSesq (Fintype.linearCombination E e c) (Fintype.linearCombination E e d) := by
  simp only [Fintype.linearCombination_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ,
    LinearMap.smul_apply, hG]

omit [NumberField E] [IsTotallyComplex E] in

theorem linearCombination_surjective {n : ℕ} {e : Fin n → W}
    (hL : IsLattice E (AddSubgroup.closure (Set.range e))) :
    Function.Surjective (Fintype.linearCombination E e) := by
  have hle : AddSubgroup.closure (Set.range e) ≤
      (LinearMap.range (Fintype.linearCombination E e)).toAddSubgroup := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    exact ⟨Pi.single a 1, by simp⟩
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
  intro x hx
  exact hle hx

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] in

theorem linearCombination_eq_zero (h : HermitianForm F E W) {n : ℕ} {e e' : Fin n → W}
    (hL' : IsLattice E (AddSubgroup.closure (Set.range e')))
    (hG : ∀ a b, h.toSesq (e a) (e b) = h.toSesq (e' a) (e' b)) (c : Fin n → E)
    (hc : Fintype.linearCombination E e c = 0) : Fintype.linearCombination E e' c = 0 := by
  apply h.nonsingular.1
  refine LinearMap.ext fun y => ?_
  obtain ⟨d, rfl⟩ := linearCombination_surjective hL' y
  rw [sesq_linearCombination h hG, hc, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]

theorem proof (h : HermitianForm F E W) : GramDetermines.Statement h := by
  intro n e e' hL hL' hG
  have hG' : ∀ a b, h.toSesq (e' a) (e' b) = h.toSesq (e a) (e b) := fun a b => (hG a b).symm
  have hs := linearCombination_surjective hL
  have hs' := linearCombination_surjective hL'
  have hker : LinearMap.ker (Fintype.linearCombination E e) =
      LinearMap.ker (Fintype.linearCombination E e') := by
    ext c
    simp only [LinearMap.mem_ker]
    exact ⟨linearCombination_eq_zero h hL' hG c, linearCombination_eq_zero h hL hG' c⟩
  let γ : W ≃ₗ[E] W := ((Fintype.linearCombination E e).quotKerEquivOfSurjective hs).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans
      ((Fintype.linearCombination E e').quotKerEquivOfSurjective hs'))
  have hγ : ∀ c, γ (Fintype.linearCombination E e c) = Fintype.linearCombination E e' c :=
    fun c => by simp [γ, Submodule.quotEquivOfEq_mk]
  refine ⟨⟨γ, fun x y => ?_⟩, fun a => ?_⟩
  · obtain ⟨c, rfl⟩ := hs x
    obtain ⟨d, rfl⟩ := hs y
    rw [hγ, hγ]
    exact sesq_linearCombination h hG c d
  · simpa using hγ (Pi.single a 1)

end GramDetermines

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
