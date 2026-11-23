import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FirstRaisingMemEquivariant

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets NumberField IsDedekindDomain Formalism.BasicNotions
  Formalism.L2.SG.HidaSetting
open scoped TensorProduct

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

theorem sigR_incl (e : X.B.I.E) :
    sigR (FpX X p) X.B.I.cm.sig (inclR (FpX X p) e) = inclR (FpX X p) (star e) := by
  simp [sigR, inclR, Algebra.TensorProduct.map_tmul]
  rfl

theorem secondEmbedding_eq_star (hθ : IsSplitEquiv X p θ) (e : X.B.I.E) : iota2 X p θ e = iota1 X p θ (star e) := by
  have h := hθ (inclR (FpX X p) e)
  rw [sigR_incl, th_incl, th_incl] at h
  have h1 := congrArg Prod.fst h
  simp only [Prod.fst_swap] at h1
  exact h1.symm

theorem unitElt_holds (hθ : IsSplitEquiv X p θ) : UnitElt X p θ := by
  classical
  have hint : ∀ o : 𝓞 X.B.I.E, Valued.v (iota1 X p θ (algebraMap (𝓞 X.B.I.E) X.B.I.E o)) ≤ 1 := by
    intro o
    have h0 : IsIntegral ℤ (algebraMap (𝓞 X.B.I.E) X.B.I.E o) := RingOfIntegers.isIntegral_coe o
    exact (Valuation.mem_integer_iff _ _).1
      (Valuation.Integers.mem_of_integral (Valuation.integer.integers _)
        (IsIntegral.map_of_comp_eq (Int.castRingHom _) (iota1 X p θ) (RingHom.ext_int _ _) h0))
  have halg : ∀ f : X.B.I.F,
      iota1 X p θ (algebraMap X.B.I.F X.B.I.E f) = algebraMap X.B.I.F (FpX X p) f := by
    intro f
    show (θ (Algebra.TensorProduct.includeRight (algebraMap X.B.I.F X.B.I.E f))).1 = _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply X.B.I.F (FpX X p) (TpX X p),
      AlgEquiv.commutes]
    rfl
  let P : Ideal (𝓞 X.B.I.E) :=
    { carrier := {x | Valued.v (iota1 X p θ (algebraMap (𝓞 X.B.I.E) X.B.I.E x)) < 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_add] at hx hy ⊢
        exact Valuation.map_add_lt _ hx hy
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at hx ⊢
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint c)) hx }
  have hmemP : ∀ x, x ∈ P ↔ Valued.v (iota1 X p θ (algebraMap (𝓞 X.B.I.E) X.B.I.E x)) < 1 :=
    fun x => Iff.rfl
  have hPprime : P.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro htop
      have h1 : (1 : 𝓞 X.B.I.E) ∈ P := by rw [htop]; exact Submodule.mem_top
      rw [hmemP] at h1
      simp at h1
    · intro x y hxy
      rw [hmemP, map_mul, map_mul, Valuation.map_mul] at hxy
      by_contra hn
      rw [not_or, hmemP, hmemP, not_lt, not_lt] at hn
      exact absurd hxy (not_lt.2 (one_le_mul_of_one_le_of_one_le hn.1 hn.2))
  have hPne : P ≠ ⊥ := by
    obtain ⟨f, hfp, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot p.1.ne_bot
    intro hbot
    have hmem : algebraMap (𝓞 X.B.I.F) (𝓞 X.B.I.E) f ∈ P := by
      rw [hmemP, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply (𝓞 X.B.I.F) X.B.I.F X.B.I.E, halg,
        IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hfp
    rw [hbot, Ideal.mem_bot] at hmem
    apply hf0
    first
    | exact (FaithfulSMul.algebraMap_injective (𝓞 X.B.I.F) (𝓞 X.B.I.E)) (by rw [hmem, map_zero])
    | exact (NoZeroSMulDivisors.algebraMap_injective (𝓞 X.B.I.F) (𝓞 X.B.I.E)) (by rw [hmem, map_zero])
  have hPmax : P.IsMaximal := Ideal.IsPrime.isMaximal hPprime hPne
  obtain ⟨a, t, ht, hat⟩ := X.B.I.cm.cmUnram.2.2 P hPmax
  rw [hmemP, not_lt] at hat
  have hv1 : Valued.v (iota1 X p θ (algebraMap (𝓞 X.B.I.E) X.B.I.E (a - t))) = 1 :=
    le_antisymm (hint _) hat
  have hdeq : iota1 X p θ (a : X.B.I.E) - iota2 X p θ (a : X.B.I.E) =
      iota1 X p θ (algebraMap (𝓞 X.B.I.E) X.B.I.E (a - t)) := by
    rw [secondEmbedding_eq_star X p θ hθ, map_sub, map_sub, ht]
  have hv : Valued.v (iota1 X p θ (a : X.B.I.E) - iota2 X p θ (a : X.B.I.E)) = 1 := by
    rw [hdeq]
    exact hv1
  have hd0 : iota1 X p θ (a : X.B.I.E) - iota2 X p θ (a : X.B.I.E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact zero_ne_one hv
  refine ⟨a, (iota1 X p θ (a : X.B.I.E) - iota2 X p θ (a : X.B.I.E))⁻¹, ?_, inv_mul_cancel₀ hd0⟩
  rw [OpX, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]

theorem herm_entry (i j : Fin X.B.I.n) : star (X.B.I.J i j) = X.B.I.J j i := by
  have h : Formalism.UG.cT (starRingEnd X.B.I.E) X.B.I.J = X.B.I.J := X.B.I.J_herm
  have h2 := congrFun (congrFun h j) i
  simpa only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, starRingEnd_apply] using h2

theorem firstForm_apply (a b : Fin X.B.I.n) : J1 X p θ a b = iota1 X p θ (X.B.I.J a b) := rfl

open scoped Matrix in
theorem dual_gen (hθ : IsSplitEquiv X p θ) (l l' : Fin X.B.I.n → X.B.I.E) (hl : l ∈ X.B.I.L)
    (hl' : l' ∈ X.B.I.L) :
    (fun j => iota2 X p θ (l' j)) ⬝ᵥ (J1 X p θ *ᵥ fun j => iota1 X p θ (l j)) ∈ OpX X p := by
  have hint : ∀ o : 𝓞 X.B.I.E, iota1 X p θ (o : X.B.I.E) ∈ OpX X p := by
    intro o
    rw [OpX, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    have h0 : IsIntegral ℤ ((o : X.B.I.E)) := RingOfIntegers.isIntegral_coe o
    exact (Valuation.mem_integer_iff _ _).1
      (Valuation.Integers.mem_of_integral (Valuation.integer.integers _)
        (IsIntegral.map_of_comp_eq (Int.castRingHom _) (iota1 X p θ) (RingHom.ext_int _ _) h0))
  obtain ⟨o, ho⟩ := (X.B.I.L_dual l).1 hl l' hl'
  have key : (fun j => iota2 X p θ (l' j)) ⬝ᵥ (J1 X p θ *ᵥ fun j => iota1 X p θ (l j)) =
      iota1 X p θ (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l' l) := by
    simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, firstForm_apply,
      secondEmbedding_eq_star X p θ hθ, starRingEnd_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key, ← ho]
  exact hint o

end Loc

end MassDataIdxSteps
