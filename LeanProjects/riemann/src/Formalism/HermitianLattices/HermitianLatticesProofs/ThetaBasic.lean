import Mathlib
import Formalism.HermitianLattices.StatementTheta

open Formalism.K

noncomputable section

namespace Formalism.HermitianLatticesTheory

theorem thetaBasic_trace_star {K : Type*} [Field K] [NumberField K] [StarRing K] (a : K) :
    Algebra.trace ℚ K (star a) = Algebra.trace ℚ K a := by
  let e : K ≃ₐ[ℚ] K := AlgEquiv.ofRingEquiv (f := (starRingAut : RingAut K))
    (fun x => ((starRingAut : K ≃+* K).toRingHom.map_rat_algebraMap x))
  exact Algebra.trace_eq_of_algEquiv e a

def thetaBasic_eqv {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (g : V ≃ₗ[K] V)
    (L : Submodule (NumberField.RingOfIntegers K) V) : L ≃ gmap g L where
  toFun x := ⟨g x, Submodule.mem_map_of_mem x.2⟩
  invFun y := ⟨g.symm y, by
    obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 y.2
    have hz' : g z = (y : V) := hzy
    rw [← hz', LinearEquiv.symm_apply_apply]
    exact hz⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)

theorem thetaBasic_eqv_apply {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (g : V ≃ₗ[K] V)
    (L : Submodule (NumberField.RingOfIntegers K) V) (x : L) :
    ((thetaBasic_eqv g L x : gmap g L) : V) = g x := rfl

theorem thetaBasic : ThetaBasic := by
  intro K V _ _ _ _ _ _ _ h hh L γ τ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    unfold thetaL
    refine Eq.trans ?_ ((Equiv.addRight (⟨l, hl⟩ : L)).tsum_eq _)
    refine tsum_congr fun x => ?_
    simp only [Equiv.coe_addRight, Submodule.coe_add]
    rw [show γ + l + (x : V) = γ + ((x : V) + l) by abel]
  · unfold thetaL
    refine Eq.trans ?_ ((Equiv.neg L).tsum_eq _)
    refine tsum_congr fun x => ?_
    simp only [Equiv.neg_apply, Submodule.coe_neg]
    rw [show -γ + (x : V) = -(γ + -(x : V)) by abel]
    simp only [map_neg, LinearMap.neg_apply, neg_neg]
  · intro g hg
    have hg' : ∀ x y, h (g x) (g y) = h x y := hg
    unfold thetaL
    rw [← (thetaBasic_eqv g L).tsum_eq]
    refine tsum_congr fun x => ?_
    rw [thetaBasic_eqv_apply, ← map_add, hg']
  · intro hev hdual
    unfold thetaL
    rw [← tsum_mul_left]
    refine tsum_congr fun x => ?_
    obtain ⟨m, hm⟩ := hev x x.2
    obtain ⟨n, hn⟩ := hdual x x.2
    have h1 : h (x : V) γ = star (h γ x) := (hh.eq γ x).symm
    have hx : Algebra.trace ℚ K (h (γ + x) (γ + x)) =
        Algebra.trace ℚ K (h γ γ) + 2 * ((n : ℚ) + m) := by
      simp only [map_add, LinearMap.add_apply, h1, thetaBasic_trace_star, hn, hm]
      ring
    rw [hx, ← Complex.exp_add]
    set T0 : ℂ := ((Algebra.trace ℚ K (h γ γ) : ℚ) : ℂ)
    have : (Real.pi : ℂ) * Complex.I * (τ + 1) * (((Algebra.trace ℚ K (h γ γ) + 2 * ((n : ℚ) + m) : ℚ)) : ℂ)
        = (Real.pi * Complex.I * T0 + Real.pi * Complex.I * τ *
          (((Algebra.trace ℚ K (h γ γ) + 2 * ((n : ℚ) + m) : ℚ)) : ℂ)) +
          ((n + m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      simp only [T0]; push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · intro n γs T g hg
    have hg' : ∀ x y, h (g x) (g y) = h x y := hg
    unfold thetaN
    rw [← (Equiv.piCongrRight fun _ : Fin n => thetaBasic_eqv g L).tsum_eq]
    refine tsum_congr fun x => ?_
    simp only [Equiv.piCongrRight_apply, Pi.map_apply, thetaBasic_eqv_apply, ← map_add, hg']
  · intro T
    unfold thetaN thetaL
    rw [← (Equiv.funUnique (Fin 1) L).symm.tsum_eq]
    refine tsum_congr fun x => ?_
    simp only [Equiv.funUnique_symm_apply, Fin.sum_univ_one]
    congr 1
    simp [uniqueElim_const]
    ring

end Formalism.HermitianLatticesTheory
