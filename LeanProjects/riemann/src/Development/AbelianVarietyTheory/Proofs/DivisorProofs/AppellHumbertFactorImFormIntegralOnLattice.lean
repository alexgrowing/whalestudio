import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusRM

theorem ahFactor_im_int_chart {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (y : Sp ℂ ⟶ X) :
    ∃ j, ⊤ ≤ y ⁻¹ᵁ L.U j := by
  let p0 : Sp ℂ := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  have hmem : y p0 ∈ (⨆ i, L.U i : X.Opens) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  refine ⟨j, fun q _ => ?_⟩
  have : q = p0 := by
    haveI := q.isPrime
    haveI := p0.isPrime
    exact PrimeSpectrum.ext ((Ideal.eq_bot_of_prime q.asIdeal).trans (Ideal.eq_bot_of_prime p0.asIdeal).symm)
  rw [this]
  exact hj

theorem ahFactor_herm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (v w : Fin g → ℂ) : w ⬝ᵥ Hm.mulVec (star v) = star (v ⬝ᵥ Hm.mulVec (star w)) := by
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← hH.apply a b, star_star]
  ring

theorem ahFactor_im_int : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (u : HolUnif A L g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), L.IsLB → IsFactorAH u Hm χ →
    ∀ l ∈ u.Λ, ∀ l' ∈ u.Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n := by
  intro g A _ L u Hm χ hL hF l hl l' hl'
  obtain ⟨hH, hχ, hfac⟩ := hF
  obtain ⟨i, hi⟩ := ahFactor_im_int_chart L hL (u.ex 0).left
  have hex : ∀ z ∈ u.Λ, u.ex z = u.ex 0 := fun z hz => by
    rw [(u.ker z).mpr hz, (u.ker 0).mpr (zero_mem _)]
  have hc : ∀ z ∈ u.Λ, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i := fun z hz => by rw [hex z hz]; exact hi
  have e1 := hfac ⟨l, hl⟩ i 0 (hc 0 (zero_mem _))
  have e2 := hfac ⟨l', hl'⟩ i l (hc l hl)
  have e3 := hfac ⟨l', hl'⟩ i 0 (hc 0 (zero_mem _))
  have e4 := hfac ⟨l, hl⟩ i l' (hc l' hl')
  have hne := u.fr_ne i (l + l') (hc _ (add_mem hl hl'))
  have hχ1 : χ ⟨l, hl⟩ ≠ 0 := fun h => by simpa [h] using hχ ⟨l, hl⟩
  have hχ2 : χ ⟨l', hl'⟩ ≠ 0 := fun h => by simpa [h] using hχ ⟨l', hl'⟩
  have hsw := ahFactor_herm_swap hH l l'
  simp only [zero_add, zero_dotProduct, mul_zero] at e1 e3
  rw [e2] at e1
  rw [e4, add_comm l' l] at e3
  have key := e1.symm.trans e3
  set F := u.fr i (l + l')
  set H := l ⬝ᵥ Hm.mulVec (star l')
  set H' := l' ⬝ᵥ Hm.mulVec (star l')
  set H0 := l ⬝ᵥ Hm.mulVec (star l)
  set Hs := l' ⬝ᵥ Hm.mulVec (star l)
  set c1 := χ ⟨l, hl⟩
  set c2 := χ ⟨l', hl'⟩
  have key2 : (c1 * c2 * F) * Complex.exp (Real.pi / 2 * H0 + (Real.pi * H + Real.pi / 2 * H')) =
      (c1 * c2 * F) * Complex.exp (Real.pi / 2 * H' + (Real.pi * Hs + Real.pi / 2 * H0)) := by
    simp only [Complex.exp_add] at key ⊢
    linear_combination key
  have hnz : c1 * c2 * F ≠ 0 := mul_ne_zero (mul_ne_zero hχ1 hχ2) hne
  have key3 := mul_left_cancel₀ hnz key2
  have key4 : Complex.exp ((Real.pi / 2 * H0 + (Real.pi * H + Real.pi / 2 * H')) -
      (Real.pi / 2 * H' + (Real.pi * Hs + Real.pi / 2 * H0))) = 1 := by
    rw [Complex.exp_sub, key3, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp key4
  refine ⟨n, ?_⟩
  have hsc : H - Hs = 2 * (H.im : ℂ) * Complex.I := by
    rw [hsw]
    have h7 := Complex.sub_conj H
    push_cast at h7
    exact h7
  have h5 : ((H.im : ℂ) - n) * (2 * Real.pi * Complex.I) = 0 := by
    linear_combination hn - (Real.pi : ℂ) * hsc
  have h6 := sub_eq_zero.mp ((mul_eq_zero.mp h5).resolve_right Complex.two_pi_I_ne_zero)
  exact_mod_cast h6

end GlobalTheory.TorusRM
