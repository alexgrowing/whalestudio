import Mathlib
import GroundTheory.AutomorphicForms.MacdonaldSpherical
import GroundTheory.AutomorphicForms.MacdonaldNormalization

noncomputable section

namespace GroundTheory.Automorphic

namespace Spherical

open MeasureTheory Matrix GLnLocal Iwasawa HeckeAlgebra AddMonoidAlgebra Finset
open scoped ValuativeRel

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

def vWeight (t : ℂ) (l : Fin n → ℤ) : ℂ :=
  ∏ a ∈ Finset.univ.image l, vPoly (Finset.univ.filter fun i => l i = a).card t

def hallLittlewoodP (t : ℂ) (l : Fin n → ℤ) : LaurentRing n := (vWeight t l)⁻¹ • hlR t l

theorem vPoly_ne_zero {t : ℂ} (ht : Function.Injective fun k : ℕ => t ^ k) (m : ℕ) :
    vPoly m t ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun k _ => div_ne_zero ?_ ?_
  · intro h
    have h' : t ^ (k + 1) = t ^ 0 := by rw [pow_zero]; exact (sub_eq_zero.1 h).symm
    have := ht h'
    omega
  · intro h
    have h' : t ^ 1 = t ^ 0 := by rw [pow_zero, pow_one]; exact (sub_eq_zero.1 h).symm
    have := ht h'
    omega

theorem vWeight_ne_zero {t : ℂ} (ht : Function.Injective fun k : ℕ => t ^ k) (l : Fin n → ℤ) :
    vWeight t l ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => vPoly_ne_zero ht _

theorem injective_qInv_pow : Function.Injective fun k : ℕ => ((qF F : ℂ))⁻¹ ^ k := by
  have hq : 1 < qF F := Finite.one_lt_card
  have hpos : (0 : ℝ) < (qF F : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast qF_pos)
  have hne : (qF F : ℝ)⁻¹ ≠ 1 := by
    intro h
    rw [inv_eq_one] at h
    have : (1 : ℝ) < qF F := by exact_mod_cast hq
    linarith
  intro a b hab
  apply pow_right_injective₀ hpos hne
  apply Complex.ofReal_injective
  simp only at hab ⊢
  push_cast
  exact hab

theorem halfModulus_mul_recursion (Q : (Fin n → ℤ) → LaurentRing n)
    (hQ : ∀ r l, esymmL n r * Q l = ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, Q (l + lamS S))
    (z : Fin n → ℂˣ) {r : ℕ} (hr : r ≤ n) (l : Fin n → ℤ) :
    sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) * (halfModulus F l * evalAt z (Q l)) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        (kappa F S : ℂ) * (halfModulus F (l + lamS S) * evalAt z (Q (l + lamS S))) := by
  have h1 : evalAt z (esymmL n r) * evalAt z (Q l) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, evalAt z (Q (l + lamS S)) := by
    rw [← map_mul, hQ, map_sum]
  calc _ = sqrtQ F ^ (r * (n - r)) * halfModulus F l * (evalAt z (esymmL n r) * evalAt z (Q l)) := by
        ring
    _ = _ := by
        rw [h1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [halfModulus_add, ← kappa_mul_halfModulus hr (Finset.mem_powersetCard.1 hS).2]
        ring

theorem rhoPair_add (a b : Fin n → ℤ) : rhoPair (a + b) = rhoPair a + rhoPair b := by
  simp only [rhoPair, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem rhoPair_neg (a : Fin n → ℤ) : rhoPair (-a) = -rhoPair a := by
  simp only [rhoPair, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem rhoPair_comp_swap {μ : Fin n → ℤ} {i j : Fin n} (hij : (j : ℕ) = i + 1)
    (hμ : μ j = μ i + 1) : rhoPair (μ ∘ Equiv.swap i j) = rhoPair μ + 2 := by
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hs : μ ∘ Equiv.swap i j = μ + (Pi.single i 1 + -Pi.single j 1) := by
    funext x
    simp only [Function.comp_apply, Pi.add_apply, Pi.neg_apply, Pi.single_apply,
      Equiv.swap_apply_def]
    split_ifs <;> subst_vars <;> omega
  rw [hs, rhoPair_add, rhoPair_add, rhoPair_neg, rhoPair_single, rhoPair_single]
  push_cast [hij]
  ring

theorem halfModulus_hlR_swap (z : Fin n → ℂˣ) {μ : Fin n → ℤ} {i j : Fin n}
    (hij : (j : ℕ) = i + 1) (hμ : μ j = μ i + 1) :
    halfModulus F (μ ∘ Equiv.swap i j) * evalAt z (hlR ((qF F : ℂ))⁻¹ (μ ∘ Equiv.swap i j)) =
      halfModulus F μ * evalAt z (hlR ((qF F : ℂ))⁻¹ μ) := by
  rw [hlR_swap _ hij hμ, map_smul, smul_eq_mul, halfModulus_eq, halfModulus_eq,
    rhoPair_comp_swap hij hμ, neg_add, zpow_add₀ sqrtQ_ne_zero, ← sqrtQ_sq]
  rw [show (sqrtQ F) ^ (-2 : ℤ) = ((sqrtQ F) ^ 2)⁻¹ by rw [_root_.zpow_neg]; norm_cast]
  ring

theorem evalAt_esymmL_self_ne_zero (z : Fin n → ℂˣ) : evalAt z (esymmL n n) ≠ 0 := by
  have hp : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  rw [evalAt_esymmL, hp, Finset.sum_singleton, monomialChar_apply]
  exact Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _

theorem schur_zero : schur (0 : Fin n → ℤ) = 1 := by
  refine altQuot_eq_of_mul ?_
  rw [mul_one, zero_add]
  rfl

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem macdonald_formula_hlR (z : Fin n → ℂˣ) {l : Fin n → ℤ} (hl : Antitone l) :
    vPoly n ((qF F : ℂ))⁻¹ * zonalSpherical μ z (torusPow F n l) =
      halfModulus F l * evalAt z (hlR ((qF F : ℂ))⁻¹ l) := by
  set t : ℂ := ((qF F : ℂ))⁻¹
  set f : (Fin n → ℤ) → ℂ := fun m =>
    vPoly n t * zonalSpherical μ z (torusPow F n m) - halfModulus F m * evalAt z (hlR t m) with hf
  have hswap : ∀ (m : Fin n → ℤ) (i j : Fin n), (j : ℕ) = i + 1 → m j = m i + 1 →
      f (m ∘ Equiv.swap i j) = f m := by
    intro m i j hij hm
    simp only [hf]
    rw [zonalSpherical_torusPow_comp, halfModulus_hlR_swap z hij hm]
  have key := eq_zero_of_recursion (fun S => (kappa F S : ℝ)) (fun S => by exact_mod_cast kappa_pos S)
    (fun r => sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r))
    (by
      rw [Nat.sub_self, mul_zero, pow_zero, one_mul]
      exact evalAt_esymmL_self_ne_zero z)
    f
    (by
      intro m hm r hr
      have h1 := zonalSpherical_recursion (μ := μ) z hm hr
      have h2 := halfModulus_mul_recursion (F := F) (hlR t) (fun r l => esymmL_mul_hlR t r l) z hr m
      simp only [hf, Complex.ofReal_natCast]
      calc _ = vPoly n t * (sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) *
              zonalSpherical μ z (torusPow F n m)) -
            sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) *
              (halfModulus F m * evalAt z (hlR t m)) := by ring
        _ = _ := by
          rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun S _ => by ring)
    (fun m hm S => Or.inr (by
      obtain ⟨σ, hσ, hfσ⟩ := exists_perm_antitone f hswap hm S
      exact ⟨σ, hσ, hfσ.symm⟩))
    (by
      simp only [hf, torusPow_zero, zonalSpherical_one, halfModulus_zero, one_mul, mul_one]
      rw [hlR_zero t injective_qInv_pow, AlgHom.commutes]
      simp)
  exact sub_eq_zero.1 (key l hl)

theorem macdonald_formula (z : Fin n → ℂˣ) {l : Fin n → ℤ} (hl : Antitone l) :
    zonalSpherical μ z (torusPow F n l) =
      halfModulus F l * (vWeight ((qF F : ℂ))⁻¹ l / vPoly n ((qF F : ℂ))⁻¹) *
        evalAt z (hallLittlewoodP ((qF F : ℂ))⁻¹ l) := by
  have h := macdonald_formula_hlR (μ := μ) z hl
  have hv := vPoly_ne_zero (injective_qInv_pow (F := F)) n
  have hw := vWeight_ne_zero (injective_qInv_pow (F := F)) l
  have h' : zonalSpherical μ z (torusPow F n l) =
      halfModulus F l * evalAt z (hlR ((qF F : ℂ))⁻¹ l) / vPoly n ((qF F : ℂ))⁻¹ := by
    rw [eq_div_iff hv, mul_comm, h]
  rw [hallLittlewoodP, map_smul, smul_eq_mul, h']
  generalize ((qF F : ℂ))⁻¹ = t at hv hw ⊢
  field_simp

theorem eq_smul_zonalSpherical (z : Fin n → ℂˣ) {f : GL (Fin n) F → ℂ}
    (hfK : ∀ g, ∀ k ∈ integralGL F n, f (g * k) = f g)
    (hfK' : ∀ k ∈ integralGL F n, ∀ g, f (k * g) = f g)
    (heig : ∀ (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F),
      ∫ x, (h : HeckeAlgebra μ) x * f (g * x) ∂μ = evalAt z (satakeTransform μ h) * f g)
    (g : GL (Fin n) F) : f g = f 1 * zonalSpherical μ z g := by
  set F' : (Fin n → ℤ) → ℂ := fun m =>
    f (torusPow F n m) - f 1 * zonalSpherical μ z (torusPow F n m) with hF'
  have hcomp : ∀ (m : Fin n → ℤ) (σ : Equiv.Perm (Fin n)), f (torusPow F n (m ∘ σ)) = f (torusPow F n m) := by
    intro m σ
    rw [← permGL_conj_torusPow, hfK _ _ (permGL_mem_integralGL F n σ),
      hfK' _ ((integralGL F n).inv_mem (permGL_mem_integralGL F n σ))]
  have hswap : ∀ (m : Fin n → ℤ) (i j : Fin n), (j : ℕ) = i + 1 → m j = m i + 1 →
      F' (m ∘ Equiv.swap i j) = F' m := by
    intro m i j _ _
    simp only [hF']
    rw [hcomp, zonalSpherical_torusPow_comp]
  have key := eq_zero_of_recursion (fun S => (kappa F S : ℝ)) (fun S => by exact_mod_cast kappa_pos S)
    (fun r => sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r))
    (by
      rw [Nat.sub_self, mul_zero, pow_zero, one_mul]
      exact evalAt_esymmL_self_ne_zero z)
    F'
    (by
      intro m hm r hr
      have h1 := zonalSpherical_recursion (μ := μ) z hm hr
      have h2 := recursion_of_integral_eq (μ := μ) z hfK (fun u hu g => hfK' u hu.2 g) hm hr
        (heig _ _)
      simp only [hF', Complex.ofReal_natCast]
      calc _ = sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) * f (torusPow F n m) -
            f 1 * (sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) *
              zonalSpherical μ z (torusPow F n m)) := by ring
        _ = _ := by
          rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun S _ => by ring)
    (fun m hm S => Or.inr (by
      obtain ⟨σ, hσ, hfσ⟩ := exists_perm_antitone F' hswap hm S
      exact ⟨σ, hσ, hfσ.symm⟩))
    (by simp only [hF', torusPow_zero, zonalSpherical_one, mul_one, sub_self])
  obtain ⟨l, hl, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul F n g
  rw [hfK _ _ hk₂, hfK' _ hk₁, zonalSpherical_mul_right z _ hk₂, zonalSpherical_mul_left z hk₁,
    diagPow_eq_torusPow]
  exact sub_eq_zero.1 (key l hl)

theorem casselman_shalika (ψ₀ : AddChar F ℂ) (hψ₀ : ∀ x ∈ 𝒪[F], ψ₀ x = 1)
    (hψ₁ : ∃ x : F, (GLnLocal.uniformizer F : F) * x ∈ 𝒪[F] ∧ ψ₀ x ≠ 1) (z : Fin n → ℂˣ)
    {W : GL (Fin n) F → ℂ}
    (hWN : ∀ u ∈ unipotent F n, ∀ g, W (u * g) = Whittaker.psiN ψ₀ u * W g)
    (hWK : ∀ g, ∀ k ∈ integralGL F n, W (g * k) = W g)
    (heig : ∀ (h : SphericalHecke μ (F := F) (n := n)) (g : GL (Fin n) F),
      ∫ x, (h : HeckeAlgebra μ) x * W (g * x) ∂μ = evalAt z (satakeTransform μ h) * W g)
    (l : Fin n → ℤ) :
    W (torusPow F n l) = if Antitone l then W 1 * halfModulus F l * evalAt z (schur l) else 0 := by
  split_ifs with hl
  swap
  · exact eq_zero_of_not_antitone hψ₁ hWN hWK hl
  have hN : ∀ u ∈ unipotent F n ⊓ integralGL F n, ∀ g, W (u * g) = W g := by
    intro u hu g
    rw [hWN u hu.1, psiN_eq_one_of_mem hψ₀ hu, one_mul]
  set f : (Fin n → ℤ) → ℂ := fun m =>
    W (torusPow F n m) - W 1 * (halfModulus F m * evalAt z (schur m)) with hf
  have key := eq_zero_of_recursion (fun S => (kappa F S : ℝ)) (fun S => by exact_mod_cast kappa_pos S)
    (fun r => sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r))
    (by
      rw [Nat.sub_self, mul_zero, pow_zero, one_mul]
      exact evalAt_esymmL_self_ne_zero z)
    f
    (by
      intro m hm r hr
      have h1 := recursion_of_integral_eq (μ := μ) z hWK hN hm hr (heig _ _)
      have h2 := halfModulus_mul_recursion (F := F) schur (fun r l => esymmL_mul_schur r l) z hr m
      simp only [hf, Complex.ofReal_natCast]
      calc _ = sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) * W (torusPow F n m) -
            W 1 * (sqrtQ F ^ (r * (n - r)) * evalAt z (esymmL n r) *
              (halfModulus F m * evalAt z (schur m))) := by ring
        _ = _ := by
          rw [h1, h2, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun S _ => by ring)
    (by
      intro m hm S
      by_cases hant : Antitone (m + lamS S)
      · exact Or.inr ⟨1, by simpa using hant, by simp⟩
      · left
        obtain ⟨i, j, hij, hmij, hiS, hjS⟩ := exists_ascent hm hant
        have hasc : (m + lamS S) j = (m + lamS S) i + 1 := by
          simp only [Pi.add_apply, lamS_apply, hiS, hjS, if_true, if_false, hmij]
          ring
        simp only [hf]
        rw [eq_zero_of_not_antitone hψ₁ hWN hWK hant, schur_eq_zero_of_ascent hij hasc, map_zero,
          mul_zero, mul_zero, sub_zero])
    (by simp only [hf, torusPow_zero, halfModulus_zero, schur_zero, map_one, mul_one, sub_self])
  have := key l hl
  simp only [hf] at this
  rw [mul_assoc]
  exact sub_eq_zero.1 this

end Spherical

end GroundTheory.Automorphic
