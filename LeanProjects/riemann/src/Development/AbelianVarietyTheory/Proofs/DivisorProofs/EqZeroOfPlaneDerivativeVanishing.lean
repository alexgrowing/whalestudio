import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesInsertZero
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

noncomputable section

namespace GlobalTheory.ThK.PlaneEv

open scoped Classical

theorem ins0_mul_plane {F : Type} [Field F] [NumberField F] {n d d₁ : ℕ} (hd : d = d₁ + 2)
    (x₁ : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) (β : Fin n × Fin d → mixedEmbedding.mixedSpace F)
    (hβ : IsPl hd β) (i : Fin n × Fin d) : ins0 hd x₁ i * β i = 0 := by
  obtain ⟨j, rfl⟩ := (idx hd).symm.surjective i
  rcases j with q | q
  · rw [hβ q, mul_zero]
  · rw [planeZeroInsertion_apply_inr, zero_mul]

theorem eq_zero_of_dH_plane_of_ins0 (F : Type) [Field F] [NumberField F] (n d d₁ : ℕ) (hd : d = d₁ + 2)
    (f₀ : SInf F (Fin n × Fin d))
    (hγ : ∀ γ : Fin n × Fin d → mixedEmbedding.mixedSpace F, IsPl hd γ →
      ∃ β : Fin n × Fin d → mixedEmbedding.mixedSpace F, IsPl hd β ∧ ∃ c : ℂ, ∀ x, dH γ 0 ⇑f₀ x = c * dH 0 β ⇑f₀ x)
    (h0 : ∀ x₁, f₀ (ins0 hd x₁) = 0) : f₀ = 0 := by
  refine SchwartzMap.ext fun x => ?_
  simp only [SchwartzMap.zero_apply]
  set x₁ : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F := fun q => x ((idx hd).symm (Sum.inl q)) with hx₁
  set p : Fin n × Fin d → mixedEmbedding.mixedSpace F := x - ins0 hd x₁ with hp
  have hpl : IsPl hd p := fun q => by simp [hp, x₁]
  obtain ⟨β, hβ, c, hc⟩ := hγ p hpl
  set K : ℝ := Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, p i * β i) with hK
  set A : ℂ := c * (-(2 * Real.pi * Complex.I * K)) with hA
  let h : ℝ → ℂ := fun t => f₀ (ins0 hd x₁ + t • p)
  have hder : ∀ t : ℝ, HasDerivAt h (A * t * h t) t := by
    intro t
    have hl : HasDerivAt (fun s : ℝ => ins0 hd x₁ + s • p) p t := by
      simpa using ((hasDerivAt_id t).smul_const p).const_add (ins0 hd x₁)
    have h1 := (f₀.differentiableAt (x := ins0 hd x₁ + t • p)).hasFDerivAt.comp_hasDerivAt t hl
    refine h1.congr_deriv ?_
    have hs : ∑ i, (ins0 hd x₁ + t • p) i * β i = t • ∑ i, p i * β i := by
      simp only [Pi.add_apply, Pi.smul_apply, add_mul, Finset.sum_add_distrib, ins0_mul_plane hd x₁ β hβ,
        Finset.sum_const_zero, zero_add, smul_mul_assoc, ← Finset.smul_sum]
    have e := hc (ins0 hd x₁ + t • p)
    simp only [dH, Pi.zero_apply, mul_zero, Finset.sum_const_zero, map_zero, Complex.ofReal_zero, zero_mul,
      sub_zero, zero_sub, hs, map_smul, smul_eq_mul] at e
    rw [e]
    simp only [h, hA, hK]
    push_cast
    ring
  let g : ℝ → ℂ := fun t => Complex.exp (-(A * ((t ^ 2 : ℝ) : ℂ) / 2)) * h t
  have hg : ∀ t : ℝ, HasDerivAt g 0 t := by
    intro t
    have e1 := ((((hasDerivAt_pow 2 t).ofReal_comp).const_mul A).div_const 2).neg.cexp
    have e2 := e1.mul (hder t)
    refine e2.congr_deriv ?_
    simp only [Nat.cast_ofNat, pow_one, Nat.add_one_sub_one]
    push_cast
    ring
  have hconst := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  have hg0 : g 0 = 0 := by
    simp [g, h, h0]
  have hg1 : g 1 = Complex.exp (-(A * ((1 ^ 2 : ℝ) : ℂ) / 2)) * f₀ x := by
    simp only [g, h, one_smul, hp, add_sub_cancel]
  rw [hconst, hg0] at hg1
  exact (mul_eq_zero.1 hg1.symm).resolve_left (Complex.exp_ne_zero _)

end GlobalTheory.ThK.PlaneEv
