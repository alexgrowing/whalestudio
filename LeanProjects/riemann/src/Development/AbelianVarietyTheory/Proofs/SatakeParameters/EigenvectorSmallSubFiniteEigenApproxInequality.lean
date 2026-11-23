import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong

namespace GlobalTheory.Cong

theorem eigen_small_sub_finite_approx : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (V X J I : Type) [AddCommGroup V] [Module ℂ V] [Fintype I] (T : J → Module.End ℂ V) (ev : X → V →ₗ[ℂ] ℂ), (∀ (v : V) (R : ℝ), (∀ x, ‖ι.symm (ev x v)‖ ≤ R) → ∀ j x, ‖ι.symm (ev x (T j v))‖ ≤ R) → ∀ (v₀ : V) (θ : J → ℂ) (x₀ : X), (∀ j, T j v₀ = θ j • v₀) → ‖ι.symm (ev x₀ v₀)‖ = 1 → ∀ (v : I → V) (η : I → J → ℂ), (∀ i j, T j (v i) = η i j • v i) → ∀ ε : ℝ, (∀ x, ‖ι.symm (ev x (v₀ + ∑ i, v i))‖ ≤ ε) → ∃ (s : Finset (J → Qbar l)) (c : (J → Qbar l) → Qbar l), (∀ z ∈ s, ∃ i, z = fun j => ι.symm (η i j)) ∧ ∀ P : MvPolynomial J ℤ, ‖MvPolynomial.aeval (fun j => ι.symm (θ j)) P - ∑ z ∈ s, c z * MvPolynomial.aeval z P‖ ≤ ε := by
  intro l _ ι V X J I _ _ _ T ev hT v₀ θ x₀ hθ hx₀ v η hη ε hε
  classical
  have hmap : ∀ (w : J → ℂ) (P : MvPolynomial J ℤ),
      ι.symm (MvPolynomial.aeval w P) = MvPolynomial.aeval (fun j => ι.symm (w j)) P := by
    intro w P
    induction P using MvPolynomial.induction_on with
    | C n => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => simp [hp]
  let u : MvPolynomial J ℤ → V := fun P =>
    MvPolynomial.aeval θ P • v₀ + ∑ i, MvPolynomial.aeval (η i) P • v i
  have good : ∀ P, ∀ x, ‖ι.symm (ev x (u P))‖ ≤ ε := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C n =>
      intro x
      have e : u (MvPolynomial.C n) = (n : ℂ) • (v₀ + ∑ i, v i) := by
        simp [u, smul_add, Finset.smul_sum]
      rw [e, map_smul, smul_eq_mul, map_mul, norm_mul, map_intCast]
      have h1 : ‖((n : ℤ) : Qbar l)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (PadicAlgCl l) n
      have h2 := hε x
      have h3 := norm_nonneg (ι.symm (ev x (v₀ + ∑ i, v i)))
      nlinarith
    | add p q hp hq =>
      intro x
      have e : u (p + q) = u p + u q := by
        simp only [u, map_add, add_smul, Finset.sum_add_distrib]; abel
      rw [e, map_add, map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hp x) (hq x))
    | mul_X p j hp =>
      intro x
      have e : u (p * MvPolynomial.X j) = T j (u p) := by
        simp only [u, map_add, map_sum, map_smul, hθ, hη, map_mul, MvPolynomial.aeval_X, smul_smul]
      rw [e]
      exact hT (u p) ε hp j x
  have hb0 : ι.symm (ev x₀ v₀) ≠ 0 := by
    intro h; rw [h, norm_zero] at hx₀; exact zero_ne_one hx₀
  refine ⟨Finset.univ.image (fun i => fun j => ι.symm (η i j)),
    fun z => - ∑ i ∈ Finset.univ.filter (fun i => (fun j => ι.symm (η i j)) = z),
      ι.symm (ev x₀ (v i)) / ι.symm (ev x₀ v₀), ?_, ?_⟩
  · intro z hz
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hz
    obtain ⟨i, rfl⟩ := hz
    exact ⟨i, rfl⟩
  · intro P
    have key : ∑ z ∈ Finset.univ.image (fun i => fun j => ι.symm (η i j)),
        (- ∑ i ∈ Finset.univ.filter (fun i => (fun j => ι.symm (η i j)) = z),
          ι.symm (ev x₀ (v i)) / ι.symm (ev x₀ v₀)) * MvPolynomial.aeval z P
        = - ∑ i, ι.symm (ev x₀ (v i)) / ι.symm (ev x₀ v₀) *
            MvPolynomial.aeval (fun j => ι.symm (η i j)) P := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun i => fun j => ι.symm (η i j))
        (t := Finset.univ.image (fun i => fun j => ι.symm (η i j)))
        (fun i hi => Finset.mem_image_of_mem _ hi), ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [neg_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [hi]
    have hexp : ι.symm (ev x₀ (u P)) =
        (MvPolynomial.aeval (fun j => ι.symm (θ j)) P + ∑ i, ι.symm (ev x₀ (v i)) / ι.symm (ev x₀ v₀) *
            MvPolynomial.aeval (fun j => ι.symm (η i j)) P) * ι.symm (ev x₀ v₀) := by
      simp only [u, map_add, map_sum, map_smul, smul_eq_mul, map_mul, hmap, add_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    rw [key, sub_neg_eq_add]
    have h := good P x₀
    rw [hexp, norm_mul, hx₀, mul_one] at h
    exact h

end GlobalTheory.Cong
