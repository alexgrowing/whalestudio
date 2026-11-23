import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOpenPartialHomeomorphAnalytic

open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory

open AffinePoints in

theorem exists_testFunctions_subset_of_mem_nhds {A : Type*} [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] {e : A →ₐ[ℂ] ℂ} {U : Set (A →ₐ[ℂ] ℂ)} (hU : U ∈ 𝓝 e) :
    ∃ (n : ℕ) (f : Fin n → A) (ε : ℝ), 0 < ε ∧
      ∀ x : A →ₐ[ℂ] ℂ, (∀ k, ‖x (f k) - e (f k)‖ < ε) → x ∈ U := by
  obtain ⟨n, p, hp⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹Algebra.FiniteType ℂ A›
  rw [(isClosedEmbedding_coords (C := ℂ) p hp).isInducing.nhds_eq_comap, mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨n, fun k => p (MvPolynomial.X k), ε, hε, fun x hx => hVU (hb ?_)⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro k
  rw [dist_eq_norm]
  exact hx k

open AffinePoints in

theorem exists_holomorphic_section_of_etale :
    (∀ (g : ℕ) (A : Type) [CommRing A] [Algebra ℂ A] [Algebra (MvPolynomial (Fin g) ℂ) A] [IsScalarTower ℂ (MvPolynomial (Fin g) ℂ) A] [Algebra.Etale (MvPolynomial (Fin g) ℂ) A] (e : A →ₐ[ℂ] ℂ), (∀ i, e (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = 0) → ∃ (W : Set (Fin g → ℂ)) (σ : (Fin g → ℂ) → (A →ₐ[ℂ] ℂ)) (n : ℕ) (f : Fin n → A) (ε : ℝ), IsOpen W ∧ 0 ∈ W ∧ σ 0 = e ∧ 0 < ε ∧ (∀ a, DifferentiableOn ℂ (fun w => σ w a) W) ∧ (∀ w ∈ W, ∀ i, σ w (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = w i) ∧ ∀ x : A →ₐ[ℂ] ℂ, (∀ k, ‖x (f k) - e (f k)‖ < ε) → ∃ w ∈ W, x = σ w) := by
  intro g A _ _ _ _ _ e he
  let φ : MvPolynomial (Fin g) ℂ →ₐ[ℂ] A := IsScalarTower.toAlgHom ℂ _ A
  have hφ : φ.Etale := RingHom.etale_algebraMap.2 inferInstance
  have : Algebra.FiniteType ℂ A :=
    Algebra.FiniteType.trans (S := MvPolynomial (Fin g) ℂ) inferInstance inferInstance
  obtain ⟨c, hc, hcφ, han⟩ := exists_chart_of_etale φ hφ e
  have h0 : c e = 0 := by rw [hcφ]; ext i; exact he i
  obtain ⟨n, f, ε, hε, hf⟩ := exists_testFunctions_subset_of_mem_nhds (c.open_source.mem_nhds hc)
  refine ⟨c.target, c.symm, n, f, ε, c.open_target, h0 ▸ c.map_source hc, ?_, hε,
    fun a => (han a).differentiableOn, fun w hw i => ?_, fun x hx => ?_⟩
  · rw [← h0, c.left_inv hc]
  · have := c.right_inv hw
    rw [hcφ] at this
    exact congrFun this i
  · exact ⟨c x, c.map_source (hf x hx), (c.left_inv (hf x hx)).symm⟩

end GlobalTheory
