import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.VecZero
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitOnOfDisj

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct UpperTheory.Gal.crystallineComparison UpperTheory.Ru.crystallineComparison

theorem UpperTheory.linear_combination_transfer_of_projector_relations :
    ∀ {A : Type} [CommRing A] {H H' : Type 1} [AddCommGroup H] [Module A H] [AddCommGroup H'] [Module A H']
        {J ι : Type} [Fintype J] [Fintype ι] {I : J → Type} [∀ i, Fintype (I i)] (G : H →ₗ[A] H') (P : ∀ i, I i → (H →ₗ[A] H'))
        (Ev : ι → H) (Wc : J → ι → H) (β γ L R : A) (σ : J → ℤ) (ρ : J → A) (cc : J → ι → A) (Z : J → H)
        (_ : ∀ i k, β • G (Wc i k) = γ • ∑ a, P i a (Ev k))
        (_ : ∀ i, (L * ρ i) • ∑ k, cc i k • Ev k = R • Z i)
        (_ : ∑ x : Σ i, I i, σ x.1 • P x.1 x.2 (Z x.1) = 0),
        (L * β) • G (∑ q : J × ι, ((σ q.1 : A) * ρ q.1 * cc q.1 q.2) • Wc q.1 q.2) = 0 := by
  intro A _ H H' _ _ _ _ J ι _ _ I _ G P Ev Wc β γ L R σ ρ cc Z h1 h2 h3
  have hi : ∀ i, ∑ k, (L * ρ i * cc i k) • (β • G (Wc i k)) = (γ * R) • ∑ a, P i a (Z i) := by
    intro i
    have e1 : ∀ a, ∑ k, (L * ρ i * cc i k) • P i a (Ev k) = R • P i a (Z i) := by
      intro a
      have := congrArg (P i a) (h2 i)
      simp only [map_smul, map_sum, Finset.smul_sum, smul_smul] at this
      simpa only [mul_assoc] using this
    calc ∑ k, (L * ρ i * cc i k) • (β • G (Wc i k))
        = ∑ k, (L * ρ i * cc i k) • (γ • ∑ a, P i a (Ev k)) := by simp only [h1]
      _ = γ • ∑ a, ∑ k, (L * ρ i * cc i k) • P i a (Ev k) := by
          rw [Finset.sum_comm]
          simp only [Finset.smul_sum, smul_comm γ]
      _ = (γ * R) • ∑ a, P i a (Z i) := by
          rw [Finset.sum_congr rfl fun a _ => e1 a, mul_smul, ← Finset.smul_sum]
  have h3' : ∑ i, (σ i : A) • ∑ a, P i a (Z i) = 0 := by
    rw [Fintype.sum_sigma] at h3
    simpa only [Finset.smul_sum, Int.cast_smul_eq_zsmul] using h3
  calc (L * β) • G (∑ q : J × ι, ((σ q.1 : A) * ρ q.1 * cc q.1 q.2) • Wc q.1 q.2)
      = ∑ i, (σ i : A) • ∑ k, (L * ρ i * cc i k) • (β • G (Wc i k)) := by
        rw [Fintype.sum_prod_type]
        simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        congr 1
        ring
    _ = (γ * R) • ∑ i, (σ i : A) • ∑ a, P i a (Z i) := by
        simp only [hi, Finset.smul_sum (s := Finset.univ) (r := γ * R), smul_comm (γ * R)]
    _ = 0 := by rw [h3', smul_zero]
