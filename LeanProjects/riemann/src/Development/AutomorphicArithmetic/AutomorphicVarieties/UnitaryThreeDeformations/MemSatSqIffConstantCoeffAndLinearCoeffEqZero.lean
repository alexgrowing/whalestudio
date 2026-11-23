import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AbsDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerPow
open IsLocalRing MvPowerSeries UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia.Abs

private lemma order_of_mem_sq {O σ : Type} [CommRing O] (I : Ideal (MvPowerSeries σ O))
    (hI : ∀ f ∈ I, constantCoeff f = 0) : ∀ f ∈ I ^ 2, ((2 : ℕ) : ℕ∞) ≤ f.order := by
  intro x hx
  rw [pow_two] at hx
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) ?_
  · refine le_trans ?_ le_order_mul
    have h := add_le_add (one_le_order_iff_constCoeff_eq_zero.2 (hI a ha))
      (one_le_order_iff_constCoeff_eq_zero.2 (hI b hb))
    rwa [one_add_one_eq_two] at h
  · intro f g hf hg
    exact le_trans (le_min hf hg) min_order_le_add

private lemma mem_sq_of_coeff {O σ : Type} [CommRing O] [Fintype σ] (I : Ideal (MvPowerSeries σ O))
    (hI : ∀ i, (X i : MvPowerSeries σ O) ∈ I) (f : MvPowerSeries σ O)
    (hf : ∀ m : σ →₀ ℕ, m.degree < 2 → coeff m f = 0) : f ∈ I ^ 2 := by
  classical
  have key : ∃ μ : Finset (σ →₀ ℕ), (μ : Set _) ⊆ {m : σ →₀ ℕ | 2 ≤ m.degree} ∧
      ∀ f : MvPowerSeries σ O, (∀ m, m ∉ {m : σ →₀ ℕ | 2 ≤ m.degree} → coeff m f = 0) →
      ∃ b : (σ →₀ ℕ) → MvPowerSeries σ O, (∀ m, b m ∈ wtPart O (fun _ : σ => (0 : ℤ)) 0) ∧
        f = ∑ m ∈ μ, b m * monomial m 1 :=
    part_span O (MvPowerSeries σ O) ℤ (WPres.free O fun _ : σ => (0 : ℤ))
      {m : σ →₀ ℕ | 2 ≤ m.degree} 0 (fun (m : σ →₀ ℕ) _ => by
        show Finsupp.weight (fun _ : σ => (0 : ℤ)) m = 0
        simp [Finsupp.weight_apply, Finsupp.sum])
  obtain ⟨μ, hμ, hs⟩ := key
  obtain ⟨b, -, hb⟩ := hs f (fun m hm => hf m (not_le.1 hm))
  rw [hb]
  refine Ideal.sum_mem _ fun m hm => Ideal.mul_mem_left _ _ ?_
  have hm2 : 2 ≤ m.degree := hμ hm
  refine Ideal.pow_le_pow_right hm2 ?_
  rw [MvPowerSeries.monomial_one_eq, Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (hI i) _

private lemma low_degree {σ : Type} (m : σ →₀ ℕ) (hm : m.degree < 2) : m = 0 ∨ ∃ i, m = Finsupp.single i 1 := by
  rcases (show m.degree = 0 ∨ m.degree = 1 by omega) with h | h
  · exact Or.inl ((Finsupp.degree_eq_zero_iff m).1 h)
  · have : m ∈ Set.range (fun i : σ => Finsupp.single i 1) := by
      rw [Finsupp.range_single_one]; exact h
    obtain ⟨i, hi⟩ := this
    exact Or.inr ⟨i, hi.symm⟩

theorem UpperTheory.mem_satSq_iff_constantCoeff_and_linearCoeff_eq_zero :
    ∀ (O : Type) [CommRing O] [IsDomain O] (σ : Type) [Fintype σ] (wt : σ → ℤ) (f : FA O wt),
        f ∈ satSq (x0 O wt) ↔ constantCoeff (ser f) = 0 ∧ ∀ i, coeff (Finsupp.single i 1) (ser f) = 0 := by
  intro O _ _ σ _ wt f
  classical
  have hk := (ker_pow O (MvPowerSeries σ O) ℤ (WPres.free O wt) (freeOrigin O wt) 2).1
  have ho : ∀ g : MvPowerSeries σ O, (WPres.free O wt).origin (freeOrigin O wt) g = constantCoeff g :=
    fun g => (WPres.free O wt).origin_π (freeOrigin O wt) g
  have hiff : ∀ g : FA O wt, g ∈ RingHom.ker (x0 O wt) ^ 2 ↔
      ser g ∈ RingHom.ker ((WPres.free O wt).origin (freeOrigin O wt)) ^ 2 := fun g => by
    show g ∈ RingHom.ker ((WPres.free O wt).originA (freeOrigin O wt)) ^ 2 ↔ _
    rw [← hk]
    rfl
  constructor
  · rintro ⟨c, hc, hf⟩
    have h2 := order_of_mem_sq _ (fun g hg => by rw [← ho]; exact hg) _ ((hiff _).1 hf)
    have h3 : ∀ m : σ →₀ ℕ, m.degree < 2 → coeff m (ser f) = 0 := fun m hm => by
      have h4 : coeff m (c • ser f) = 0 :=
        coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hm) h2)
      rw [map_smul, smul_eq_mul] at h4
      exact (mul_eq_zero.1 h4).resolve_left hc
    exact ⟨h3 0 (by simp), fun i => h3 _ (by simp)⟩
  · rintro ⟨h0, h1⟩
    refine ⟨1, one_ne_zero, ?_⟩
    rw [one_smul, hiff]
    refine mem_sq_of_coeff _ (fun i => ?_) _ (fun m hm => ?_)
    · rw [RingHom.mem_ker, ho]; simp
    · rcases low_degree m hm with rfl | ⟨i, rfl⟩
      · exact h0
      · exact h1 i
