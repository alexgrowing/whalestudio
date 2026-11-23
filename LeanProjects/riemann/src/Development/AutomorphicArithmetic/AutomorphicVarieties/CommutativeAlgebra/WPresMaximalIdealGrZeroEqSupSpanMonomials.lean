import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem UpperTheory.V.Alg.monomial_mem_weight_zero {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X)
    (m : σ →₀ ℕ) (hm : Finsupp.weight wt m = 0) : (monomial m (1 : O) : MvPowerSeries σ O) ∈ wtPart O wt 0 := by
  classical
  intro n hn
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact hn hm

theorem UpperTheory.V.Alg.wPres_maximalIdeal_gr_zero_eq_sup_span_monomials :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ [IsCO O (W.gr 0)], (∀ b : W.gr 0, b ∈ maximalIdeal (W.gr 0) ↔ ((b : W.A) : R) ∈ maximalIdeal R) ∧
      ∃ u : Finset (W.gr 0), (∀ b ∈ u, ∃ n : W.σ →₀ ℕ, n ≠ 0 ∧ Finsupp.weight W.wt n = 0 ∧ ((b : W.A) : R) = n.prod fun s k => W.z s ^ k) ∧
        maximalIdeal (W.gr 0) = (maximalIdeal O).map (algebraMap O (W.gr 0)) ⊔ Ideal.span (u : Set (W.gr 0)) := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hz _
  classical
  let φ : W.gr 0 →ₐ[O] R :=
    { toFun := fun b => ((b : W.A) : R)
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hφ : ∀ b : W.gr 0, φ b = ((b : W.A) : R) := fun _ => rfl
  have hinj : Function.Injective φ := fun a b h => Subtype.ext (Subtype.ext h)
  have h1 : ∀ b : W.gr 0, b ∈ maximalIdeal (W.gr 0) ↔ ((b : W.A) : R) ∈ maximalIdeal R := fun b => by
    rw [← hφ, ← res_eq_zero_iff O, ← res_eq_zero_iff O, res_map]
  refine ⟨h1, ?_⟩
  let mk : ∀ f : MvPowerSeries W.σ O, f ∈ wtPart O W.wt 0 → W.gr 0 := fun f hf =>
    ⟨⟨W.π f, W.part_le_A (j := 0) ⟨f, hf, rfl⟩⟩, ⟨f, hf, rfl⟩⟩
  have hmk : ∀ f hf, φ (mk f hf) = W.π f := fun _ _ => rfl
  obtain ⟨μ, hμ, hspan⟩ := UpperTheory.V.Alg.part_span O R X W {n | n ≠ 0 ∧ Finsupp.weight W.wt n = 0} 0
    (fun n hn => hn.2)
  let U : μ → W.gr 0 := fun m => mk (monomial m.1 1) (UpperTheory.V.Alg.monomial_mem_weight_zero W.wt m.1 (hμ m.2).2)
  have hU : ∀ m : μ, φ (U m) = m.1.prod fun s k => W.z s ^ k := fun m => by
    show W.π (monomial m.1 1) = _
    rw [monomial_one_eq, Finsupp.prod, Finsupp.prod, map_prod]
    simp only [map_pow, WPres.z]
  have hUm : ∀ m : μ, U m ∈ maximalIdeal (W.gr 0) := fun m => by
    rw [h1, ← hφ, hU]
    obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.2 (hμ m.2).1
    exact Ideal.prod_mem _ hs (Ideal.pow_mem_of_mem _ (hz s) _
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hs)))
  have hle : Ideal.span ((Finset.univ.image U : Finset (W.gr 0)) : Set (W.gr 0)) ≤ maximalIdeal (W.gr 0) := by
    rw [Ideal.span_le]
    intro b hb
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hb)
    exact hUm m
  refine ⟨Finset.univ.image U, fun b hb => ?_, le_antisymm (fun b hb => ?_) (sup_le ?_ hle)⟩
  · obtain ⟨m, -, rfl⟩ := Finset.mem_image.1 hb
    exact ⟨m.1, (hμ m.2).1, (hμ m.2).2, hU m⟩
  · obtain ⟨f, hf, hfb⟩ : ((b : W.A) : R) ∈ W.part 0 := b.2
    obtain ⟨c, hc, hsum⟩ := hspan (f - C (constantCoeff f)) (fun n hn => by
      rw [map_sub, coeff_C]
      by_cases h0 : n = 0
      · subst h0; simp
      · rw [if_neg h0, sub_zero]
        exact hf n fun h => hn ⟨h0, h⟩)
    have hb' : b - algebraMap O (W.gr 0) (constantCoeff f) = ∑ m : μ, mk (c m.1) (hc m.1) * U m := by
      apply hinj
      have h2 := congrArg W.π hsum
      rw [map_sub, map_sum, ← Finset.sum_coe_sort] at h2
      rw [map_sub, map_sum, AlgHom.commutes, hφ, ← hfb, ← W.π.commutes]
      simp only [map_mul] at h2 ⊢
      exact h2
    have hs : b - algebraMap O (W.gr 0) (constantCoeff f) ∈
        Ideal.span ((Finset.univ.image U : Finset (W.gr 0)) : Set (W.gr 0)) := by
      rw [hb']
      exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_left _ _
        (Ideal.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem U (Finset.mem_univ m))))
    have h3 : algebraMap O (W.gr 0) (constantCoeff f) ∈ maximalIdeal (W.gr 0) := by
      simpa using Ideal.sub_mem _ hb (hle hs)
    have h4 : constantCoeff f ∈ maximalIdeal O := fun h => h3 (h.map _)
    rw [← add_sub_cancel (algebraMap O (W.gr 0) (constantCoeff f)) b]
    exact Submodule.add_mem_sup (Ideal.mem_map_of_mem _ h4) hs
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha h
    exact ha (IsLocalHom.map_nonunit a h)
