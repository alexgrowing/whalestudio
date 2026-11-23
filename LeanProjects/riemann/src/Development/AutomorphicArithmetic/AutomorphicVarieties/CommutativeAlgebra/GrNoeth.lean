import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrGen

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.gr_noeth :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → IsNoetherianRing W.A ∧ Algebra.FiniteType (W.gr 0) W.A ∧ ∀ j, ∃ s : Finset W.A, (∀ a ∈ s, a ∈ W.gr j) ∧ W.gr j = W.gr 0 * Submodule.span O (s : Set W.A) := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hz
  classical
  haveI := W.fin
  haveI hco : IsCO O (W.gr 0) := wPres_gr_zero_isCO_of_mem_maximalIdeal O X R W hz
  haveI : IsNoetherianRing (W.gr 0) := IsCO.toIsNoetherian O
  have hgen : Algebra.adjoin (W.gr 0) (Set.range W.zA) = ⊤ := by
    rw [eq_top_iff]
    rintro a -
    have ha : a ∈ Algebra.adjoin O ((W.gr 0 : Set W.A) ∪ Set.range W.zA) := by
      rw [gr_gen O R X W]
      trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with hx | ⟨i, rfl⟩
      · have e : algebraMap (W.gr 0) W.A ⟨x, hx⟩ = x := rfl
        rw [← e]
        exact Subalgebra.algebraMap_mem _ _
      · exact Algebra.subset_adjoin ⟨i, rfl⟩
    | algebraMap r =>
      have hr : algebraMap O W.A r ∈ W.gr 0 := SetLike.algebraMap_mem_graded W.gr r
      have e : algebraMap (W.gr 0) W.A ⟨_, hr⟩ = algebraMap O W.A r := rfl
      rw [← e]
      exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy
  haveI hft : Algebra.FiniteType (W.gr 0) W.A :=
    ⟨⟨Finset.univ.image W.zA, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hgen]⟩⟩
  refine ⟨Algebra.FiniteType.isNoetherianRing (W.gr 0) W.A, hft, ?_⟩
  intro j
  have hmono : ∀ m : W.σ →₀ ℕ, monomial m (1 : O) ∈ wtPart O W.wt (Finsupp.weight W.wt m) := by
    intro m n hn
    rw [coeff_monomial, if_neg]
    rintro rfl
    exact hn rfl
  obtain ⟨μ, hμS, hμ⟩ := part_span O R X W {n | Finsupp.weight W.wt n = j} j (fun n hn => hn)
  let mA : (W.σ →₀ ℕ) → W.A := fun m =>
    ⟨W.π (monomial m 1), W.part_le_A (Submodule.mem_map_of_mem (hmono m))⟩
  have hsj : ∀ a ∈ μ.image mA, a ∈ W.gr j := by
    intro a ha
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp ha
    have hw : Finsupp.weight W.wt m = j := hμS hm
    show (W.π (monomial m 1) : R) ∈ W.part j
    rw [← hw]
    exact Submodule.mem_map_of_mem (hmono m)
  refine ⟨μ.image mA, hsj, ?_⟩
  apply le_antisymm
  · intro a ha
    have ha' : (a : R) ∈ W.part j := ha
    obtain ⟨f, hf, hfa⟩ := Submodule.mem_map.mp ha'
    obtain ⟨b, hb, hfb⟩ := hμ f (fun n hn => hf n hn)
    let bA : (W.σ →₀ ℕ) → W.A := fun m =>
      ⟨W.π (b m), W.part_le_A (Submodule.mem_map_of_mem (hb m))⟩
    have hsum : a = ∑ m ∈ μ, bA m * mA m := by
      apply Subtype.ext
      rw [← hfa]
      simp [hfb, map_sum, map_mul, bA, mA]
    rw [hsum]
    refine Submodule.sum_mem _ fun m hm => Submodule.mul_mem_mul ?_ ?_
    · show (W.π (b m) : R) ∈ W.part 0
      exact Submodule.mem_map_of_mem (hb m)
    · exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem mA hm))
  · rw [Submodule.mul_le]
    intro x hx y hy
    have hy' : y ∈ W.gr j := (Submodule.span_le.mpr fun z hz => hsj z hz) hy
    simpa using SetLike.GradedMul.mul_mem hx hy'
