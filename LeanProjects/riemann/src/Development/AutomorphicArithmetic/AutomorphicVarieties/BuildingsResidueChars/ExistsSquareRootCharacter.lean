import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.AdjointLowWeight.SymmetricCubeSymplecticSimilitude

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

private theorem sqrt_ex {O : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O] (h2 : IsUnit (2 : O))
    (a : O) (ha : residue O a = 1) : ∃ x : O, x ^ 2 = a ∧ residue O x = 1 := by
  haveI : HenselianRing O (maximalIdeal O) := IsAdicComplete.henselianRing O (maximalIdeal O)
  have hev : eval 1 (X ^ 2 - C a) ∈ maximalIdeal O := by
    simp only [eval_sub, eval_pow, eval_X, eval_C, one_pow]
    rw [← residue_eq_zero_iff, map_sub, map_one, ha, sub_self]
  have hd : eval 1 (derivative (X ^ 2 - C a)) = (2 : O) := by
    simp
    exact one_add_one_eq_two
  obtain ⟨x, hx, hx1⟩ := HenselianRing.is_henselian (X ^ 2 - C a) (monic_X_pow_sub_C a two_ne_zero) 1 hev
    (by rw [hd]; exact h2.map _)
  refine ⟨x, ?_, ?_⟩
  · simpa [sub_eq_zero] using hx
  · rw [← sub_eq_zero, ← map_one (residue O), ← map_sub, residue_eq_zero_iff]
    exact hx1

private theorem add_unit {O : Type} [CommRing O] [IsLocalRing O] (h2 : IsUnit (2 : O)) {x y : O}
    (hx : residue O x = 1) (hy : residue O y = 1) : IsUnit (x + y) := by
  rw [← residue_ne_zero_iff_isUnit, map_add, hx, hy]
  have h2' : residue O (2 : O) = 1 + 1 := by
    rw [← map_one (residue O), ← map_add, one_add_one_eq_two]
  rw [← h2']
  exact (residue_ne_zero_iff_isUnit (2 : O)).mpr h2

private theorem sqrt_uniq {O : Type} [CommRing O] [IsLocalRing O] (h2 : IsUnit (2 : O)) {x y : O}
    (hx : residue O x = 1) (hy : residue O y = 1) (h : x ^ 2 = y ^ 2) : x = y := by
  have hu := add_unit h2 hx hy
  have hz : (x - y) * (x + y) = 0 := by linear_combination h
  exact sub_eq_zero.mp (hu.mul_left_eq_zero.mp hz)

theorem UpperTheory.exists_square_root_character :
    UpperTheory.V.Sd.S3.SqrtChar := by
  intro O _ _ _ h2 Γ _ _ μ hμ hc
  have ex : ∀ g, ∃ x : O, x ^ 2 = (μ g : O) ∧ residue O x = 1 := fun g => sqrt_ex h2 _ (hμ g)
  choose s hs1 hs2 using ex
  have hsu : ∀ g, IsUnit (s g) := fun g =>
    (residue_ne_zero_iff_isUnit _).mp (by rw [hs2 g]; exact one_ne_zero)
  let η : Γ →* Oˣ :=
    { toFun := fun g => (hsu g).unit
      map_one' := by
        apply Units.ext
        show s 1 = 1
        exact sqrt_uniq h2 (hs2 1) (map_one _) (by rw [hs1, map_one, Units.val_one, one_pow])
      map_mul' := by
        intro g k
        apply Units.ext
        show s (g * k) = s g * s k
        refine sqrt_uniq h2 (hs2 _) (by rw [map_mul, hs2, hs2, one_mul]) ?_
        rw [mul_pow, hs1, hs1, hs1, map_mul, Units.val_mul] }
  refine ⟨η, ?_, ?_, ?_, ?_⟩
  · intro g
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact hs1 g
  · intro g
    exact hs2 g
  · intro N
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro y
    rw [isOpen_iff_forall_mem_open]
    intro g0 hg0
    refine ⟨_, ?_, (hc N).isOpen_fiber (Ideal.Quotient.mk _ (μ g0 : O)), rfl⟩
    intro g hg
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq] at hg hg0 ⊢
    rw [← hg0]
    show Ideal.Quotient.mk (maximalIdeal O ^ N) (s g) = Ideal.Quotient.mk (maximalIdeal O ^ N) (s g0)
    rw [Ideal.Quotient.eq] at hg ⊢
    obtain ⟨w, hw⟩ := (add_unit h2 (hs2 g) (hs2 g0)).exists_right_inv
    have hd : s g - s g0 = ((μ g : O) - μ g0) * w := by
      rw [← hs1 g, ← hs1 g0]
      linear_combination (-(s g - s g0)) * hw
    rw [hd]
    exact Ideal.mul_mem_right _ _ hg
  · intro g hg
    apply Units.ext
    show s g = 1
    exact sqrt_uniq h2 (hs2 g) (map_one _) (by rw [hs1, hg, Units.val_one, one_pow])
