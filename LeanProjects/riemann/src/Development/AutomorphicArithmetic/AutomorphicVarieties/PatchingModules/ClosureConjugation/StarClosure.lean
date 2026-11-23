import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

section
variable {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R]
  [Algebra O R] (n : ℕ)

private theorem star_closure_conj_cont : Continuous F.conj := by
  apply Continuous.subtype_mk
  fun_prop

end

private theorem exists_unit_valuation_le_subset_nhds {l : ℕ} [Fact l.Prime] (F : GFrame l) (N : ℕ) (H : OpenNormalSubgroup F.G₀) :
    ∃ H' : OpenNormalSubgroup F.G₀, ∀ h ∈ H', (F.conj h)⁻¹ ∈ H ∧ ((F.ε h : ℤ_[l]) - 1) ∈ Ideal.span {(l : ℤ_[l]) ^ N} := by
  let φ : F.G₀ →* (ZMod (l ^ N))ˣ :=
    (Units.map (PadicInt.toZModPow N : ℤ_[l] →+* ZMod (l ^ N)).toMonoidHom).comp (F.ε.comp F.η.ker.subtype)
  have hK : ∀ h : F.G₀, h ∈ φ.ker ↔ ((F.ε h : ℤ_[l]) - 1) ∈ Ideal.span {(l : ℤ_[l]) ^ N} := by
    intro h
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero, MonoidHom.mem_ker, Units.ext_iff]
    rfl
  let S0 : Subgroup F.G₀ := φ.ker ⊓ Subgroup.comap F.conj (H : Subgroup F.G₀)
  have hN : S0.Normal := by
    haveI : (Subgroup.comap F.conj (H : Subgroup F.G₀)).Normal := Subgroup.Normal.comap H.isNormal' F.conj
    exact Subgroup.normal_inf_normal _ _
  have hcont : Continuous (fun g : F.G₀ => ((F.ε g : ℤ_[l]ˣ) : ℤ_[l])) :=
    Units.continuous_val.comp (F.ε_cont.comp continuous_subtype_val)
  have hopen : IsOpen (S0 : Set F.G₀) := by
    apply Subgroup.isOpen_of_mem_nhds S0 (g := 1)
    apply Filter.inter_mem
    · have hb : (fun g : F.G₀ => ((F.ε g : ℤ_[l]ˣ) : ℤ_[l])) ⁻¹' Metric.ball 1 ((l : ℝ) ^ (-(N : ℤ))) ∈ nhds (1 : F.G₀) := by
        apply hcont.continuousAt.preimage_mem_nhds
        have h1 : ((F.ε ((1 : F.G₀) : F.Γ) : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by simp
        rw [h1]
        apply Metric.ball_mem_nhds
        have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
        positivity
      apply Filter.mem_of_superset hb
      intro g hg
      simp only [Set.mem_preimage, Metric.mem_ball, dist_eq_norm] at hg
      show g ∈ φ.ker
      rw [hK, ← PadicInt.norm_le_pow_iff_mem_span_pow]
      exact hg.le
    · apply (H.isOpen'.preimage (star_closure_conj_cont F)).mem_nhds
      show F.conj 1 ∈ (H : Subgroup F.G₀)
      rw [map_one]
      exact one_mem _
  refine ⟨⟨⟨S0, hopen⟩, hN⟩, ?_⟩
  intro h hh
  have hh' : h ∈ S0 := hh
  refine ⟨inv_mem hh'.2, (hK h).1 hh'.1⟩

theorem UpperTheory.V.Pa.star_closure :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (n : ℕ) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (I : Ideal R) (S : Set (MonoidAlgebra R F.G₀)), (l : R) ∈ I → (∀ z ∈ S, F.star O R n z ∈ TwoSidedIdeal.span S) → ∀ y ∈ closureIdeal I S, F.star O R n y ∈ closureIdeal I S := by
  intro l _ F n O _ _ R _ _ I S hl hS y hy
  have hadd : ∀ y z, F.star O R n (y + z) = F.star O R n y + F.star O R n z := by
    intro y z
    simp [GFrame.star, map_add]
  have hneg : ∀ y, F.star O R n (-y) = -F.star O R n y := by
    intro y
    simp [GFrame.star, map_neg]
  have hsub : ∀ y z, F.star O R n (y - z) = F.star O R n y - F.star O R n z := by
    intro y z
    simp [GFrame.star, map_sub]
  have hzero : F.star O R n 0 = 0 := by simp [GFrame.star]
  have hmul : ∀ y z, F.star O R n (y * z) = F.star O R n z * F.star O R n y := by
    intro y z
    simp [GFrame.star, map_mul]
  have hsingle : ∀ (g : F.G₀) (b : R), F.star O R n (MonoidAlgebra.single g b) =
      MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
    intro g b
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]
  have h1 : F.star O R n 1 = 1 := by simp [GFrame.star, map_one]
  simp only [closureIdeal, TwoSidedIdeal.mem_iInf] at hy ⊢
  intro N H
  obtain ⟨H', hH'⟩ := exists_unit_valuation_le_subset_nhds F N H
  set T := TwoSidedIdeal.span (S ∪ {z : MonoidAlgebra R F.G₀ | ∃ a ∈ I ^ N, z = MonoidAlgebra.single 1 a} ∪
    {z : MonoidAlgebra R F.G₀ | ∃ h ∈ H, z = MonoidAlgebra.single h 1 - 1}) with hT
  have hJ : ∀ a ∈ I ^ N, MonoidAlgebra.single (1 : F.G₀) a ∈ T := by
    intro a ha
    apply TwoSidedIdeal.subset_span
    exact Or.inl (Or.inr ⟨a, ha, rfl⟩)
  have hKH : ∀ h ∈ H, MonoidAlgebra.single h (1 : R) - 1 ∈ T := by
    intro h hh
    apply TwoSidedIdeal.subset_span
    exact Or.inr ⟨h, hh, rfl⟩
  have hST : TwoSidedIdeal.span S ≤ T := by
    rw [TwoSidedIdeal.span_le]
    exact (Set.subset_union_left.trans Set.subset_union_left).trans TwoSidedIdeal.subset_span
  have heps : ∀ h ∈ H', ((F.eps O R h : Rˣ) : R) - 1 ∈ I ^ N := by
    intro h hh
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (hH' h hh).2
    have hv : ((F.eps O R h : Rˣ) : R) = algebraMap O R (algebraMap ℤ_[l] O ((F.ε h : ℤ_[l]ˣ) : ℤ_[l])) := by
      simp [GFrame.eps, pushCh]
    rw [hv, eq_add_of_sub_eq' ht.symm]
    simp only [map_add, map_mul, map_pow, map_natCast, map_one, add_sub_cancel_left]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hl N)
  refine TwoSidedIdeal.span_induction (p := fun x _ => F.star O R n x ∈ T) ?_ ?_ ?_ ?_ ?_ ?_ (hy N H')
  · rintro x ((hx | ⟨a, ha, rfl⟩) | ⟨h, hh, rfl⟩)
    · exact hST (hS x hx)
    · rw [hsingle]
      simpa using hJ a ha
    · have hk : (h ^ (1 - (n : ℤ))) ∈ H' := zpow_mem hh _
      have hu := heps _ hk
      rw [map_zpow] at hu
      rw [hsub, hsingle, one_mul, h1]
      set u : R := ((F.eps O R h ^ (1 - (n : ℤ)) : Rˣ) : R)
      have hsplit : MonoidAlgebra.single (F.conj h)⁻¹ u - 1 =
          MonoidAlgebra.single (F.conj h)⁻¹ (1 : R) * MonoidAlgebra.single 1 (u - 1) +
            (MonoidAlgebra.single (F.conj h)⁻¹ (1 : R) - 1) := by
        rw [MonoidAlgebra.single_mul_single, mul_one, one_mul, MonoidAlgebra.single_sub]
        abel
      rw [hsplit]
      exact T.add_mem (T.mul_mem_left _ _ (hJ _ hu)) (hKH _ (hH' h hh).1)
  · rw [hzero]
    exact T.zero_mem
  · intro x z _ _ hx hz
    rw [hadd]
    exact T.add_mem hx hz
  · intro x _ hx
    rw [hneg]
    exact T.neg_mem hx
  · intro a x _ hx
    rw [hmul]
    exact T.mul_mem_right _ _ hx
  · intro b x _ hx
    rw [hmul]
    exact T.mul_mem_left _ _ hx
