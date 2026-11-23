import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.IftSubstLow

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem lin_mul {E τ : Type} [CommRing E] (i : τ) (f g : MvPowerSeries τ E)
    (hf : MvPowerSeries.constantCoeff f = 0) (hg : MvPowerSeries.constantCoeff g = 0) :
    MvPowerSeries.coeff (Finsupp.single i 1) (f * g) = 0 := by
  classical
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have h := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  by_cases h1 : p.1 = 0
  · rw [h1, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_mul]
  · have h2 : p.2 = 0 := by
      have hd := congrArg Finsupp.degree h
      rw [map_add, Finsupp.degree_single] at hd
      have : Finsupp.degree p.1 ≠ 0 := fun h0 => h1 ((Finsupp.degree_eq_zero_iff _).1 h0)
      exact (Finsupp.degree_eq_zero_iff _).1 (by omega)
    rw [h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg, mul_zero]

private theorem lin_smul {O A τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]
    (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (n : τ →₀ ℕ) (c : O) (f : A) :
    MvPowerSeries.coeff n (φ (c • f)) = algebraMap O (FractionRing O) c * MvPowerSeries.coeff n (φ f) := by
  rw [map_smul, ← algebraMap_smul (FractionRing O) c, map_smul, smul_eq_mul]

private theorem lin_sat {O A τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] (x : A →ₐ[O] O)
    (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O))
    (hc : ∀ f, MvPowerSeries.constantCoeff (φ f) = algebraMap O (FractionRing O) (x f)) (i : τ) (f : A)
    (hf : f ∈ satSq x) : MvPowerSeries.coeff (Finsupp.single i 1) (φ f) = 0 := by
  obtain ⟨c, hc0, h⟩ := hf
  have key : ∀ g ∈ RingHom.ker x * RingHom.ker x, MvPowerSeries.coeff (Finsupp.single i 1) (φ g) = 0 := by
    intro g hg
    refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [map_mul]
      exact lin_mul i _ _ (by rw [hc, (RingHom.mem_ker).1 ha, map_zero]) (by rw [hc, (RingHom.mem_ker).1 hb, map_zero])
    · rw [map_add, map_add, ha, hb, add_zero]
  have h2 := key _ (by rwa [sq] at h)
  rw [lin_smul] at h2
  exact (mul_eq_zero.1 h2).resolve_left fun h0 => hc0 (IsFractionRing.injective O (FractionRing O) (by rw [h0, map_zero]))

private theorem lin_proj {O A τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O))
    (hg : ∀ j, ∀ f ∈ 𝒜 j, φ f ∈ wtPart (FractionRing O) wt j) (i : τ) (hi : wt i = 0) (f : A) :
    MvPowerSeries.coeff (Finsupp.single i 1) (φ (DirectSum.decompose 𝒜 f 0 : A)) =
      MvPowerSeries.coeff (Finsupp.single i 1) (φ f) := by
  induction f using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous j a =>
    by_cases hj : j = 0
    · subst hj
      rw [DirectSum.decompose_of_mem_same 𝒜 a.2]
    · rw [DirectSum.decompose_of_mem_ne 𝒜 a.2 hj, map_zero, map_zero]
      exact (hg j a a.2 _ (by simp [Finsupp.weight_single, hi, Ne.symm hj])).symm
  | add a b ha hb => simp [DirectSum.decompose_add, ha, hb]

private theorem lin_span {O A τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A]
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (x : A →ₐ[O] O) (wt : τ → ℤ)
    (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)) (h : IsChart 𝒜 x wt φ) {m : ℕ} (Z : Fin m → A)
    (hZ : SpansCot x 𝒜 0 Z) (i : τ) (hi : wt i = 0) :
    ∃ c : Fin m → FractionRing O, ∀ i', MvPowerSeries.coeff (Finsupp.single i' 1) (∑ k, c k • φ (Z k)) =
        MvPowerSeries.coeff (Finsupp.single i' 1) (MvPowerSeries.X i : MvPowerSeries τ (FractionRing O)) := by
  classical
  obtain ⟨f, hf, hf'⟩ := h.onto i
  set f0 : A := (DirectSum.decompose 𝒜 f 0 : A) with hf0
  have hm0 : f0 ∈ 𝒜 0 := (DirectSum.decompose 𝒜 f 0).2
  set g : A := f0 - algebraMap O A (x f0) with hgdef
  have hg0 : g ∈ 𝒜 0 := sub_mem hm0 (SetLike.algebraMap_mem_graded 𝒜 _)
  have hgx : x g = 0 := by simp [hgdef]
  have hgl : ∀ i', MvPowerSeries.coeff (Finsupp.single i' 1) (φ g) =
      MvPowerSeries.coeff (Finsupp.single i' 1) (φ f0) := by
    intro i'
    rw [hgdef, map_sub, map_sub, AlgHom.commutes, MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, if_neg (by simp),
      sub_zero]
  obtain ⟨c, hc, hs⟩ := hZ _ ⟨g, ⟨hg0, hgx⟩, rfl⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hs
  have hsat : (∑ k, a k • Z k) - c • g ∈ satSq x := by
    rw [← Submodule.Quotient.eq]
    show (satSq x).mkQ _ = (satSq x).mkQ _
    rw [map_sum, map_smul, ← ha]
    simp only [map_smul]
  have hc' : algebraMap O (FractionRing O) c ≠ 0 := fun h0 =>
    hc (IsFractionRing.injective O (FractionRing O) (by rw [h0, map_zero]))
  refine ⟨fun k => (algebraMap O (FractionRing O) c * MvPowerSeries.coeff (Finsupp.single i 1) (φ f))⁻¹ *
    algebraMap O (FractionRing O) (a k), fun i' => ?_⟩
  have h1 := lin_sat x φ h.const i' _ hsat
  rw [map_sub, map_sub, sub_eq_zero, lin_smul, map_sum, map_sum, hgl] at h1
  simp only [lin_smul] at h1
  simp only [map_sum, map_smul, smul_eq_mul, mul_assoc]
  rw [← Finset.mul_sum, h1, MvPowerSeries.coeff_X]
  by_cases hii : i' = i
  · subst hii
    rw [if_pos rfl, hf0, lin_proj 𝒜 wt φ h.graded i' hi, inv_mul_cancel₀ (mul_ne_zero hc' hf)]
  · rw [if_neg (fun h0 => hii (Finsupp.single_left_injective one_ne_zero h0))]
    have : MvPowerSeries.coeff (Finsupp.single i' 1) (φ f0) = 0 := by
      by_cases hw : wt i' = 0
      · rw [hf0, lin_proj 𝒜 wt φ h.graded i' hw, hf' i' hii]
      · exact h.graded 0 f0 hm0 _ (by simpa [Finsupp.weight_single] using hw)
    rw [this, mul_zero, mul_zero]

theorem UpperTheory.V.Alg.M.cut_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    M1 Q → ∃ (τ : Type) (_ : Fintype τ) (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ ∧
      (∀ i, φ (Q.Z i) = 0) ∧ ∀ j, Nat.card {i // wt i = j} = mDims r s r' s' 0 j := by
  classical
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x _ r s r' s' m Q ⟨_, ⟨τ, _, wt, φ, h, hcard⟩, _, _, hZ⟩
  obtain ⟨ψ, hψ1, hψ2, hψ3, hψ4⟩ := ift_holds (FractionRing O) τ (Fin m) ℤ wt (fun k => φ (Q.Z k))
    (fun k => ⟨h.graded 0 _ (Q.hZ k).1, by rw [h.const, (Q.hZ k).2, map_zero]⟩)
    (by rw [hcard 0]; simp [mDims]) (lin_span 𝒜 x wt φ h Q.Z hZ)
  refine ⟨{i // wt i ≠ 0}, inferInstance, fun i => wt i, (ψ.restrictScalars O).comp φ,
    ⟨fun j f hf => hψ1 j _ (h.graded j f hf), fun f => (hψ3 _).trans (h.const f), fun i => ?_, fun i => ?_⟩,
    hψ2, fun j => ?_⟩
  · obtain ⟨f, hf, hf'⟩ := h.onto i.1
    refine ⟨f, fun h0 => hf ((hψ4 _ i).symm.trans h0), fun i' hi' => (hψ4 _ i').trans (hf' _ fun h0 => hi' (Subtype.ext h0))⟩
  · have h1 : Nat.card {i' // wt i' = wt i} ≠ 0 := by
      haveI : Nonempty {i' // wt i' = wt i} := ⟨⟨i, rfl⟩⟩
      exact Nat.card_pos.ne'
    rw [hcard] at h1
    have h2 := i.2
    by_contra hn
    push Not at hn
    simp [mDims, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2, h2] at h1
  · by_cases hj : j = 0
    · subst hj
      haveI : IsEmpty {i : {i // wt i ≠ 0} // wt i = 0} := ⟨fun i => i.1.2 i.2⟩
      simp [mDims]
    · have : mDims r s r' s' 0 j = mDims r s r' s' m j := by simp [mDims, hj]
      rw [this, ← hcard]
      exact Nat.card_congr ⟨fun i => ⟨i.1.1, i.2⟩, fun i => ⟨⟨i.1, by rw [i.2]; exact hj⟩, i.2⟩, fun _ => rfl, fun _ => rfl⟩
