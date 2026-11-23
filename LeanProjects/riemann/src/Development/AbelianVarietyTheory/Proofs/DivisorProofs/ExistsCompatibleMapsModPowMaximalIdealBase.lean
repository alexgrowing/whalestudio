import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem exists_maximalIdeal_pow_le_map_maximalIdeal (R : Type) [CommRing R] [IsLocalRing R]
    (R' : Type) [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [Algebra R R']
    [Module.Finite R R'] :
    ∃ N : ℕ, maximalIdeal R' ^ N ≤ (maximalIdeal R).map (algebraMap R R') := by
  have hrad : maximalIdeal R' ≤ ((maximalIdeal R).map (algebraMap R R')).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hIP, hP⟩
    haveI := hP
    have hc : P.comap (algebraMap R R') = maximalIdeal R := by
      apply le_antisymm
      · exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.comap (algebraMap R R')).ne_top
      · exact Ideal.map_le_iff_le_comap.1 hIP
    have hmax : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P (by rw [hc]; infer_instance)
    exact (IsLocalRing.eq_maximalIdeal hmax).ge
  obtain ⟨n, hn⟩ := Ideal.exists_radical_pow_le_of_fg _
    (IsNoetherian.noetherian ((maximalIdeal R).map (algebraMap R R')).radical)
  exact ⟨n, (Ideal.pow_right_mono hrad n).trans hn⟩

theorem exists_compatible_maps_mod_pow_maximalIdeal_base : ∀ (R : Type) [CommRing R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [Algebra R R'] [Module.Finite R R'] (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (Γ : Type) (actC : Γ → (C' ≃ₐ[R] C')) (O : Type) [CommRing O] [Algebra R O] (i' : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C')), (∀ e x y, Ideal.Quotient.mk _ y = i' (e + 1) x → Ideal.Quotient.mk _ y = i' e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i' e x → Ideal.Quotient.mk _ (actC σ y) = i' e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i' e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i' e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R' ^ (e + 1)).map (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R')) → ∃ i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C'), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) ∧ (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (actC σ y) = i e x) ∧ (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) := by
  intro R _ _ R' _ _ _ _ _ C' _ _ _ _ Γ actC O _ _ i' hcomp hinv hsk
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le_map_maximalIdeal R R'
  have hR' : ∀ e : ℕ, maximalIdeal R' ^ (N * (e + 1) + 1) ≤
      (maximalIdeal R ^ (e + 1)).map (algebraMap R R') := by
    intro e
    calc maximalIdeal R' ^ (N * (e + 1) + 1) ≤ maximalIdeal R' ^ (N * (e + 1)) :=
          Ideal.pow_le_pow_right (Nat.le_succ _)
      _ = (maximalIdeal R' ^ N) ^ (e + 1) := pow_mul _ _ _
      _ ≤ ((maximalIdeal R).map (algebraMap R R')) ^ (e + 1) := Ideal.pow_right_mono hN _
      _ = _ := (Ideal.map_pow _ _ _).symm
  have hle : ∀ e : ℕ, (maximalIdeal R' ^ (N * (e + 1) + 1)).map (algebraMap R' C') ≤
      (maximalIdeal R ^ (e + 1)).map (algebraMap R C') := by
    intro e
    rw [Ideal.map_le_iff_le_comap]
    refine (hR' e).trans ?_
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    simp only [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact Ideal.mem_map_of_mem _ hr
  have hJ : ∀ e : ℕ, (maximalIdeal R ^ (e + 1 + 1)).map (algebraMap R C') ≤
      (maximalIdeal R ^ (e + 1)).map (algebraMap R C') :=
    fun e => Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ _))
  have hiter : ∀ a b : ℕ, a ≤ b → ∀ x y,
      Ideal.Quotient.mk ((maximalIdeal R' ^ (b + 1)).map (algebraMap R' C')) y = i' b x →
      Ideal.Quotient.mk ((maximalIdeal R' ^ (a + 1)).map (algebraMap R' C')) y = i' a x := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact fun x y h => h
    | succ b _ ih => exact fun x y h => ih x y (hcomp b x y h)
  let i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C') :=
    fun e => (Ideal.Quotient.factorₐ R (hle e)).comp (i' (N * (e + 1)))
  have hi : ∀ e x, i e x = Ideal.Quotient.factorₐ R (hle e) (i' (N * (e + 1)) x) :=
    fun _ _ => rfl
  have hlift : ∀ e x y, Ideal.Quotient.mk ((maximalIdeal R ^ (e + 1)).map (algebraMap R C')) y
      = i e x → ∃ y', Ideal.Quotient.mk ((maximalIdeal R' ^ (N * (e + 1) + 1)).map
        (algebraMap R' C')) y' = i' (N * (e + 1)) x ∧
        y - y' ∈ (maximalIdeal R ^ (e + 1)).map (algebraMap R C') := by
    intro e x y h
    obtain ⟨y', hy'⟩ := Ideal.Quotient.mk_surjective (i' (N * (e + 1)) x)
    refine ⟨y', hy', ?_⟩
    rw [← Ideal.Quotient.eq, h, hi, ← hy', Ideal.Quotient.factorₐ_apply_mk]
  refine ⟨i, ?_, ?_, ?_⟩
  · intro e x y h
    obtain ⟨y', hy', hd⟩ := hlift (e + 1) x y h
    have h2 := hiter (N * (e + 1)) (N * (e + 1 + 1)) (Nat.mul_le_mul_left _ (Nat.le_succ _)) x y' hy'
    rw [Ideal.Quotient.eq.2 (hJ e hd), hi, ← h2, Ideal.Quotient.factorₐ_apply_mk]
  · intro e σ x y h
    obtain ⟨y', hy', hd⟩ := hlift e x y h
    have hst : (maximalIdeal R ^ (e + 1)).map (algebraMap R C') ≤
        ((maximalIdeal R ^ (e + 1)).map (algebraMap R C')).comap (actC σ) := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      simp only [Ideal.mem_comap, AlgEquiv.commutes]
      exact Ideal.mem_map_of_mem _ hr
    have hσ : actC σ y - actC σ y' ∈ (maximalIdeal R ^ (e + 1)).map (algebraMap R C') := by
      rw [← map_sub]; exact hst hd
    rw [Ideal.Quotient.eq.2 hσ, hi, ← hinv (N * (e + 1)) σ x y' hy', Ideal.Quotient.factorₐ_apply_mk]
  · intro e
    obtain ⟨hsur, hker⟩ := hsk (N * (e + 1))
    set L' := Algebra.TensorProduct.lift (i' (N * (e + 1)))
      ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _
      with hL'
    have hfac : Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _)
        = (Ideal.Quotient.factorₐ R (hle e)).comp L' := by
      apply Algebra.TensorProduct.ext'
      intro a b
      rw [AlgHom.comp_apply, hL', Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul,
        map_mul, hi]
      congr 1
    rw [hfac]
    refine ⟨?_, ?_⟩
    · intro z
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨t, ht⟩ := hsur (Ideal.Quotient.mk _ c)
      exact ⟨t, by simp [ht, Ideal.Quotient.factorₐ_apply_mk]⟩
    apply le_antisymm
    · intro t ht
      rw [RingHom.mem_ker, AlgHom.comp_apply] at ht
      obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (L' t)
      have hcJ : c ∈ (maximalIdeal R ^ (e + 1)).map (algebraMap R C') := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.factorₐ_apply_mk R (hle e), hc]
        exact ht
      have hsub : (maximalIdeal R ^ (e + 1)).map (algebraMap R C') ≤
          (((maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))).map L').comap
            (Ideal.Quotient.mk ((maximalIdeal R' ^ (N * (e + 1) + 1)).map (algebraMap R' C'))) := by
        rw [Ideal.map_le_iff_le_comap]
        intro r hr
        simp only [Ideal.mem_comap, Ideal.Quotient.mk_algebraMap]
        rw [← AlgHom.commutes L' r]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hr)
      have hmem := hsub hcJ
      rw [Ideal.mem_comap, hc] at hmem
      obtain ⟨t', ht'K, ht'⟩ := (Ideal.mem_map_iff_of_surjective L' hsur).1 hmem
      have hdiff : t - t' ∈ RingHom.ker L' := by
        rw [RingHom.mem_ker, map_sub, ht', sub_self]
      rw [hker] at hdiff
      have hKK : (maximalIdeal R' ^ (N * (e + 1) + 1)).map
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R') ≤
          (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R')) := by
        rw [Ideal.map_le_iff_le_comap]
        refine (hR' e).trans ?_
        rw [Ideal.map_le_iff_le_comap]
        intro r hr
        simp only [Ideal.mem_comap, AlgHom.commutes]
        exact Ideal.mem_map_of_mem _ hr
      simpa using Ideal.add_mem _ (hKK hdiff) ht'K
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
      rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hr

end GlobalTheory
