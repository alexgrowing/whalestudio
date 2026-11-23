import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem mvPowerSeries_mem_span_X_of_constantCoeff_zero {σ R : Type} [Finite σ] [CommRing R] (h : MvPowerSeries σ R)
    (h0 : MvPowerSeries.constantCoeff h = 0) :
    h ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) := by
  classical
  have := Fintype.ofFinite σ
  have hex : ∀ d : σ →₀ ℕ, ∃ o : Option σ, d ≠ 0 → ∃ s, o = some s ∧ d s ≠ 0 := by
    intro d
    by_cases hd : d = 0
    · exact ⟨none, fun h => (h hd).elim⟩
    · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
        by_contra H
        push_neg at H
        exact hd (Finsupp.ext H)
      exact ⟨some s, fun _ => ⟨s, rfl, hs⟩⟩
  choose sel hsel using hex
  let g : σ → MvPowerSeries σ R := fun s e =>
    if sel (e + Finsupp.single s 1) = some s then MvPowerSeries.coeff (e + Finsupp.single s 1) h
    else 0
  have key : h = ∑ s, MvPowerSeries.X s * g s := by
    ext d
    rw [map_sum]
    simp_rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, one_mul]
    by_cases hd : d = 0
    · subst hd
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
      refine (Finset.sum_eq_zero fun s _ => ?_).symm
      rw [if_neg]
      simp [Finsupp.single_le_iff]
    · obtain ⟨s0, hs0, hds0⟩ := hsel d hd
      have hle0 : Finsupp.single s0 1 ≤ d := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hds0)
      rw [Finset.sum_eq_single s0]
      · rw [if_pos hle0]
        show _ = (if sel (d - Finsupp.single s0 1 + Finsupp.single s0 1) = some s0 then
          MvPowerSeries.coeff (d - Finsupp.single s0 1 + Finsupp.single s0 1) h else 0)
        rw [tsub_add_cancel_of_le hle0, if_pos hs0]
      · intro s _ hs
        split_ifs with hle
        · show (if sel (d - Finsupp.single s 1 + Finsupp.single s 1) = some s then
            MvPowerSeries.coeff (d - Finsupp.single s 1 + Finsupp.single s 1) h else 0) = 0
          rw [tsub_add_cancel_of_le hle, hs0, if_neg]
          intro h'
          exact hs (Option.some_injective _ h').symm
        · rfl
      · simp
  rw [key]
  exact Ideal.sum_mem _ fun s _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s, rfl⟩)

private theorem mvPowerSeries_exists_polynomial_sub_mem_span_X_pow {σ R : Type} [Finite σ] [CommRing R] (n : ℕ) (g : MvPowerSeries σ R) :
    ∃ p : MvPolynomial σ R, g - (p : MvPowerSeries σ R) ∈
      (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R))) ^ n := by
  classical
  have := Fintype.ofFinite σ
  induction n generalizing g with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    have h1 : g - MvPowerSeries.C (MvPowerSeries.constantCoeff g) ∈
        Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) :=
      mvPowerSeries_mem_span_X_of_constantCoeff_zero _ (by simp)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPowerSeries σ R)).mp h1
    choose p hp using fun s => ih (c s)
    refine ⟨MvPolynomial.C (MvPowerSeries.constantCoeff g) + ∑ s, p s * MvPolynomial.X s, ?_⟩
    have hsum : ((∑ s, p s * MvPolynomial.X s : MvPolynomial σ R) : MvPowerSeries σ R) =
        ∑ s, (p s : MvPowerSeries σ R) * MvPowerSeries.X s := by
      rw [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
      simp [MvPolynomial.coeToMvPowerSeries.ringHom_apply]
    have e : g - ((MvPolynomial.C (MvPowerSeries.constantCoeff g) + ∑ s, p s * MvPolynomial.X s :
        MvPolynomial σ R) : MvPowerSeries σ R) =
        ∑ s, (c s - (p s : MvPowerSeries σ R)) * MvPowerSeries.X s := by
      rw [MvPolynomial.coe_add, hsum, MvPolynomial.coe_C, ← sub_sub, ← hc]
      simp [sub_mul, smul_eq_mul, Finset.sum_sub_distrib]
    rw [e, pow_succ]
    exact Ideal.sum_mem _ fun s _ => Ideal.mul_mem_mul (hp s) (Ideal.subset_span ⟨s, rfl⟩)

theorem UpperTheory.V.Alg.co_ev :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (σ : Type) [Finite σ] (f : R →ₐ[O] R') (a : σ → R'), (∀ s, a s ∈ maximalIdeal R') →
      ∃! F : MvPowerSeries σ R →ₐ[O] R', (∀ x, F (C x) = f x) ∧ ∀ s, F (X s) = a s := by
  intro O _ _ R _ _ _ R' _ _ _ σ _ f a ha
  classical
  letI : WithIdeal R' := ⟨maximalIdeal R'⟩
  have hcs : CompleteSpace R' ∧ T2Space R' :=
    (IsAdic.isAdicComplete_iff (R := R') (I := maximalIdeal R') rfl).mp (IsCO.complete (O := O))
  haveI := hcs.1
  haveI := hcs.2
  have hE : MvPowerSeries.HasEval a :=
    ⟨fun s => WithIdeal.isTopologicallyNilpotent_of_mem (ha s), by simp [Filter.cofinite_eq_bot]⟩
  let E : MvPowerSeries σ R →+* R' :=
    (MvPowerSeries.aeval hE).toRingHom.comp (MvPowerSeries.map f.toRingHom)
  have hEC : ∀ x, E (C x) = f x := by
    intro x
    simp [E, MvPowerSeries.coe_aeval, MvPowerSeries.eval₂_C, MvPowerSeries.map_C]
  have hEX : ∀ s, E (X s) = a s := by
    intro s
    simp [E, MvPowerSeries.coe_aeval, MvPowerSeries.eval₂_X, MvPowerSeries.map_X]
  let F : MvPowerSeries σ R →ₐ[O] R' :=
    { E with
      commutes' := fun r => by
        change E (algebraMap O (MvPowerSeries σ R) r) = _
        rw [MvPowerSeries.algebraMap_apply, hEC]
        simp }
  refine ⟨F, ⟨hEC, hEX⟩, ?_⟩
  rintro G ⟨hGC, hGX⟩
  have hpoly : ∀ (H : MvPowerSeries σ R →ₐ[O] R'), (∀ x, H (C x) = f x) → (∀ s, H (X s) = a s) →
      ∀ p : MvPolynomial σ R, H (p : MvPowerSeries σ R) = MvPolynomial.eval₂ f.toRingHom a p := by
    intro H hC hX p
    induction p using MvPolynomial.induction_on with
    | C c => simp [MvPolynomial.coe_C, hC]
    | add p q hp hq => simp [MvPolynomial.coe_add, hp, hq]
    | mul_X p s hp => simp [MvPolynomial.coe_mul, MvPolynomial.coe_X, hp, hX]
  have hJ : ∀ (H : MvPowerSeries σ R →ₐ[O] R'), (∀ s, H (X s) = a s) → ∀ n,
      ∀ y ∈ (Ideal.span (Set.range (X : σ → MvPowerSeries σ R))) ^ n, H y ∈ maximalIdeal R' ^ n := by
    intro H hX n y hy
    have h1 : Ideal.map H (Ideal.span (Set.range (X : σ → MvPowerSeries σ R))) ≤ maximalIdeal R' := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
      rw [hX]
      exact ha s
    have h2 := Ideal.mem_map_of_mem H hy
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono h1 n h2
  have hH : IsHausdorff (maximalIdeal R') R' := (IsCO.complete (O := O)).toIsHausdorff
  ext g
  rw [← sub_eq_zero]
  refine hH.haus _ fun n => ?_
  obtain ⟨p, hp⟩ := mvPowerSeries_exists_polynomial_sub_mem_span_X_pow n g
  have e1 : G g - F g = G (g - p) - F (g - p) := by
    rw [map_sub, map_sub, hpoly G hGC hGX, hpoly F (fun x => hEC x) (fun s => hEX s)]
    ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, e1]
  exact Ideal.sub_mem _ (hJ G hGX n _ hp) (hJ F (fun s => hEX s) n _ hp)
