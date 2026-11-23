import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.TactVanish
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.TchPoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem eigen_low {R S σ : Type} [CommRing R] [CommRing S] [Finite σ] (m : Ideal S)
    (F : MvPowerSeries σ R →+* S) (hF : ∀ s, F (X s) ∈ m) (n : ℕ) (g : MvPowerSeries σ R)
    (hg : ∀ d : σ →₀ ℕ, d.degree < n → coeff d g = 0) : F g ∈ m ^ n := by
  have hI : MvPolynomial.idealOfVars σ R ≤ m.comap (F.comp MvPolynomial.coeToMvPowerSeries.ringHom) := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    simpa using hF s
  have hIn : MvPolynomial.idealOfVars σ R ^ n ≤
      (m ^ n).comap (F.comp MvPolynomial.coeToMvPowerSeries.ringHom) :=
    (Ideal.pow_right_mono hI n).trans (Ideal.le_comap_pow _ n)
  let e := toAdicCompletionAlgEquiv σ R
  have key : ∀ y ∈ (MvPolynomial.idealOfVars σ R ^ n • ⊤ : Submodule (MvPolynomial σ R)
      (AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R))), F (e.symm y) ∈ m ^ n := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun p hp z _ => ?_) (fun a b ha hb => ?_)
    · rw [map_smul, Algebra.smul_def, map_mul]
      exact Ideal.mul_mem_right _ _ (hIn hp)
    · rw [map_add, map_add]; exact add_mem ha hb
  have h := key (e g) (by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (MvPolynomial.idealOfVars_fg σ R), LinearMap.mem_ker,
      AdicCompletion.eval_apply, toAdicCompletionAlgEquiv_apply, toAdicCompletion_apply_eq_mk_truncTotal]
    have : truncTotal n g = 0 := by
      ext x
      rw [coeff_truncTotal_eq_ite]
      split_ifs with hx
      · rw [hg x hx]; simp
      · simp
    rw [this]
    rfl)
  rwa [AlgEquiv.symm_apply_apply] at h

private theorem eigen_split {O σ X : Type} [CommRing O] [Finite σ] [AddCommGroup X] (wt : σ → X) (j : X)
    (n : ℕ) (g : MvPowerSeries σ O) : ∃ s : Finset X, j ∈ s ∧
      ∀ d : σ →₀ ℕ, d.degree < n → coeff d (g - ∑ i ∈ s, wcomp O wt i g) = 0 := by
  classical
  refine ⟨insert j ((truncTotal n g).support.image (Finsupp.weight wt)), Finset.mem_insert_self _ _,
    fun d hd => ?_⟩
  rw [map_sub, map_sum]
  simp only [coeff_wcomp]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · exact sub_self _
  · rw [sub_zero]
    by_contra hne
    refine h (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ?_))
    rwa [MvPolynomial.mem_support_iff, coeff_truncTotal _ hd]

theorem UpperTheory.V.Alg.eigen_mem :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (x : R) (j : X),
      (∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f f' : R →ₐ[O] R') (t : Multiplicative X →* R'ˣ), (∀ i, res O R' (t i) = 1) →
        (∀ s, f' (W.z s) = t (Multiplicative.ofAdd (W.wt s)) * f (W.z s)) → f' x = t (Multiplicative.ofAdd j) * f x) → x ∈ W.part j := by
  intro O _ _ _ _ X _ _ _ R _ _ hR W hz x j H
  classical
  obtain ⟨n, t0, ht1, hind⟩ := tchar O X
  haveI : IsCO O (MvPowerSeries (Fin n) R) := co_mvps O R (Fin n)
  let f : R →ₐ[O] MvPowerSeries (Fin n) R :=
    { (C : R →+* MvPowerSeries (Fin n) R) with commutes' := fun a => (MvPowerSeries.algebraMap_apply).symm }
  have hf : ∀ a, f a = C a := fun _ => rfl
  let t : Multiplicative X →* (MvPowerSeries (Fin n) R)ˣ :=
    (Units.map (MvPowerSeries.map (σ := Fin n) (algebraMap O R)).toMonoidHom).comp t0
  have ht : ∀ i, (t i : MvPowerSeries (Fin n) R) =
      MvPowerSeries.map (algebraMap O R) (t0 i : MvPowerSeries (Fin n) O) := fun _ => rfl
  have hres : ∀ i, res O (MvPowerSeries (Fin n) R) (t i) = 1 := fun i => by
    have h : (t i : MvPowerSeries (Fin n) R) - 1 ∈ maximalIdeal (MvPowerSeries (Fin n) R) := fun hu => by
      have h2 := isUnit_constantCoeff _ hu
      rw [map_sub, ht, constantCoeff_map, ht1, map_one, map_one, sub_self] at h2
      exact not_isUnit_zero h2
    have := (res_eq_zero_iff O _ _).2 h
    rwa [map_sub, map_one, sub_eq_zero] at this
  obtain ⟨f', hf', -⟩ := tact O X R W hz (MvPowerSeries (Fin n) R) f t
  have hx := H _ f f' t hres (fun s => hf' _ _ (W.z_mem s))
  obtain ⟨g, rfl⟩ := W.surj x
  suffices h : W.π (wcomp O W.wt j g) - W.π g = 0 by
    rw [sub_eq_zero] at h
    exact ⟨_, wcomp_mem O W.wt j g, h⟩
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  refine IsHausdorff.haus (I := maximalIdeal R) inferInstance _ fun N => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  obtain ⟨s, hjs, hs⟩ := eigen_split W.wt j N g
  have h1 := eigen_low ((maximalIdeal R).map (C : R →+* MvPowerSeries (Fin n) R))
    ((f'.comp W.π : MvPowerSeries W.σ O →ₐ[O] _) : MvPowerSeries W.σ O →+* _) (fun s => by
      show f' (W.z s) ∈ _
      rw [hf' _ _ (W.z_mem s)]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hz s))) N _ hs
  let q := Ideal.Quotient.mk (maximalIdeal R ^ N)
  have h2 : MvPowerSeries.map (σ := Fin n) q (f' (W.π (g - ∑ i ∈ s, wcomp O W.wt i g))) = 0 := by
    rw [← Ideal.map_pow] at h1
    refine (Ideal.map_le_iff_le_comap.2 (fun a ha => ?_) : _ ≤ RingHom.ker (MvPowerSeries.map (σ := Fin n) q)) h1
    rw [Ideal.mem_comap, RingHom.mem_ker, map_C, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
  have hq : ∀ i, MvPowerSeries.map (σ := Fin n) q (t i) =
      MvPowerSeries.map (algebraMap O (R ⧸ maximalIdeal R ^ N)) (t0 i : MvPowerSeries (Fin n) O) := fun i => by
    ext d
    rfl
  have h3 := hind (R ⧸ maximalIdeal R ^ N) s
    (fun i => q (W.π (wcomp O W.wt i g)) - if i = j then q (W.π g) else 0) (by
      rw [map_sub, map_sub, hx, map_sum, map_sum, Finset.sum_congr rfl
        (fun i _ => hf' i (W.π (wcomp O W.wt i g)) ⟨_, wcomp_mem O W.wt i g, rfl⟩), map_sub, map_sum] at h2
      simp only [map_mul, hq, hf, map_C] at h2
      simp only [map_sub, mul_sub, Finset.sum_sub_distrib, apply_ite C, map_zero, mul_ite, mul_zero,
        Finset.sum_ite_eq', if_pos hjs]
      rw [← neg_eq_zero, neg_sub]
      exact h2) j hjs
  simp only [if_true] at h3
  rwa [← map_sub, Ideal.Quotient.eq_zero_iff_mem] at h3
