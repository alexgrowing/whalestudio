import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem tact_prod {X σ S : Type} [AddCommGroup X] [CommRing S] (wt : σ → X)
    (t : Multiplicative X →* Sˣ) (x : σ → S) (d : σ →₀ ℕ) :
    (d.prod fun i k => ((t (Multiplicative.ofAdd (wt i)) : S) * x i) ^ k) =
      (t (Multiplicative.ofAdd (Finsupp.weight wt d)) : S) * d.prod fun i k => x i ^ k := by
  simp_rw [mul_pow]
  rw [Finsupp.prod_mul]
  congr 1
  rw [Finsupp.weight_apply, Finsupp.sum, ofAdd_sum, map_prod, Units.coe_prod, Finsupp.prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofAdd_nsmul, map_pow, Units.val_pow_eq_pow_val]

private theorem tact_aeval {O X σ S : Type} [CommRing O] [AddCommGroup X] [CommRing S] [Algebra O S]
    (wt : σ → X) (t : Multiplicative X →* Sˣ) (x : σ → S) (j : X) (p : MvPolynomial σ O)
    (hp : ∀ d, Finsupp.weight wt d ≠ j → MvPolynomial.coeff d p = 0) :
    MvPolynomial.aeval (fun i => (t (Multiplicative.ofAdd (wt i)) : S) * x i) p =
      (t (Multiplicative.ofAdd j) : S) * MvPolynomial.aeval x p := by
  rw [p.as_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' : Finsupp.weight wt d = j := by
    by_contra h
    exact MvPolynomial.mem_support_iff.1 hd (hp d h)
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, tact_prod, hd']
  ring

private theorem tact_approx {O X σ : Type} [CommRing O] [AddCommGroup X] [Finite σ] (wt : σ → X)
    (F : MvPowerSeries σ O) (n : ℕ) :
    ∃ s : Finset X, (n : ℕ∞) ≤ (F - ∑ j ∈ s, wcomp O wt j F).order := by
  classical
  refine ⟨(truncTotal n F).support.image (Finsupp.weight wt), nat_le_order fun d hd => ?_⟩
  rw [map_sub, map_sum]
  simp only [coeff_wcomp]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · exact sub_self _
  · rw [sub_zero]
    by_contra h0
    refine h (Finset.mem_image_of_mem _ (MvPolynomial.mem_support_iff.2 ?_))
    rwa [coeff_truncTotal _ hd]

private theorem tact_vanish {O X σ S : Type} [CommRing O] [AddCommGroup X] [Finite σ] [CommRing S]
    [Algebra O S] (wt : σ → X) (J : Ideal S) [IsHausdorff J S] (φ : MvPowerSeries σ O →ₐ[O] S)
    (hφ : ∀ i, φ (MvPowerSeries.X i) ∈ J) (F : MvPowerSeries σ O) (h : ∀ j, φ (wcomp O wt j F) = 0) :
    φ F = 0 := by
  apply GlobalTheory.eq_of_forall_sub_mem_ideal_pow J
  intro n
  obtain ⟨s, hs⟩ := tact_approx wt F n
  have hm := GlobalTheory.algHom_mem_pow_of_le_order φ hφ hs
  rw [map_sub, map_sum] at hm
  simpa [h] using hm

theorem UpperTheory.V.Alg.tact :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Type) [AddCommGroup X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (t : Multiplicative X →* R'ˣ),
      ∃! f' : R →ₐ[O] R', ∀ j, ∀ x ∈ W.part j, f' x = t (Multiplicative.ofAdd j) * f x := by
  intro O _ _ X _ R _ _ _ W hz R' _ _ _ f t
  classical
  haveI : Fintype W.σ := W.fin
  haveI : IsAdicComplete (maximalIdeal R') R' := IsCO.complete (O := O)
  have hf_max : ∀ x ∈ maximalIdeal R, f x ∈ maximalIdeal R' := by
    intro x hx
    rw [← res_eq_zero_iff O R' (f x), res_map f x, res_eq_zero_iff O R x]
    exact hx
  let xs : W.σ → R' := fun i =>
    (t (Multiplicative.ofAdd (W.wt i)) : R') * f (W.π (MvPowerSeries.X i))
  have hxs : ∀ i, xs i ∈ maximalIdeal R' := fun i => Ideal.mul_mem_left _ _ (hf_max _ (hz i))
  obtain ⟨Ψ, hΨX, hΨtr⟩ : ∃ Ψ : MvPowerSeries W.σ O →ₐ[O] R', (∀ i, Ψ (MvPowerSeries.X i) = xs i) ∧
      ∀ (n : ℕ) (G : MvPowerSeries W.σ O),
        Ψ G - MvPolynomial.aeval xs (truncTotal n G) ∈ maximalIdeal R' ^ n :=
    ⟨_, GlobalTheory.mvEvalAdic_X _ xs hxs, GlobalTheory.mvEvalAdic_sub_aeval_truncTotal_mem _ xs hxs⟩
  have key : ∀ j, ∀ G ∈ wtPart O W.wt j,
      Ψ G = (t (Multiplicative.ofAdd j) : R') * f (W.π G) := by
    intro j G hG
    apply GlobalTheory.eq_of_forall_sub_mem_ideal_pow (maximalIdeal R')
    intro n
    have h1 := hΨtr n G
    have h2 := GlobalTheory.algHom_sub_aeval_truncTotal_mem (f.comp W.π) (J := maximalIdeal R')
      (fun i => hf_max _ (hz i)) n G
    simp only [AlgHom.coe_comp, Function.comp_apply] at h2
    have h3 : MvPolynomial.aeval xs (truncTotal n G) =
        (t (Multiplicative.ofAdd j) : R') *
          MvPolynomial.aeval (fun i => f (W.π (MvPowerSeries.X i))) (truncTotal n G) := by
      refine tact_aeval W.wt t (fun i => f (W.π (MvPowerSeries.X i))) j _ fun d hd => ?_
      rw [coeff_truncTotal_eq_ite]
      split_ifs
      · exact hG d hd
      · rfl
    have he : Ψ G - (t (Multiplicative.ofAdd j) : R') * f (W.π G) =
        (Ψ G - MvPolynomial.aeval xs (truncTotal n G)) -
          (t (Multiplicative.ofAdd j) : R') *
            (f (W.π G) - MvPolynomial.aeval (fun i => f (W.π (MvPowerSeries.X i))) (truncTotal n G)) := by
      rw [h3]
      ring
    rw [he]
    exact Ideal.sub_mem _ h1 (Ideal.mul_mem_left _ _ h2)
  have hker : ∀ F ∈ RingHom.ker W.π, Ψ F = 0 := by
    intro F hF
    refine tact_vanish W.wt (maximalIdeal R') Ψ (fun i => by rw [hΨX]; exact hxs i) F fun j => ?_
    rw [key j _ (wcomp_mem O W.wt j F)]
    have h0 : W.π (wcomp O W.wt j F) = 0 := RingHom.mem_ker.mp (W.homog F hF j)
    rw [h0, map_zero, mul_zero]
  let f' : R →ₐ[O] R' := (Ideal.Quotient.liftₐ (RingHom.ker W.π) Ψ hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm.toAlgHom
  have hf'π : ∀ G, f' (W.π G) = Ψ G := by
    intro G
    have hs : (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π G) =
        Ideal.Quotient.mk (RingHom.ker W.π) G := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    show Ideal.Quotient.liftₐ (RingHom.ker W.π) Ψ hker
      ((Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π G)) = Ψ G
    rw [hs]
    rfl
  refine ⟨f', ?_, ?_⟩
  · intro j x hx
    obtain ⟨G, hG, rfl⟩ := Submodule.mem_map.mp hx
    simp only [AlgHom.toLinearMap_apply]
    rw [hf'π, key j G hG]
  · intro g hg
    have hgz : ∀ i, g (W.π (MvPowerSeries.X i)) = xs i := fun i => hg (W.wt i) (W.z i) (W.z_mem i)
    have hcomp : g.comp W.π = Ψ := by
      apply GlobalTheory.mvPowerSeries_algHom_ext_of_isHausdorff (maximalIdeal R')
      · intro i
        rw [AlgHom.comp_apply, hgz]
        exact hxs i
      · intro i
        rw [AlgHom.comp_apply, hgz, hΨX]
    ext x
    obtain ⟨G, rfl⟩ := W.surj x
    rw [hf'π, ← AlgHom.comp_apply, hcomp]
