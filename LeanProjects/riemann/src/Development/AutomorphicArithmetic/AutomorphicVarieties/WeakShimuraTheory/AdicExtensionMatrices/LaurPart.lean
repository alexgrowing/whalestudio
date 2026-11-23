import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem laurPart_prod {S R' ι : Type} [CommRing S] [CommRing R'] (e : S →+* LaurentSeries R')
    (w : ι → ℤ) (z : ι → S) (h : ∀ s, ∃ y, e (z s) = HahnSeries.single (w s) y) (d : ι → ℕ) (t : Finset ι) :
    ∃ y, e (∏ i ∈ t, z i ^ d i) = HahnSeries.single (∑ i ∈ t, d i • w i) y := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a t ha ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨u, hu⟩ := h a
    refine ⟨u ^ d a * y, ?_⟩
    rw [Finset.prod_insert ha, Finset.sum_insert ha, map_mul, map_pow, hy, hu, HahnSeries.single_pow,
      HahnSeries.single_mul_single]

theorem UpperTheory.V.Ws.sxLaurPart :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (W : WPres Λ X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ {R' : Type} [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {S : Type} [CommRing S] [Algebra Λ S] [IsCO Λ S] {c : ℕ} {e : S →+* LaurentSeries R'}, Laur Λ c e → ∀ (τ : X →+ ℤ) (F : R →ₐ[Λ] S), (∀ s, ∃ y, e (F (W.z s)) = HahnSeries.single (τ (W.wt s)) y) → ∀ j, ∀ x ∈ W.part j, ∃ y, e (F x) = HahnSeries.single (τ j) y := by
  intro Λ _ _ _ _ X _ _ _ _ R _ _ _ W hW R' _ _ _ S _ _ _ c e hL τ F hF j x hx
  classical
  obtain ⟨g, hg, rfl⟩ := hx
  have hm : ∀ s, (F.comp W.π) (MvPowerSeries.X s) ∈ maximalIdeal S := fun s => by
    show F (W.z s) ∈ maximalIdeal S
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
    exact hW s
  refine ⟨(e (F (W.π g))).coeff (τ j), ?_⟩
  ext n
  show (e (F (W.π g))).coeff n = _
  by_cases hn : n = τ j
  · subst hn
    rw [HahnSeries.coeff_single_same]
  rw [HahnSeries.coeff_single_of_ne hn]
  obtain ⟨M, hM⟩ := hL.small n
  have h1 := hM _ (GlobalTheory.algHom_sub_aeval_truncTotal_mem (F.comp W.π) hm M g)
  rw [map_sub, HahnSeries.coeff_sub, sub_eq_zero] at h1
  refine h1.trans ?_
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, map_sum, HahnSeries.coeff_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hw : Finsupp.weight W.wt d = j := by
    by_contra hne
    apply MvPolynomial.mem_support_iff.1 hd
    rw [MvPowerSeries.coeff_truncTotal_eq_ite, hg d hne, ite_self]
  obtain ⟨y, hy⟩ := laurPart_prod e (fun s => τ (W.wt s)) (fun s => F (W.z s)) hF d d.support
  have hs : (∑ i ∈ d.support, d i • τ (W.wt i)) = τ j := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum, map_sum]
    simp only [map_nsmul]
  rw [hs] at hy
  rw [map_mul, hL.alg]
  erw [hy]
  rw [HahnSeries.single_mul_single, zero_add, HahnSeries.coeff_single_of_ne hn]
