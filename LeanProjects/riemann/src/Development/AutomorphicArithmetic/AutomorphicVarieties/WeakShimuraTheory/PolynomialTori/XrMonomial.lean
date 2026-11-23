import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

section SlopeTestRemainingChoices

open MvPowerSeries

private theorem xr_ev {O S σ : Type} [CommRing O] [CommRing S] [Algebra O S] [Finite σ] (m : Ideal S)
    [IsAdicComplete m S] (a : σ → S) (ha : ∀ s, a s ∈ m) :
    ∃ F : MvPowerSeries σ O →ₐ[O] S, ∀ s, F (X s) = a s := by
  letI : UniformSpace O := ⊥
  haveI : DiscreteTopology O := ⟨rfl⟩
  letI : WithIdeal S := ⟨m⟩
  haveI : ContinuousSMul O S := continuousSMul_of_algebraMap O S continuous_of_discreteTopology
  have hadic : IsAdic m := rfl
  obtain ⟨_, _⟩ := (IsAdic.isAdicComplete_iff hadic).1 inferInstance
  have hE : MvPowerSeries.HasEval a := by
    refine ⟨fun s => ?_, ?_⟩
    · show Filter.Tendsto (fun n => a s ^ n) Filter.atTop (nhds 0)
      rw [hadic.hasBasis_nhds_zero.tendsto_right_iff]
      intro i _
      rw [Filter.eventually_atTop]
      exact ⟨i, fun n hn => Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow (ha s) n)⟩
    · simp
  refine ⟨MvPowerSeries.aeval hE, fun s => ?_⟩
  rw [← MvPolynomial.coe_X, MvPowerSeries.aeval_coe, MvPolynomial.aeval_X]

private theorem xr_monomial {O σ : Type} [CommRing O] [Fintype σ] (m : σ →₀ ℕ) :
    (monomial m (1 : O) : MvPowerSeries σ O) = ∏ i, (MvPowerSeries.X i) ^ (m i) := by
  classical
  rw [← MvPolynomial.coe_monomial, ← MvPolynomial.prod_X_pow_eq_monomial]
  have h := map_prod (MvPolynomial.coeToMvPowerSeries.ringHom (σ := σ) (R := O)) (fun x => MvPolynomial.X x ^ m x) m.support
  simp only [map_pow, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_X] at h
  rw [h]
  refine Finset.prod_subset (Finset.subset_univ _) ?_
  intro i _ hi
  rw [Finsupp.notMem_support_iff.1 hi, pow_zero]

private theorem mvPowerSeries_algHom_monomial_eq_prod_X_pow {O σ K : Type} [CommRing O] [Fintype σ] [CommRing K] [Algebra O K]
    (G : MvPowerSeries σ O →ₐ[O] K) (m : σ →₀ ℕ) :
    G (MvPowerSeries.monomial m 1) = ∏ s, G (MvPowerSeries.X s) ^ m s := by
  rw [xr_monomial, map_prod]
  simp only [map_pow]

private theorem prod_pow_mem_ideal_pow_of_mem_of_le_exponent {σ K : Type} [Fintype σ] [CommRing K] (I : Ideal K) (c : σ → K)
    (hc : ∀ s, c s ∈ I) (m : σ →₀ ℕ) (k : ℕ) (s0 : σ) (hs0 : k ≤ m s0) :
    ∏ s, c s ^ m s ∈ I ^ k := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ (fun s => c s ^ m s) (Finset.mem_univ s0)]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right hs0 (Ideal.pow_mem_pow (hc s0) _))

private theorem xr_agree {O R X K : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] [CommRing K] [Algebra O K] (I : Ideal K) [IsHausdorff I K]
    (W : WPres O X R) (F : MvPowerSeries W.σ O →ₐ[O] K) (η : W.A →ₐ[O] K)
    (hX : ∀ s, F (MvPowerSeries.X s) = η (W.zA s)) (hz : ∀ s, η (W.zA s) ∈ I) (j : X)
    (f : MvPowerSeries W.σ O) (hf : f ∈ wtPart O W.wt j) (x : W.A) (hx : (x : R) = W.π f) : F f = η x := by
  classical
  apply sub_eq_zero.1
  refine IsHausdorff.haus' (I := I) _ fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  let n' : W.σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => k)
  let T := Finset.Iic n'
  let p : MvPowerSeries W.σ O := ∑ m ∈ T, coeff m f • monomial m 1
  have hpc : ∀ m, coeff m p = if m ≤ n' then coeff m f else 0 := by
    intro m
    simp only [p, map_sum, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_monomial, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [T, Finset.mem_Iic]
  have hf' : ∀ n, Finsupp.weight W.wt n ≠ j → coeff n f = 0 := hf
  obtain ⟨μ, hμ, hμf⟩ :=
    part_span O R X W {m | Finsupp.weight W.wt m = j ∧ ¬ m ≤ n'} j (fun n hn => hn.1)
  obtain ⟨b, hb, hg⟩ := hμf (f - p) (by
    intro n hn
    rw [map_sub, hpc]
    split_ifs with h
    · exact sub_self _
    · rw [sub_zero]
      apply hf'
      intro hw
      exact hn ⟨hw, h⟩)
  have hG : ∀ (K' : Type) [CommRing K'] [Algebra O K'] (G : MvPowerSeries W.σ O →ₐ[O] K'),
      G p = ∑ m ∈ T, coeff m f • ∏ s, G (MvPowerSeries.X s) ^ m s := by
    intro K' _ _ G
    simp only [p, map_sum, map_smul, mvPowerSeries_algHom_monomial_eq_prod_X_pow]
  let y : W.A := ∑ m ∈ T, coeff m f • ∏ s, W.zA s ^ m s
  have hy : F p = η y := by
    rw [hG K F]
    simp only [y, map_sum, map_smul, map_prod, map_pow, hX]
  have hyR : (y : R) = W.π p := by
    rw [hG R W.π]
    show W.A.val y = _
    simp only [y, map_sum, map_smul, map_prod, map_pow]
    rfl
  let e : W.A := ∑ m ∈ μ, (⟨W.π (b m), W.part_le_A (j := 0) (Submodule.mem_map_of_mem (hb m))⟩ : W.A) *
    ∏ s, W.zA s ^ m s
  have he : x - y = e := by
    apply Subtype.ext
    show W.A.val (x - y) = W.A.val e
    rw [map_sub]
    show (x : R) - (y : R) = _
    rw [hx, hyR, ← map_sub, hg]
    simp only [e, map_sum, map_mul, map_prod, map_pow, mvPowerSeries_algHom_monomial_eq_prod_X_pow]
    rfl
  have hdiff : F f - η x = F (f - p) - η e := by
    rw [← he, map_sub, map_sub, hy]
    ring
  rw [hdiff, hg]
  simp only [e, map_sum, map_mul, mvPowerSeries_algHom_monomial_eq_prod_X_pow, hX, map_prod, map_pow]
  rw [← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun m hm => ?_
  rw [← sub_mul]
  refine Ideal.mul_mem_left _ _ ?_
  obtain ⟨-, hm2⟩ := hμ (Finset.mem_coe.2 hm)
  have hex : ∃ s0, k < m s0 := by
    by_contra hcon
    push_neg at hcon
    exact hm2 (Finsupp.le_def.2 fun s => by simpa [n'] using hcon s)
  obtain ⟨s0, hs0⟩ := hex
  exact prod_pow_mem_ideal_pow_of_mem_of_le_exponent I _ hz m k s0 hs0.le

private theorem xr_const {O S σ : Type} [CommRing O] [CommRing S] [Algebra O S] [Fintype σ] (I : Ideal S)
    (F : MvPowerSeries σ O →ₐ[O] S) (hF : ∀ s, F (X s) ∈ I) (f : MvPowerSeries σ O) :
    F f - algebraMap O S (constantCoeff f) ∈ I := by
  classical
  have key : ∀ T : Finset σ, ∀ g : MvPowerSeries σ O,
      (∀ n : σ →₀ ℕ, (∀ s ∈ T, n s = 0) → coeff n g = 0) → F g ∈ I := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · intro g hg
      have hg0 : g = 0 := by
        ext n
        exact hg n (by simp)
      rw [hg0, map_zero]
      exact I.zero_mem
    · intro s T _ ih g hg
      let r : MvPowerSeries σ O := fun n => if n s = 0 then coeff n g else 0
      have hr : ∀ n, coeff n r = if n s = 0 then coeff n g else 0 := fun n => rfl
      have hdvd : X s ∣ g - r := by
        rw [MvPowerSeries.X_dvd_iff]
        intro n hn
        rw [map_sub, hr, if_pos hn, sub_self]
      obtain ⟨q, hq⟩ := hdvd
      have hrI : F r ∈ I := by
        apply ih
        intro n hn
        rw [hr]
        split_ifs with h
        · apply hg
          intro t ht
          rcases Finset.mem_insert.1 ht with rfl | ht
          · exact h
          · exact hn t ht
        · rfl
      have hgq : g = X s * q + r := by rw [← hq, sub_add_cancel]
      rw [hgq, map_add, map_mul]
      exact I.add_mem (I.mul_mem_right _ (hF s)) hrI
  have h := key Finset.univ (f - algebraMap O (MvPowerSeries σ O) (constantCoeff f)) ?_
  · rwa [map_sub, F.commutes] at h
  · intro n hn
    have hn0 : n = 0 := Finsupp.ext fun s => hn s (Finset.mem_univ s)
    subst hn0
    rw [map_sub, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← MvPowerSeries.c_eq_algebraMap, MvPowerSeries.constantCoeff_C, sub_self]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.Po.extR :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (A' : Type) [CommRing A'] [IsLocalRing A'] [IsAdicComplete (maximalIdeal A') A'] [Algebra O A'] (η : W.A →ₐ[O] A'),
      (∀ s, η (W.zA s) ∈ maximalIdeal A') → (∀ b ∈ W.gr 0, (b : R) ∈ maximalIdeal R → η b ∈ maximalIdeal A') →
      ∃ Ξ : R →ₐ[O] A', Ξ.comp W.A.val = η ∧ ∀ x ∈ maximalIdeal R, Ξ x ∈ maximalIdeal A' := by
  intro O _ _ _ _ X _ _ _ _ R _ _ _ W hzm A' _ _ _ _ η hηz hη0
  classical
  obtain ⟨F, hF⟩ := xr_ev (O := O) (σ := W.σ) (maximalIdeal A') (fun s => η (W.zA s)) hηz
  obtain ⟨n, f, c, hfc, hker⟩ := ker_gen O X W.σ W.wt (RingHom.ker W.π) W.homog
  have hkill : ∀ a ∈ RingHom.ker W.π, F a = 0 := by
    intro a ha
    rw [hker] at ha
    have hle : Ideal.span (Set.range f) ≤ RingHom.ker F := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have hfi : f i ∈ RingHom.ker W.π := by
        rw [hker]
        exact Ideal.subset_span ⟨i, rfl⟩
      rw [RingHom.mem_ker] at hfi
      show F (f i) = 0
      have h := xr_agree (I := maximalIdeal A') W F η hF hηz (c i) (f i) (hfc i) 0 (by rw [hfi]; rfl)
      rw [h, map_zero]
    exact hle ha
  let e := Ideal.quotientKerAlgEquivOfSurjective W.surj
  let Ξ : R →ₐ[O] A' := (Ideal.Quotient.liftₐ (RingHom.ker W.π) F hkill).comp e.symm.toAlgHom
  have hΞ : ∀ g, Ξ (W.π g) = F g := by
    intro g
    have h1 : e.symm (W.π g) = Ideal.Quotient.mk _ g := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    show Ideal.Quotient.liftₐ _ F hkill (e.symm (W.π g)) = F g
    rw [h1]
    rfl
  have hF' : ∀ s, F (MvPowerSeries.X s) ∈ maximalIdeal A' := fun s => by
    rw [hF]
    exact hηz s
  refine ⟨Ξ, ?_, ?_⟩
  · apply AlgHom.ext
    intro a
    have key : ∀ y : R, y ∈ (⨆ j, W.part j) → y ∈ W.A ∧ ∀ h : y ∈ W.A, Ξ y = η ⟨y, h⟩ := by
      intro y hy
      refine Submodule.iSup_induction (motive := fun y => y ∈ W.A ∧ ∀ h : y ∈ W.A, Ξ y = η ⟨y, h⟩) _ hy
        ?_ ?_ ?_
      · intro i y hy
        refine ⟨W.part_le_A hy, fun h => ?_⟩
        obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.1 hy
        exact (hΞ g).trans (xr_agree (I := maximalIdeal A') W F η hF hηz i g hg _ rfl)
      · refine ⟨W.A.zero_mem, fun h => ?_⟩
        rw [map_zero]
        exact (map_zero η).symm
      · rintro y z ⟨hy1, hy2⟩ ⟨hz1, hz2⟩
        refine ⟨W.A.add_mem hy1 hz1, fun h => ?_⟩
        rw [map_add, hy2 hy1, hz2 hz1, ← map_add]
        rfl
    exact (key a a.2).2 a.2
  · intro x hx
    obtain ⟨g, rfl⟩ := W.surj x
    rw [hΞ]
    have h1 := xr_const (maximalIdeal R) W.π hzm g
    have h2 : algebraMap O R (MvPowerSeries.constantCoeff g) ∈ maximalIdeal R := by
      have h := Ideal.sub_mem _ hx h1
      rwa [sub_sub_cancel] at h
    have hb : (algebraMap O W.A (MvPowerSeries.constantCoeff g)) ∈ W.gr 0 := by
      show W.A.val (algebraMap O W.A (MvPowerSeries.constantCoeff g)) ∈ W.part 0
      rw [AlgHom.commutes]
      refine Submodule.mem_map.2 ⟨algebraMap O (MvPowerSeries W.σ O) (MvPowerSeries.constantCoeff g), ?_,
        W.π.commutes _⟩
      show ∀ k : W.σ →₀ ℕ, Finsupp.weight W.wt k ≠ 0 → MvPowerSeries.coeff k _ = 0
      intro k hk
      rw [← MvPowerSeries.c_eq_algebraMap, MvPowerSeries.coeff_C, if_neg]
      rintro rfl
      exact hk (map_zero _)
    have h3 := hη0 _ hb (by
      show W.A.val (algebraMap O W.A (MvPowerSeries.constantCoeff g)) ∈ maximalIdeal R
      rw [AlgHom.commutes]
      exact h2)
    rw [AlgHom.commutes] at h3
    have h4 := xr_const (maximalIdeal A') F hF' g
    have h5 := Ideal.add_mem _ h4 h3
    rwa [sub_add_cancel] at h5
