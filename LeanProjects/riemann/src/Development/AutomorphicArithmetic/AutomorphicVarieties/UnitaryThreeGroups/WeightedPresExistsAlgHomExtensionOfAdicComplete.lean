import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.MopBase
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesEvalOfPowMem

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

section SlopeTestRemainingChoices

open MvPowerSeries

private theorem pf_monomial {O σ S : Type} [CommRing O] [CommRing S] [Algebra O S]
    (f : MvPowerSeries σ O →ₐ[O] S) (m : σ →₀ ℕ) :
    f (monomial m 1) = m.prod fun s k => f (MvPowerSeries.X s) ^ k := by
  have h := GlobalTheory.algHom_coe_mvPolynomial f (MvPolynomial.monomial m (1 : O))
  rw [MvPolynomial.coe_monomial, MvPolynomial.aeval_monomial, RingHom.map_one, one_mul] at h
  exact h

private theorem pf_prod {X σ S : Type} [AddCommGroup X] [CommRing S] (wt : σ → X)
    (t : Multiplicative X →* Sˣ) (x : σ → S) (d : σ →₀ ℕ) :
    (d.prod fun i k => ((t (Multiplicative.ofAdd (wt i)) : S) * x i) ^ k) =
      (t (Multiplicative.ofAdd (Finsupp.weight wt d)) : S) * d.prod fun i k => x i ^ k := by
  simp only [mul_pow, Finsupp.prod_mul]
  congr 1
  rw [Finsupp.weight_apply, Finsupp.sum, ofAdd_sum, map_prod, Units.coe_prod, Finsupp.prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofAdd_nsmul, map_pow, Units.val_pow_eq_pow_val]

private theorem pf_approx {O X σ : Type} [CommRing O] [AddCommGroup X] [Finite σ] (wt : σ → X)
    (F : MvPowerSeries σ O) (n : ℕ) :
    ∃ s : Finset X, (n : ℕ∞) ≤ (F - ∑ j ∈ s, wcomp O wt j F).order := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Finset (σ →₀ ℕ), ∀ d, Finsupp.degree d < n → d ∈ T :=
    ⟨(Finsupp.finite_of_degree_lt (σ := σ) n).toFinset, fun d hd => by simpa using hd⟩
  refine ⟨T.image (Finsupp.weight wt), MvPowerSeries.le_order fun d hd => ?_⟩
  have hd' : Finsupp.degree d < n := by exact_mod_cast hd
  have hmem : Finsupp.weight wt d ∈ T.image (Finsupp.weight wt) :=
    Finset.mem_image_of_mem _ (hT d hd')
  rw [map_sub, map_sum]
  simp only [coeff_wcomp]
  rw [Finset.sum_ite_eq, if_pos hmem, sub_self]

private theorem pf_vanish {O X σ S : Type} [CommRing O] [AddCommGroup X] [Finite σ] [CommRing S]
    [Algebra O S] (wt : σ → X) (J : Ideal S) [IsHausdorff J S] (φ : MvPowerSeries σ O →ₐ[O] S)
    (hφ : ∀ i, φ (MvPowerSeries.X i) ∈ J) (F : MvPowerSeries σ O) (h : ∀ j, φ (wcomp O wt j F) = 0) :
    φ F = 0 := by
  refine GlobalTheory.eq_of_forall_sub_mem_ideal_pow J fun n => ?_
  obtain ⟨s, hs⟩ := pf_approx wt F n
  have h1 := GlobalTheory.algHom_mem_pow_of_le_order φ hφ hs
  have h2 : φ (∑ j ∈ s, wcomp O wt j F) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => h j
  rw [map_sub, h2, sub_zero] at h1
  rwa [sub_zero]

variable {O X R K : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R] (W : WPres O X R)
  [CommRing K] [Algebra O K] (ξ : W.A →ₐ[O] K)

private theorem pf_zprod (m : W.σ →₀ ℕ) :
    ((m.prod fun s k => W.zA s ^ k : W.A) : R) = W.π (monomial m 1) := by
  rw [pf_monomial]
  exact map_finsuppProd W.A.val _ _

variable [Module.Free ℤ X] [Module.Finite ℤ X] {B : Type} [CommRing B] [Algebra O B] (ι : B →ₐ[O] K)
  (t : Multiplicative X →* Kˣ) (g : MvPowerSeries W.σ O →ₐ[O] B)

private theorem pf_step (hg : ∀ s, ι (g (MvPowerSeries.X s)) = t (Multiplicative.ofAdd (W.wt s)) * ξ (W.zA s))
    (I J : Ideal B) (S : Set (W.σ →₀ ℕ)) (j : X) (hS : ∀ n ∈ S, Finsupp.weight W.wt n = j)
    (hJ : ∀ n ∈ S, g (monomial n 1) ∈ J)
    (hI : ∀ b, b ∈ wtPart O W.wt 0 → ∀ x : W.A, (x : R) = W.π b → ∃ c, ι c = ξ x ∧ g b - c ∈ I)
    (F : MvPowerSeries W.σ O) (hF : ∀ n, n ∉ S → coeff n F = 0) (x : W.A) (hx : (x : R) = W.π F) :
    ∃ c, ι c = t (Multiplicative.ofAdd j) * ξ x ∧ g F - c ∈ I * J := by
  classical
  obtain ⟨μ, hμS, hμ⟩ := part_span O R X W S j hS
  obtain ⟨b, hb, hFb⟩ := hμ F hF
  have hy : ∀ m, W.π (b m) ∈ W.A := fun m =>
    W.part_le_A (j := 0) (show W.π (b m) ∈ W.part 0 from Submodule.mem_map_of_mem (hb m))
  choose c hc hcI using fun m => hI (b m) (hb m) ⟨W.π (b m), hy m⟩ rfl
  refine ⟨∑ m ∈ μ, c m * g (monomial m 1), ?_, ?_⟩
  · have hx' : x = ∑ m ∈ μ, (⟨W.π (b m), hy m⟩ : W.A) * (m.prod fun s k => W.zA s ^ k) := by
      apply Subtype.ext
      rw [hx, hFb]
      show _ = W.A.val _
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, map_mul]
      show _ = W.π (b m) * ((m.prod fun s k => W.zA s ^ k : W.A) : R)
      rw [pf_zprod]
    have hgm : ∀ m ∈ μ, ι (g (monomial m 1)) =
        (t (Multiplicative.ofAdd j) : K) * ξ (m.prod fun s k => W.zA s ^ k) := by
      intro m hm
      have h1 := pf_monomial (ι.comp g) m
      simp only [AlgHom.comp_apply, hg] at h1
      rw [h1, pf_prod W.wt t (fun s => ξ (W.zA s)) m, hS m (hμS (Finset.mem_coe.mpr hm)),
        map_finsuppProd]
      simp only [map_pow]
    rw [hx', map_sum ι, map_sum ξ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [map_mul ι, map_mul ξ, hc m, hgm m hm]
    ring
  · rw [hFb, map_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun m hm => ?_
    rw [map_mul, ← sub_mul]
    exact Ideal.mul_mem_mul (hcI m) (hJ m (hμS (Finset.mem_coe.mpr hm)))

private theorem mono_lemma {O' σ' B' : Type} [CommRing O'] [CommRing B'] [Algebra O' B'] [Finite σ']
    (g' : MvPowerSeries σ' O' →ₐ[O'] B') (J : Ideal B') (hJ : ∀ s, g' (MvPowerSeries.X s) ∈ J)
    (m : σ' →₀ ℕ) (hm : m ≠ 0) : g' (monomial m 1) ∈ J := by
  classical
  have h := GlobalTheory.algHom_mem_pow_of_le_order g' hJ (n := 1) (g := monomial m 1) ?_
  · simpa using h
  refine MvPowerSeries.le_order fun d hd => ?_
  have hd' : Finsupp.degree d < 1 := by exact_mod_cast hd
  have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
  subst hd0
  rw [MvPowerSeries.coeff_monomial, if_neg (Ne.symm hm)]

private theorem exists_lift_sub_mem_pow_of_mem_wtPart_zero
    (hg : ∀ s, ι (g (MvPowerSeries.X s)) = t (Multiplicative.ofAdd (W.wt s)) * ξ (W.zA s))
    (J : Ideal B) (hJ : ∀ s, g (MvPowerSeries.X s) ∈ J)
    (h0 : ∀ x ∈ W.gr 0, ∃ c, ι c = ξ x) (n : ℕ) :
    ∀ b, b ∈ wtPart O W.wt 0 → ∀ x : W.A, (x : R) = W.π b → ∃ c, ι c = ξ x ∧ g b - c ∈ J ^ n := by
  classical
  induction n with
  | zero =>
    intro b hb x hx
    obtain ⟨c, hc⟩ := h0 x (show (x : R) ∈ W.part 0 from Submodule.mem_map.mpr ⟨b, hb, hx.symm⟩)
    exact ⟨c, hc, by simp⟩
  | succ n ih =>
    intro b hb x hx
    have hb' : ∀ m, Finsupp.weight W.wt m ≠ 0 → coeff m b = 0 := hb
    obtain ⟨b0, hb0⟩ : ∃ b0, b0 = MvPowerSeries.constantCoeff b := ⟨_, rfl⟩
    have hC : (MvPowerSeries.C b0 : MvPowerSeries W.σ O) = algebraMap O _ b0 := rfl
    obtain ⟨x', hxe⟩ : ∃ x' : W.A, x' = x - algebraMap O W.A b0 := ⟨_, rfl⟩
    have hx' : (x' : R) = W.π (b - MvPowerSeries.C b0) := by
      rw [hxe, map_sub, hC, AlgHom.commutes, ← hx]
      rfl
    have hF : ∀ m, m ∉ {m : W.σ →₀ ℕ | Finsupp.weight W.wt m = 0 ∧ m ≠ 0} →
        coeff m (b - MvPowerSeries.C b0) = 0 := by
      intro m hm
      rw [map_sub, MvPowerSeries.coeff_C]
      by_cases hw : Finsupp.weight W.wt m = 0
      · have hm0 : m = 0 := by
          by_contra h
          exact hm ⟨hw, h⟩
        subst hm0
        rw [if_pos rfl, hb0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, sub_self]
      · have hm0 : m ≠ 0 := by
          rintro rfl
          exact hw (map_zero _)
        rw [if_neg hm0, hb' m hw, sub_zero]
    obtain ⟨c', hc', hcm⟩ := pf_step W ξ ι t g hg (J ^ n) J
      {m : W.σ →₀ ℕ | Finsupp.weight W.wt m = 0 ∧ m ≠ 0} 0 (fun m hm => hm.1)
      (fun m hm => mono_lemma g J hJ m hm.2) ih _ hF x' hx'
    refine ⟨algebraMap O B b0 + c', ?_, ?_⟩
    · rw [map_add, AlgHom.commutes, hc', ofAdd_zero, map_one, Units.val_one, one_mul,
        ← AlgHom.commutes ξ b0, ← map_add, hxe]
      congr 1
      abel
    · have he : g b - (algebraMap O B b0 + c') = g (b - MvPowerSeries.C b0) - c' := by
        rw [map_sub, hC, AlgHom.commutes]
        ring
      rw [he, pow_succ]
      exact hcm

private theorem pf_agree (hι : Function.Injective ι)
    (hg : ∀ s, ι (g (MvPowerSeries.X s)) = t (Multiplicative.ofAdd (W.wt s)) * ξ (W.zA s))
    (J : Ideal B) [IsHausdorff J B] (hJ : ∀ s, g (MvPowerSeries.X s) ∈ J)
    (h0 : ∀ x ∈ W.gr 0, ∃ c, ι c = ξ x) (j : X) (F : MvPowerSeries W.σ O) (hF : F ∈ wtPart O W.wt j)
    (x : W.A) (hx : (x : R) = W.π F) : ι (g F) = t (Multiplicative.ofAdd j) * ξ x := by
  have hF' : ∀ m, Finsupp.weight W.wt m ≠ j → coeff m F = 0 := hF
  have key : ∀ n : ℕ, ∃ c, ι c = t (Multiplicative.ofAdd j) * ξ x ∧ g F - c ∈ J ^ n := by
    intro n
    by_cases hj : j = 0
    · subst hj
      obtain ⟨c, hc, hm⟩ := exists_lift_sub_mem_pow_of_mem_wtPart_zero W ξ ι t g hg J hJ h0 n F hF x hx
      exact ⟨c, by rw [hc, ofAdd_zero, map_one, Units.val_one, one_mul], hm⟩
    · obtain ⟨c, hc, hm⟩ := pf_step W ξ ι t g hg (J ^ n) J {m | Finsupp.weight W.wt m = j} j
        (fun m hm => hm)
        (fun m hm => mono_lemma g J hJ m (by
          rintro rfl
          exact hj (hm.symm.trans (map_zero _))))
        (exists_lift_sub_mem_pow_of_mem_wtPart_zero W ξ ι t g hg J hJ h0 n) F (fun m hm => hF' m hm) x hx
      exact ⟨c, hc, (Ideal.mul_le_left : J ^ n * J ≤ J ^ n) hm⟩
  obtain ⟨c0, hc0, -⟩ := key 0
  have hgF : g F = c0 := GlobalTheory.eq_of_forall_sub_mem_ideal_pow J fun n => by
    obtain ⟨c, hc, hm⟩ := key n
    have hcc : c = c0 := hι (hc.trans hc0.symm)
    rwa [hcc] at hm
  rw [hgF, hc0]

private theorem pf_factor [DecidableEq X] (hι : Function.Injective ι)
    (hg : ∀ s, ι (g (MvPowerSeries.X s)) = t (Multiplicative.ofAdd (W.wt s)) * ξ (W.zA s))
    (J : Ideal B) [IsHausdorff J B] (hJ : ∀ s, g (MvPowerSeries.X s) ∈ J)
    (h0 : ∀ x ∈ W.gr 0, ∃ c, ι c = ξ x) :
    ∃ f : R →ₐ[O] B, ∀ j, ∀ x ∈ W.gr j, ι (f x) = t (Multiplicative.ofAdd j) * ξ x := by
  have hker : ∀ F ∈ RingHom.ker W.π, g F = 0 := by
    intro F hF
    refine pf_vanish W.wt J g hJ F fun j => ?_
    have hmem : wcomp O W.wt j F ∈ RingHom.ker W.π := W.homog F hF j
    have h := pf_agree W ξ ι t g hι hg J hJ h0 j (wcomp O W.wt j F) (wcomp_mem O W.wt j F) 0
      (by
        show (0 : R) = _
        exact (RingHom.mem_ker.mp hmem).symm)
    rw [map_zero, mul_zero] at h
    exact hι (h.trans (map_zero ι).symm)
  refine ⟨(Ideal.Quotient.liftₐ (RingHom.ker W.π) g hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm.toAlgHom, fun j x hx => ?_⟩
  obtain ⟨F, hF, hFx⟩ := Submodule.mem_map.mp (show (x : R) ∈ W.part j from hx)
  have hmk : (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π F) =
      Ideal.Quotient.mk (RingHom.ker W.π) F := by
    rw [AlgEquiv.symm_apply_eq]
    rfl
  have hval : (Ideal.Quotient.liftₐ (RingHom.ker W.π) g hker).comp
      (Ideal.quotientKerAlgEquivOfSurjective W.surj).symm.toAlgHom (x : R) = g F := by
    rw [← hFx]
    show Ideal.Quotient.liftₐ (RingHom.ker W.π) g hker
      ((Ideal.quotientKerAlgEquivOfSurjective W.surj).symm (W.π F)) = g F
    rw [hmk]
    rfl
  rw [hval]
  exact pf_agree W ξ ι t g hι hg J hJ h0 j F hF x hFx.symm

end SlopeTestRemainingChoices

theorem UpperTheory.weightedPres_exists_algHom_extension_of_adicComplete :
    ∀ {O X R : Type} [CommRing O] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R)
          {B : Type} [CommRing B] [Algebra O B] (J : Ideal B) [IsAdicComplete J B] (τ : W.A →ₐ[O] B), (∀ s, τ (W.zA s) ∈ J) → ∃ f : R →ₐ[O] B, f.comp W.A.val = τ := by
  intro O X R _ _ _ _ _ _ _ W B _ _ J _ τ hτ
  let g := GlobalTheory.mvEvalAdic O J (fun s => τ (W.zA s)) hτ
  have hgX : ∀ s, g (MvPowerSeries.X s) = τ (W.zA s) := fun s => GlobalTheory.mvEvalAdic_X J _ hτ s
  obtain ⟨f, hf⟩ := pf_factor W τ (AlgHom.id O B) (1 : Multiplicative X →* Bˣ) g
    (fun a b h => h) (fun s => by simp [hgX]) J (fun s => by rw [hgX]; exact hτ s)
    (fun x _ => ⟨τ x, rfl⟩)
  refine ⟨f, AlgHom.ext fun a => ?_⟩
  have key : ∀ y ∈ ⨆ j, W.part j, y ∈ W.A ∧ ∀ h : y ∈ W.A, f y = τ ⟨y, h⟩ := by
    intro y hy
    refine Submodule.iSup_induction (fun j => W.part j)
      (motive := fun y => y ∈ W.A ∧ ∀ h : y ∈ W.A, f y = τ ⟨y, h⟩) hy ?_ ?_ ?_
    · intro j z hz
      exact ⟨W.part_le_A hz, fun h => by simpa using hf j ⟨z, h⟩ hz⟩
    · exact ⟨W.A.zero_mem, fun h => by rw [map_zero]; exact (map_zero τ).symm⟩
    · intro z w hz hw
      exact ⟨W.A.add_mem hz.1 hw.1, fun h => by rw [map_add, hz.2 hz.1, hw.2 hw.1, ← map_add]; rfl⟩
  exact (key a a.2).2 a.2
