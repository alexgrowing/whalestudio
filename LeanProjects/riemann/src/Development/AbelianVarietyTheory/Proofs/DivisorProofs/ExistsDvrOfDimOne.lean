import Mathlib

open IsLocalRing

namespace GlobalTheory.CompleteDiscreteValuationRing

theorem fg_of_mem {A B : Type} [CommRing A] [IsNoetherianRing A] [CommRing B] [IsDomain B]
    [Algebra A B] (a : A) (ha : algebraMap A B a ≠ 0)
    (hart : IsArtinian A (A ⧸ Ideal.span {a}))
    (hden : ∀ x : B, ∃ (n : ℕ) (r : A), algebraMap A B a ^ n * x = algebraMap A B r)
    (J : Ideal B) (hJ : algebraMap A B a ∈ J) : J.FG := by
  set α := algebraMap A B a with hα
  let D : ℕ → Ideal A := fun n => (Ideal.span {α ^ n}).comap (algebraMap A B)
  have hD : ∀ {m n : ℕ}, m ≤ n → D n ≤ D m := fun h =>
    Ideal.comap_mono (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ h))
  let E : ℕ →o (Submodule A (A ⧸ Ideal.span {a}))ᵒᵈ :=
    ⟨fun n => OrderDual.toDual (Submodule.map (Ideal.span {a}).mkQ (D n)),
      fun m n h => Submodule.map_mono (hD h)⟩
  obtain ⟨l, hl⟩ := IsArtinian.monotone_stabilizes E
  have key : ∀ n, l ≤ n → ∀ r : A, α ^ n ∣ algebraMap A B r →
      ∃ (b : B) (s : A), algebraMap A B r = α ^ (n + 1) * b + α * algebraMap A B s := by
    intro n hn r hr
    have h1 : Submodule.map (Ideal.span {a}).mkQ (D n) =
        Submodule.map (Ideal.span {a}).mkQ (D (n + 1)) :=
      (hl n hn).symm.trans (hl (n + 1) (by omega))
    have h2 : (Ideal.span {a}).mkQ r ∈ Submodule.map (Ideal.span {a}).mkQ (D n) :=
      Submodule.mem_map_of_mem (Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 hr))
    rw [h1] at h2
    obtain ⟨r', hr', e⟩ := h2
    have h3 : r - r' ∈ Ideal.span {a} := (Submodule.Quotient.eq _).1 e.symm
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.1 h3
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 (Ideal.mem_comap.1 hr')
    refine ⟨b, s, ?_⟩
    rw [← hb, hα, ← map_mul, ← hs, ← map_add]
    congr 1; ring
  have down : ∀ (x : B) (j : ℕ),
      (∃ (b : B) (r : A), α ^ (l + j) * x = α ^ (l + j + 1) * b + algebraMap A B r) →
      ∃ (b : B) (r : A), α ^ l * x = α ^ (l + 1) * b + algebraMap A B r := by
    intro x j
    induction j with
    | zero => exact id
    | succ j ih =>
      rintro ⟨b, r, h⟩
      apply ih
      obtain ⟨b', s, hs⟩ := key (l + (j + 1)) (by omega) r
        ⟨x - α * b, by rw [mul_sub, h]; ring⟩
      refine ⟨b + b', s, mul_left_cancel₀ ha ?_⟩
      rw [hs] at h
      linear_combination h
  have claim : ∀ x : B, ∃ (b : B) (r : A), α ^ l * x = α ^ (l + 1) * b + algebraMap A B r := by
    intro x
    obtain ⟨n, r, h⟩ := hden x
    refine down x n ⟨0, a ^ l * r, ?_⟩
    rw [map_mul, map_pow, ← hα, ← h]; ring
  let Q : Ideal B := Ideal.span {α ^ (l + 1)}
  let φ : B →ₗ[B] B ⧸ Q := Q.mkQ ∘ₗ LinearMap.mul B B (α ^ l)
  refine Submodule.fg_of_fg_map_of_fg_inf_ker φ ?_ ?_
  · apply Submodule.FG.of_restrictScalars A
    refine Submodule.FG.of_le (Submodule.fg_span_singleton (R := A) (1 : B ⧸ Q)) ?_
    rintro _ ⟨x, -, rfl⟩
    obtain ⟨b, r, h⟩ := claim x
    refine Submodule.mem_span_singleton.2 ⟨r, ?_⟩
    have : φ x = Ideal.Quotient.mk Q (α ^ l * x) := rfl
    rw [this, h, map_add, Ideal.Quotient.eq_zero_iff_mem.2
      (Ideal.mem_span_singleton.2 (dvd_mul_right _ _)), zero_add, Algebra.smul_def, mul_one]
    rfl
  · have : (J : Submodule B B) ⊓ LinearMap.ker φ = Ideal.span {α} := by
      apply le_antisymm
      · rintro x ⟨-, hx⟩
        have h1 : Ideal.Quotient.mk Q (α ^ l * x) = 0 := hx
        have h2 := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h1)
        rw [pow_succ] at h2
        exact Ideal.mem_span_singleton.2 ((mul_dvd_mul_iff_left (pow_ne_zero l ha)).1 h2)
      · rw [Ideal.span_singleton_le_iff_mem]
        refine ⟨hJ, ?_⟩
        change Ideal.Quotient.mk Q (α ^ l * α) = 0
        rw [← pow_succ]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    rw [this]
    exact Submodule.fg_span_singleton _

theorem exists_dvr_of_dim_one (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O]
    [IsNoetherianRing O] [Ring.KrullDimLE 1 O] (t : O) (ht0 : t ≠ 0) (ht : ¬ IsUnit t) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (f : O →+* W), Function.Injective f ∧ ¬ IsUnit (f t) := by
  let K := FractionRing O
  obtain ⟨B, hB, hloc⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap O K)
  let f : O →+* B := (algebraMap O K).codRestrict B.toSubring hB
  have hf : ∀ x, ((f x : B) : K) = algebraMap O K x := fun _ => rfl
  have finj : Function.Injective f := fun x y h =>
    IsFractionRing.injective O K (by rw [← hf, ← hf, h])
  have hft : ¬ IsUnit (f t) := fun h => ht (hloc.1 _ h)
  have hpow : ∀ s : O, s ≠ 0 → ∃ n : ℕ, s ∣ t ^ n := by
    intro s hs
    have : t ∈ (Ideal.span {s}).radical := by
      rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
      rintro P ⟨hP, hP'⟩
      have hne : P ≠ ⊥ := by
        rintro rfl
        exact hs (by simpa using hP)
      have hmax : Ideal.IsMaximal P :=
        Ring.krullDimLE_one_iff_of_noZeroDivisors.1 inferInstance P hne hP'
      rw [IsLocalRing.eq_maximalIdeal hmax]
      exact ht
    obtain ⟨n, hn⟩ := this
    exact ⟨n, Ideal.mem_span_singleton.1 hn⟩
  have hfrac : ∀ x : B, ∃ r s : O, s ≠ 0 ∧ f s * x = f r := by
    intro x
    obtain ⟨r, s, hs, e⟩ := IsFractionRing.div_surjective (A := O) (x : K)
    have hs0 := nonZeroDivisors.ne_zero hs
    refine ⟨r, s, hs0, Subtype.ext ?_⟩
    have : algebraMap O K s ≠ 0 := fun h => hs0 (IsFractionRing.injective O K (by simpa using h))
    change algebraMap O K s * (x : K) = algebraMap O K r
    rw [← e]; exact mul_div_cancel₀ _ this
  letI : Algebra O B := f.toAlgebra
  have hN : IsNoetherianRing B := by
    rw [isNoetherianRing_iff_ideal_fg]
    intro J
    by_cases hJ : J = ⊥
    · rw [hJ]; exact Submodule.fg_bot
    obtain ⟨x, hxJ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
    obtain ⟨r, s, hs, e⟩ := hfrac x
    have hr : r ≠ 0 := by
      rintro rfl
      rw [map_zero] at e
      exact mul_ne_zero ((map_ne_zero_iff f finj).2 hs) hx0 e
    obtain ⟨n, c, hc⟩ := hpow r hr
    have hne : t ^ (n + 1) ≠ 0 := pow_ne_zero _ ht0
    refine fg_of_mem (t ^ (n + 1)) ((map_ne_zero_iff f finj).2 hne) ?_ ?_ J ?_
    · exact (isFiniteLength_iff_isNoetherian_isArtinian.1
        (isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hne))).2
    · intro y
      obtain ⟨r', s', hs', e'⟩ := hfrac y
      obtain ⟨m, c', hc'⟩ := hpow s' hs'
      refine ⟨m, r' * c' * t ^ (n * m), ?_⟩
      change f _ ^ m * y = f _
      rw [map_mul, map_mul, ← e', ← map_pow, ← pow_mul, add_mul, one_mul, pow_add, hc',
        map_mul, map_mul]
      ring
    · change f _ ∈ J
      rw [pow_succ, hc, map_mul, map_mul, ← e]
      exact J.mul_mem_right _ (J.mul_mem_right _ (J.mul_mem_left _ hxJ))
  have hP : IsPrincipalIdealRing B := IsPrincipalIdealRing.of_isNoetherianRing_of_isBezout
  have hD : IsDiscreteValuationRing B :=
    { not_a_field' := fun h => by
        have h1 : f t ∈ maximalIdeal B := hft
        rw [h] at h1
        exact ht0 ((map_eq_zero_iff f finj).1 h1) }
  exact ⟨B, inferInstance, inferInstance, hD, f, finj, hft⟩

theorem dvr_of_principal (S : Type) [CommRing S] [IsLocalRing S] (p : S)
    (hp : maximalIdeal S = Ideal.span {p}) (hreg : p ∈ nonZeroDivisors S)
    [IsHausdorff (maximalIdeal S) S] :
    ∃ _ : IsDomain S, IsDiscreteValuationRing S := by
  classical
  have hfac : ∀ x : S, x ≠ 0 → ∃ (n : ℕ) (u : S), IsUnit u ∧ x = p ^ n * u := by
    intro x hx
    have hex : ∃ n : ℕ, ¬ p ^ n ∣ x := by
      by_contra h
      push Not at h
      apply hx
      refine IsHausdorff.haus (I := maximalIdeal S) inferInstance x fun n => ?_
      rw [SModEq.zero, hp, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
      exact Ideal.mem_span_singleton.2 (h n)
    have h1 := Nat.find_spec hex
    have h0 : Nat.find hex ≠ 0 := fun h => by rw [h] at h1; simp at h1
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have h2 := Nat.find_min hex (m := n) (by omega)
    push Not at h2
    obtain ⟨u, hu⟩ := h2
    refine ⟨n, u, ?_, hu⟩
    by_contra hnu
    have : u ∈ maximalIdeal S := hnu
    rw [hp, Ideal.mem_span_singleton] at this
    apply h1
    rw [hn, hu, pow_succ]
    exact mul_dvd_mul_left _ this
  have hreg' : ∀ x : S, x ≠ 0 → x ∈ nonZeroDivisors S := by
    intro x hx
    obtain ⟨n, u, hu, rfl⟩ := hfac x hx
    exact mul_mem (pow_mem hreg n) hu.mem_nonZeroDivisors
  have hnz : NoZeroDivisors S := ⟨fun {x y} h => by
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr ((hreg' x hx).1 y h)⟩
  have hdom : IsDomain S := NoZeroDivisors.to_isDomain S
  have hp0 : p ≠ 0 := nonZeroDivisors.ne_zero hreg
  have hprime : Prime p := by
    rw [← Ideal.span_singleton_prime hp0, ← hp]
    infer_instance
  refine ⟨hdom, IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨p, hprime.irreducible, fun {x} hx => ?_⟩⟩
  obtain ⟨n, u, hu, rfl⟩ := hfac x hx
  exact ⟨n, hu.unit, rfl⟩

theorem exists_complete (B : Type) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (f : B →+* W), IsAdicComplete (maximalIdeal W) W ∧ Function.Injective f ∧ IsLocalHom f := by
  let W := AdicCompletion (maximalIdeal B) B
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible B
  have h1 : maximalIdeal W = Ideal.span {algebraMap B W p} := by
    have h0 : Ideal.map (algebraMap B W) (maximalIdeal B) = Ideal.span {algebraMap B W p} := by
      generalize algebraMap B W = g
      exact (congrArg (Ideal.map g) hp.maximalIdeal_eq).trans
        (by rw [Ideal.map_span, Set.image_singleton])
    exact AdicCompletion.maximalIdeal_eq_map.trans h0
  have hr : ∀ x : B, x ≠ 0 → algebraMap B W x ∈ nonZeroDivisors W := by
    intro x hx
    have h2 : IsSMulRegular W x :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hx)
    rw [mem_nonZeroDivisors_iff_left]
    intro y hy
    apply h2
    simp only [smul_zero]
    rw [Algebra.smul_def, hy]
  obtain ⟨hd, hD⟩ := dvr_of_principal W _ h1 (hr p hp.ne_zero)
  refine ⟨W, inferInstance, hd, hD, algebraMap B W, inferInstance, ?_, inferInstance⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h
  exact nonZeroDivisors.ne_zero (hr x h) hx

theorem exists_complete_dvr (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (t : A) (ht0 : t ≠ 0) (ht : ¬ IsUnit t) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (f : A →+* W), IsAdicComplete (maximalIdeal W) W ∧ Function.Injective f ∧
        ¬ IsUnit (f t) := by
  have hne : Ideal.span {t} ≠ ⊤ := fun h => ht (Ideal.span_singleton_eq_top.1 h)
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes hne
  have hPp : P.IsPrime := hP.1.1
  have htP : t ∈ P := hP.1.2 (Ideal.mem_span_singleton_self t)
  have hh : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP
  let O := Localization.AtPrime P
  have hdim : Ring.KrullDimLE 1 O := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height P O]
    exact_mod_cast hh
  have hinj : Function.Injective (algebraMap A O) :=
    IsLocalization.injective O P.primeCompl_le_nonZeroDivisors
  have hnu : ¬ IsUnit (algebraMap A O t) := fun h =>
    (IsLocalization.AtPrime.isUnit_to_map_iff O P t).1 h htP
  obtain ⟨B, _, _, _, f, hf, hft⟩ := exists_dvr_of_dim_one O (algebraMap A O t)
    ((map_ne_zero_iff _ hinj).2 ht0) hnu
  obtain ⟨W, _, _, hW, g, hc, hg, hl⟩ := exists_complete B
  exact ⟨W, inferInstance, inferInstance, hW, g.comp (f.comp (algebraMap A O)), hc,
    hg.comp (hf.comp hinj), fun h => hft (hl.1 _ h)⟩

theorem exists_chart (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V)
    (hϖ : Irreducible ϖ) (ψ : R →+* V) (hψ : IsLocalHom ψ) (I : Type) [Finite I] (a : I → R)
    (k : I → ℕ) (h : ∀ i, Associated (ψ (a i)) (ϖ ^ k i)) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsNoetherianRing A) (g : R →+* A) (t : A),
      Function.Injective g ∧ t ≠ 0 ∧ ¬ IsUnit t ∧ (∀ r ∈ maximalIdeal R, t ∣ g r) ∧
      ∀ i, Associated (g (a i)) (t ^ k i) := by
  classical
  have := Fintype.ofFinite I
  let K := FractionRing V
  let ι : V →+* K := algebraMap V K
  have hι : Function.Injective ι := IsFractionRing.injective V K
  have hψa : ∀ i, ψ (a i) ≠ 0 := fun i => (h i).ne_zero_iff.2 (pow_ne_zero _ hϖ.ne_zero)
  have ha : ∀ i, a i ≠ 0 := fun i e => hψa i (by rw [e, map_zero])
  let d : Polynomial R := Polynomial.X * Polynomial.C (∏ i, a i)
  have hd : d ≠ 0 := mul_ne_zero Polynomial.X_ne_zero
    (Polynomial.C_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => ha i))
  have hle : Submonoid.powers d ≤ nonZeroDivisors (Polynomial R) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hd
  let C := Localization.Away d
  have hCd : IsDomain C := IsLocalization.isDomain_localization hle
  have hinj : Function.Injective (algebraMap (Polynomial R) C) := IsLocalization.injective C hle
  let e : Polynomial R →+* K := Polynomial.eval₂RingHom (ι.comp ψ) (ι ϖ)
  have hϖK : ι ϖ ≠ 0 := (map_ne_zero_iff ι hι).2 hϖ.ne_zero
  have hed : IsUnit (e d) := by
    refine Ne.isUnit ?_
    simp only [e, d, map_mul, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, Polynomial.eval₂_C,
      RingHom.comp_apply]
    refine mul_ne_zero hϖK ((map_ne_zero_iff ι hι).2 ?_)
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hψa i
  let φ : C →+* K := IsLocalization.Away.lift d hed
  let τ : C := algebraMap (Polynomial R) C Polynomial.X
  have hRC : ∀ r : R, algebraMap R C r = algebraMap (Polynomial R) C (Polynomial.C r) :=
    fun r => by rw [IsScalarTower.algebraMap_apply R (Polynomial R) C]; rfl
  have hφτ : φ τ = ι ϖ := by
    simp only [φ, τ, IsLocalization.Away.lift_eq, e, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X]
  have hφr : ∀ r : R, φ (algebraMap R C r) = ι (ψ r) := fun r => by
    simp only [hRC, φ, IsLocalization.Away.lift_eq, e, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_C, RingHom.comp_apply]
  have hud : IsUnit (algebraMap (Polynomial R) C d) := IsLocalization.Away.algebraMap_isUnit d
  have huτ : IsUnit τ := isUnit_of_dvd_unit (map_dvd _ (dvd_mul_right _ _)) hud
  have hua : ∀ i, IsUnit (algebraMap R C (a i)) := fun i => by
    rw [hRC]
    refine isUnit_of_dvd_unit (map_dvd _ (Dvd.dvd.mul_left (map_dvd _ ?_) _)) hud
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

  have hdiv : ∀ (x y : C) (x' y' : V), IsUnit y → φ x = ι x' → φ y = ι y' → y' ∣ x' →
      ∃ z : C, x = y * z ∧ φ z ∈ ι.range := by
    rintro x y _ y' hy hx' hy' ⟨c, rfl⟩
    obtain ⟨z, rfl⟩ := hy.dvd (a := x)
    refine ⟨z, rfl, c, mul_left_cancel₀ (hy.map φ).ne_zero ?_⟩
    rw [← map_mul, hx', hy', map_mul]
  have hτk : ∀ i, φ (τ ^ k i) = ι (ϖ ^ k i) := fun i => by rw [map_pow, map_pow, hφτ]
  choose u hu hu' using fun i => hdiv (algebraMap R C (a i)) (τ ^ k i) _ _ (huτ.pow _) (hφr _)
    (hτk i) (h i).symm.dvd
  choose w hw hw' using fun i => hdiv (τ ^ k i) (algebraMap R C (a i)) _ _ (hua i) (hτk i)
    (hφr _) (h i).dvd
  obtain ⟨s, hs⟩ := (maximalIdeal R).fg_of_isNoetherianRing
  have hsd : ∀ y : s, ϖ ∣ ψ y := fun y => by
    have h1 : (y : R) ∈ maximalIdeal R := hs ▸ Ideal.subset_span y.2
    have h2 : ψ y ∈ maximalIdeal V := fun h => h1 (hψ.1 _ h)
    rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at h2
  choose z hz hz' using fun y : s => hdiv (algebraMap R C y) τ _ _ huτ (hφr _) hφτ (hsd y)
  let S : Set C := {τ} ∪ Set.range u ∪ Set.range w ∪ Set.range z
  have hS : S.Finite :=
    (((Set.finite_singleton _).union (Set.finite_range _)).union (Set.finite_range _)).union
      (Set.finite_range _)
  let A := Algebra.adjoin R S
  have hft : Algebra.FiniteType R A := by
    rw [← Subalgebra.fg_iff_finiteType]
    exact Subalgebra.fg_def.2 ⟨S, hS, rfl⟩
  have hN : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have hA : ∀ x ∈ A, φ x ∈ ι.range := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ((rfl | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩
      exacts [⟨_, hφτ.symm⟩, hu' i, hw' i, hz' i]
    | algebraMap r => exact ⟨_, (hφr r).symm⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have mτ : τ ∈ A := Algebra.subset_adjoin (Or.inl (Or.inl (Or.inl rfl)))
  have mu : ∀ i, u i ∈ A := fun i => Algebra.subset_adjoin (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))
  have mw : ∀ i, w i ∈ A := fun i => Algebra.subset_adjoin (Or.inl (Or.inr ⟨i, rfl⟩))
  have mz : ∀ i, z i ∈ A := fun i => Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)
  refine ⟨A, inferInstance, inferInstance, hN, algebraMap R A, ⟨τ, mτ⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    have h1 : algebraMap R C x = algebraMap R C y := congrArg Subtype.val hxy
    rw [hRC, hRC] at h1
    exact Polynomial.C_injective (hinj h1)
  · exact fun h0 => huτ.ne_zero (congrArg Subtype.val h0)
  · intro h0
    obtain ⟨x, hx⟩ := isUnit_iff_exists_inv.1 h0
    have h1 : τ * (x : C) = 1 := congrArg Subtype.val hx
    obtain ⟨v, hv⟩ := hA x x.2
    have h2 := congrArg φ h1
    rw [map_mul, map_one, hφτ, ← hv, ← map_mul, ← map_one ι] at h2
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one _ (hι h2))
  · intro r hr
    rw [← Ideal.mem_span_singleton, ← Ideal.mem_comap]
    rw [← hs] at hr
    refine Ideal.span_le.2 (fun y hy => ?_) hr
    exact Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 ⟨⟨_, mz ⟨y, hy⟩⟩, Subtype.ext (hz ⟨y, hy⟩)⟩)
  · intro i
    exact associated_of_dvd_dvd ⟨⟨_, mw i⟩, Subtype.ext (hw i)⟩ ⟨⟨_, mu i⟩, Subtype.ext (hu i)⟩

theorem main (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [CharZero R] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V)
    (hϖ : Irreducible ϖ) (ψ : R →+* V) (hψ : IsLocalHom ψ) (I : Type) [Finite I] (a : I → R)
    (k : I → ℕ) (h : ∀ i, Associated (ψ (a i)) (ϖ ^ k i)) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ϖ' : W)
      (ψ' : R →+* W) (m : ℕ) (m' : ℕ) (k' : I → ℕ),
      IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ Irreducible ϖ' ∧ Function.Injective ψ' ∧
        IsLocalHom ψ' ∧ 1 ≤ m ∧ 1 ≤ m' ∧
        ∀ i, Associated (ψ' (a i)) (ϖ' ^ k' i) ∧ m * k' i = m' * k i := by
  obtain ⟨A, _, _, _, g, t, hg, ht0, ht, hm, ha⟩ := exists_chart R V ϖ hϖ ψ hψ I a k h
  obtain ⟨W, _, _, hW, f, hc, hf, hft⟩ := exists_complete_dvr A t ht0 ht
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    ((map_ne_zero_iff f hf).2 ht0) hp
  refine ⟨W, inferInstance, inferInstance, hW, p, f.comp g, 1, n, fun i => n * k i, hc, hp,
    hf.comp hg, ⟨fun r hr => ?_⟩, le_rfl, ?_, fun i => ⟨?_, one_mul _⟩⟩
  · by_contra hnu
    exact hft (isUnit_of_dvd_unit (map_dvd f (hm r hnu)) hr)
  · rw [Nat.one_le_iff_ne_zero]
    rintro rfl
    rw [pow_zero, associated_one_iff_isUnit] at hn
    exact hft hn
  · have h1 := (ha i).map f
    rw [map_pow] at h1
    rw [pow_mul]
    exact h1.trans hn.pow_pow

end GlobalTheory.CompleteDiscreteValuationRing
