import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormByPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.KTFiniteDimensional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.UniformizerOfResidueIndep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GoodPrimesProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ScaleMultiHomogeneous

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem finsum_liesOver_eq_finsum_good (c : ι) (p : Ideal (KTp K d.D d.N)) (g : Ω c) (hg : g ≠ 0)
    (F : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) → WithTop ℤ → ℤ)
    (hF : ∀ w, F w 0 = 0) :
    (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p),
      F w (w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g))) =
    ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
      F w (d.Wres c w g) := by
  classical
  refine finsum_congr fun w => ?_
  by_cases hG : w ∈ d.GoodP c p
  · have hO : w ∈ d.OverP c p := hG.1
    simp only [finsum_eq_if, if_pos hO, if_pos hG]
    rfl
  · simp only [finsum_eq_if, if_neg hG]
    split_ifs with hO
    · have h0 : d.Wres c w g = 0 := by
        by_contra hne
        exact hG ⟨hO, g, hg, hne⟩
      have h1 : w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g) = 0 := h0
      rw [h1, hF]
    · rfl

theorem norm_factorization_clause (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (g : Ω c) (hg : g ≠ 0) :
    ∃ κ : K, κ ≠ 0 ∧
      letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
      Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g) =
        algebraMap K (KTf K d.D d.N) κ *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
              (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
                (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w g)) := by
  obtain ⟨-, hy⟩ := d.norm_by_places hd h c
  have hne : algebraMap (Ω c) (OmS (Ω c) d.D d.N) g ≠ 0 := by
    intro h0
    exact hg ((map_eq_zero_iff _ (algebraMap (Ω c) (OmS (Ω c) d.D d.N)).injective).mp h0)
  obtain ⟨-, κ, hκ, hN⟩ := hy _ hne
  refine ⟨κ, hκ, ?_⟩
  rw [hN]
  congr 1
  refine finprod_congr fun p => finprod_congr fun _ => ?_
  congr 1
  exact d.finsum_liesOver_eq_finsum_good c p g hg (fun w t => (d.fze h c w : ℤ) * WithTop.untopD 0 t)
    (fun w => by simp)

theorem prod_zpow_eq_zpow_sum {M : Type*} [CommGroupWithZero M] {α : Type*} (s : Finset α)
    (a : M) (ha : a ≠ 0) (k : α → ℤ) : ∏ p ∈ s, a ^ k p = a ^ (∑ p ∈ s, k p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, zpow_add₀ ha]

theorem int_eq_zero_of_two_zpow {F : Type*} [Field F] [CharZero F] {M : ℤ}
    (h : (2 : F) ^ M = 1) : M = 0 := by
  rcases M with n | n
  · have h' : ((2 ^ n : ℕ) : F) = 1 := by push_cast; simpa using h
    have h2 : 2 ^ n = 1 := by exact_mod_cast h'
    have := Nat.pow_eq_one.mp h2
    have hn : n = 0 := by omega
    simp [hn]
  · exfalso
    rw [zpow_negSucc, inv_eq_one] at h
    have h' : ((2 ^ (n + 1) : ℕ) : F) = 1 := by push_cast; exact h
    have h2 : 2 ^ (n + 1) = 1 := by exact_mod_cast h'
    have := Nat.pow_eq_one.mp h2
    omega

private theorem sum_fst_lemma {D N : ℕ} [DecidablePred (fun v : TVar D N => v.1 = (1 : Fin (D + 1)))]
    (s : TVar D N →₀ ℕ) :
    ∑ v ∈ Finset.univ.filter (fun v : TVar D N => v.1 = (1 : Fin (D + 1))), s v = ∑ j, s (1, j) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single (1 : Fin (D + 1))]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h1
    exact absurd (Finset.mem_univ _) h1

private theorem scaleBlock_eq_C_pow_mul {D N : ℕ} (u : Kˣ) (q : KTp K D N) (m : ℕ)
    (hq : ∀ s ∈ q.support, ∑ j, s (1, j) = m) :
    sigP (N := N) (1 : Fin (D + 1)) u q = MvPolynomial.C ((u : K) ^ m) * q := by
  have hq' : q = ∑ s ∈ q.support, MvPolynomial.monomial s (q.coeff s) := q.as_sum
  rw [hq', map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [sigP, scaleEquiv_monomial, sum_fst_lemma, hq s hs]

private theorem key_lemma_3 (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (r : Ω c) (hr : r ≠ 0)
    (n : Ideal (KTp K d.D d.N) → ℤ) (hfin : {p | p ∈ d.HtOne ∧ n p ≠ 0}.Finite)
    (hN : ∃ κ : K, κ ≠ 0 ∧
      letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
      Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) r) =
        algebraMap K (KTf K d.D d.N) κ *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ n p)
    (hhom : ∀ p ∈ d.HtOne, n p ≠ 0 → ∀ s ∈ (d.gen p).support, ∑ j, s (1, j) = d.dg (d.gen p)) :
    (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), n p * (d.dg (d.gen p) : ℤ)) = 0 := by
  classical
  obtain ⟨κ, hκ, hN⟩ := hN
  have hb : (1 : Fin (d.D + 1)) ≠ 0 := by
    have := hd.D_ge
    rw [Ne, Fin.one_eq_zero_iff]
    omega
  have hT : ∀ p, p ∈ hfin.toFinset ↔ p ∈ d.HtOne ∧ n p ≠ 0 := fun p => Set.Finite.mem_toFinset hfin
  have hprod : ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ n p =
      ∏ p ∈ hfin.toFinset, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ n p := by
    apply finprod_mem_eq_prod_of_subset
    · rintro p ⟨hp, hs⟩
      refine (hT p).mpr ⟨hp, fun h0 => hs ?_⟩
      simp [h0]
    · intro p hp
      exact ((hT p).mp hp).1
  have hsum : (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), n p * (d.dg (d.gen p) : ℤ)) =
      ∑ p ∈ hfin.toFinset, n p * (d.dg (d.gen p) : ℤ) := by
    apply finsum_mem_eq_sum_of_subset
    · rintro p ⟨hp, hs⟩
      refine (hT p).mpr ⟨hp, fun h0 => hs ?_⟩
      simp [h0]
    · intro p hp
      exact ((hT p).mp hp).1
  rw [hsum]
  rw [hprod] at hN
  have hne : algebraMap (Ω c) (OmS (Ω c) d.D d.N) r ≠ 0 := by
    intro h0
    exact hr ((map_eq_zero_iff _ (algebraMap (Ω c) (OmS (Ω c) d.D d.N)).injective).mp h0)
  have hX : (letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
      Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) r)) ≠ 0 := by
    letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
    by_cases hfd : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
    · exact Algebra.norm_ne_zero_iff.mpr hne
    · rw [Algebra.norm_eq_one_of_not_exists_basis]
      · exact one_ne_zero
      · rintro ⟨s, ⟨bs⟩⟩
        exact hfd (Module.Finite.of_basis bs)
  obtain ⟨u, hu⟩ : ∃ u : Kˣ, (u : K) = 2 := ⟨Units.mk0 2 two_ne_zero, rfl⟩
  have hσ := d.sigF_norm h c 1 hb u r
  have hκσ : sigF (N := d.N) (1 : Fin (d.D + 1)) u (algebraMap K (KTf K d.D d.N) κ) =
      algebraMap K (KTf K d.D d.N) κ := by
    rw [IsScalarTower.algebraMap_apply K (KTp K d.D d.N) (KTf K d.D d.N), sigF,
      IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    congr 1
    exact (sigP (N := d.N) (1 : Fin (d.D + 1)) u).commutes κ
  have hgσ : ∀ p ∈ hfin.toFinset, sigF (N := d.N) (1 : Fin (d.D + 1)) u
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ n p) =
      algebraMap K (KTf K d.D d.N) 2 ^ (n p * (d.dg (d.gen p) : ℤ)) *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ n p := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := (hT p).mp hp
    rw [map_zpow₀, sigF, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    have hs : (sigP (N := d.N) (1 : Fin (d.D + 1)) u).toRingEquiv (d.gen p) =
        MvPolynomial.C ((u : K) ^ d.dg (d.gen p)) * d.gen p :=
      scaleBlock_eq_C_pow_mul u (d.gen p) _ (hhom p hp1 hp2)
    rw [hs, map_mul, mul_zpow]
    congr 1
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, map_pow, hu,
      ← zpow_natCast, ← zpow_mul, mul_comm]
  have h2 : algebraMap K (KTf K d.D d.N) 2 ≠ 0 :=
    (map_ne_zero (algebraMap K (KTf K d.D d.N))).mpr two_ne_zero
  rw [hN] at hσ hX
  simp only [map_mul, map_prod] at hσ
  rw [hκσ, Finset.prod_congr rfl hgσ, Finset.prod_mul_distrib, prod_zpow_eq_zpow_sum _ _ h2] at hσ
  have h1 : algebraMap K (KTf K d.D d.N) 2 ^ (∑ p ∈ hfin.toFinset, n p * (d.dg (d.gen p) : ℤ)) = 1 := by
    apply mul_right_cancel₀ hX
    rw [one_mul]
    linear_combination hσ
  rw [← map_zpow₀, map_eq_one_iff _ (algebraMap K (KTf K d.D d.N)).injective] at h1
  exact int_eq_zero_of_two_zpow h1

theorem key_degree (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (r : Ω c) (hr : r ≠ 0) :
    (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w r)) * (d.dg (d.gen p) : ℤ)) = 0 := by
  classical
  have hb : (1 : Fin (d.D + 1)) ≠ 0 := by
    have := hd.D_ge
    rw [Ne, Fin.one_eq_zero_iff]
    omega
  refine key_lemma_3 d hd h c r hr (fun p => ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
      (_ : w ∈ d.GoodP c p), (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w r))
    ?_ (d.norm_factorization_clause hd h c r hr) ?_
  · obtain ⟨-, hy⟩ := d.norm_by_places hd h c
    have hne : algebraMap (Ω c) (OmS (Ω c) d.D d.N) r ≠ 0 := by
      intro h0
      exact hr ((map_eq_zero_iff _ (algebraMap (Ω c) (OmS (Ω c) d.D d.N)).injective).mp h0)
    refine (hy _ hne).1.subset ?_
    rintro p ⟨hp, hsum⟩
    refine ⟨hp, ?_⟩
    by_contra hcon
    push_neg at hcon
    apply hsum
    refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
    by_cases hw : w ∈ d.GoodP c p
    · have h0 : d.Wres c w r = 0 := hcon w hw.1
      simp [finsum_eq_if, hw, h0]
    · simp [finsum_eq_if, hw]
  intro p hp hn0 s hs
  have hex : ∃ w, w ∈ d.GoodP c p := by
    by_contra hne
    push_neg at hne
    apply hn0
    refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
    simp [finsum_eq_if, hne w]
  have := (d.good_primes_properties hd h c).2.1 p hp hex s hs 1
  simpa [hb] using this

theorem good_adm (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    {w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)} (hw : w ∈ d.GoodP c p) :
    d.admitted c (d.Wres c w) := by
  obtain ⟨hO, a, ha, hwa⟩ := hw
  rcases d.PlaceTrivialOrPositive hd h c p hp w hO with h1 | h2
  · exact absurd (h1 a ha) hwa
  · exact h2.1

theorem goodP_finite (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)}
    (hp : p ∈ d.HtOne) : (d.GoodP c p).Finite :=
  ((d.norm_by_places hd h c).1 p hp).subset fun _ hw => hw.1

theorem nP_mul (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {G G' : WT} {f g : A c} (hf : f ∈ 𝒜 c G)
    (hg : g ∈ 𝒜 c G') (hf0 : f ≠ 0) (hg0 : g ≠ 0) {p : Ideal (KTp K d.D d.N)}
    (hp : p ∈ d.HtOne) :
    d.nP h c (G + G') (f * g) p = d.nP h c G f p + d.nP h c G' g p := by
  unfold nP
  rw [← finsum_mem_add_distrib (d.goodP_finite hd h c hp)]
  refine finsum_mem_congr rfl fun w hw => ?_
  rw [hd.ord_mul c _ (d.good_adm hd h c hp hw) hf hg hf0 hg0, mul_add]

theorem untopD_eq {t : WithTop ℤ} (ht : t ≠ ⊤) : ((t.untopD 0 : ℤ) : WithTop ℤ) = t := by
  induction t using WithTop.recTopCoe with
  | top => exact absurd rfl ht
  | coe a => simp

theorem nP_smul (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {G : WT} {f : A c} (hf : f ∈ 𝒜 c G)
    (hf0 : f ≠ 0) {a : Ω c} (ha : a ≠ 0) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) :
    d.nP h c G (a • f) p = d.nP h c G f p +
      ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
        (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w a) := by
  unfold nP
  rw [← finsum_mem_add_distrib (d.goodP_finite hd h c hp)]
  refine finsum_mem_congr rfl fun w hw => ?_
  have key := hd.ord_smul c _ (d.good_adm hd h c hp hw) (G := G) (f := f) a hf hf0 ha
  have hva : (d.Wres c w) a ≠ ⊤ := by
    intro htop
    exact ha ((AddValuation.top_iff _).mp htop)
  rw [← untopD_eq hva, ← WithTop.coe_add] at key
  rw [WithTop.coe_inj.mp key]
  ring

theorem use₈ (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (r : Ω c) (hr : r ≠ 0) :
    {p | p ∈ d.HtOne ∧ (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ))
      (_ : w ∈ d.GoodP c p), (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w r)) ≠ 0}.Finite := by
  obtain ⟨-, hy⟩ := d.norm_by_places hd h c
  have hne : algebraMap (Ω c) (OmS (Ω c) d.D d.N) r ≠ 0 := by
    intro h0
    exact hr ((map_eq_zero_iff _ (algebraMap (Ω c) (OmS (Ω c) d.D d.N)).injective).mp h0)
  refine (hy _ hne).1.subset ?_
  rintro p ⟨hp, hsum⟩
  refine ⟨hp, ?_⟩
  by_contra hcon
  push_neg at hcon
  apply hsum
  refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
  classical
  by_cases hw : w ∈ d.GoodP c p
  · have h0 : d.Wres c w r = 0 := hcon w hw.1
    simp [finsum_eq_if, hw, h0]
  · simp [finsum_eq_if, hw]

theorem arithDegree_additive (hd : d.AxH 𝒜) (h : d.S1) :
    (∀ (G : WT) (ta ta' : ∀ c, A c), (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) →
      (∀ c, ta' c ∈ 𝒜 c G ∧ ta' c ≠ 0) → d.aG h G ta = d.aG h G ta') ∧
    (∀ (G G' : WT) (ta ta' : ∀ c, A c), (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) →
      (∀ c, ta' c ∈ 𝒜 c G' ∧ ta' c ≠ 0) → d.aG h (G + G') (ta * ta') = d.aG h G ta + d.aG h G' ta') := by
  have hfin1 : ∀ c (G : WT) (f : A c), f ∈ 𝒜 c G → f ≠ 0 →
      (d.HtOne ∩ Function.support fun p => d.nP h c G f p * (d.dg (d.gen p) : ℤ)).Finite := by
    intro c G f hf hf0
    refine ((d.good_primes_properties hd h c).2.2.1 G f hf hf0).subset ?_
    rintro p ⟨hp, hs⟩
    refine ⟨hp, fun h0 => hs ?_⟩
    simp [h0]
  refine ⟨?_, ?_⟩
  · intro G ta ta' hta hta'
    unfold aG
    refine Finset.sum_congr rfl fun c _ => ?_
    have hv : (⟨ta c, (hta c).1⟩ : 𝒜 c G) ≠ 0 := by
      intro h0
      apply (hta c).2
      simpa using congrArg Subtype.val h0
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hv).mp (hd.finrank_one c G)
      ⟨ta' c, (hta' c).1⟩
    have ha' : a • ta c = ta' c := congrArg Subtype.val ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply (hta' c).2
      rw [← ha', zero_smul]
    have hS : (d.HtOne ∩ Function.support fun p =>
        (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
          (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w a)) * (d.dg (d.gen p) : ℤ)).Finite := by
      refine (d.use₈ hd h c a ha0).subset ?_
      rintro p ⟨hp, hs⟩
      refine ⟨hp, fun h0 => hs ?_⟩
      simp [h0]
    have e : ∀ p ∈ d.HtOne, d.nP h c G (a • ta c) p * (d.dg (d.gen p) : ℤ) =
        d.nP h c G (ta c) p * (d.dg (d.gen p) : ℤ) +
          (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
            (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w a)) * (d.dg (d.gen p) : ℤ) := by
      intro p hp
      rw [d.nP_smul hd h c (hta c).1 (hta c).2 ha0 hp, add_mul]
    rw [← ha', finsum_mem_congr rfl e,
      finsum_mem_add_distrib' (hfin1 c G _ (hta c).1 (hta c).2) hS,
      d.key_degree hd h c a ha0, add_zero]
  · intro G G' ta ta' hta hta'
    unfold aG
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    have e : ∀ p ∈ d.HtOne, d.nP h c (G + G') ((ta * ta') c) p * (d.dg (d.gen p) : ℤ) =
        d.nP h c G (ta c) p * (d.dg (d.gen p) : ℤ) + d.nP h c G' (ta' c) p * (d.dg (d.gen p) : ℤ) := by
      intro p hp
      rw [Pi.mul_apply, d.nP_mul hd h c (hta c).1 (hta' c).1 (hta c).2 (hta' c).2 hp, add_mul]
    rw [finsum_mem_congr rfl e, finsum_mem_add_distrib' (hfin1 c G _ (hta c).1 (hta c).2)
      (hfin1 c G' _ (hta' c).1 (hta' c).2)]

theorem norm_factorization (hd : d.AxH 𝒜) (h : d.S1) :
    (∀ c (g : Ω c), g ≠ 0 → ∃ κ : K, κ ≠ 0 ∧
      letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
      Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g) =
        algebraMap K (KTf K d.D d.N) κ *
          ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
              (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p),
                (d.fze h c w : ℤ) * WithTop.untopD 0 (d.Wres c w g))) ∧
    (∀ (G : WT) (ta ta' : ∀ c, A c), (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) →
      (∀ c, ta' c ∈ 𝒜 c G ∧ ta' c ≠ 0) → d.aG h G ta = d.aG h G ta') ∧
    (∀ (G G' : WT) (ta ta' : ∀ c, A c), (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) →
      (∀ c, ta' c ∈ 𝒜 c G' ∧ ta' c ≠ 0) → d.aG h (G + G') (ta * ta') = d.aG h G ta + d.aG h G' ta') := by
  exact ⟨fun c g hg => d.norm_factorization_clause hd h c g hg, (d.arithDegree_additive hd h).1, (d.arithDegree_additive hd h).2⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
