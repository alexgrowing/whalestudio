import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSubDvdChoosePrimePowOfLtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffAevalOneAddXPowSubOneNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotDvdCoeffAevalOneAddXPowSubOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationPolynomialAtRootOfUnitySubOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLowCoeffNotDvdOfCongrMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExponentStrictlyLeastWeightStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitFamilyOfFiniteCoefficientsStatement

open scoped BigOperators

namespace GlobalTheory.OrderEval

theorem addVal_le_iff_not_dvd {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) (x : O) (n : ℕ) :
    IsDiscreteValuationRing.addVal O x ≤ n ↔ ¬ ϖ ^ (n + 1) ∣ x := by
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hϖ, not_le]
  simp only [nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
  exact (ENat.lt_add_one_iff (ENat.coe_ne_top n)).symm

theorem degree_le_weight {σ : Type} [Fintype σ] {l : ℕ} (hl : 0 < l) (e : σ → ℕ) (m : σ →₀ ℕ) :
    m.degree ≤ ∑ q, m q * l ^ e q := by
  rw [Finsupp.degree_eq_sum]
  exact Finset.sum_le_sum fun q _ => Nat.le_mul_of_pos_right _ (pow_pos hl _)

theorem aeval_subst {O O' σ : Type} [CommRing O] [CommRing O'] [Algebra O O'] (l : ℕ) (e : σ → ℕ)
    (ζ : O') (F : MvPolynomial σ O) :
    Polynomial.aeval (ζ - 1)
      (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1) F)
      = MvPolynomial.aeval (fun q => ζ ^ (l ^ e q) - 1) F := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  simp

theorem le_totient_pow {l : ℕ} (hl : l.Prime) {k : ℕ} (hk : 1 ≤ k) : k ≤ Nat.totient (l ^ k) := by
  rw [Nat.totient_prime_pow hl hk]
  have h1 : k - 1 < l ^ (k - 1) := Nat.lt_pow_self hl.one_lt
  have h2 : 1 ≤ l - 1 := by have := hl.two_le; omega
  calc k ≤ l ^ (k - 1) * 1 := by omega
    _ ≤ _ := Nat.mul_le_mul_left _ h2

theorem exists_low_coeff_of_limit (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (hϖ : Irreducible ϖ) (l : ℕ) (hl : l.Prime) (hd : ϖ ∣ (l : O))
    (σ : Type) [Fintype σ] (ρ : ℕ) (τ : Fin ρ ≃ σ) (D M₀ : ℕ) (I : Type) [Finite I] (μ : I → ℕ)
    (F : ℕ → I → MvPolynomial σ O)
    (hF : ∀ M, M₀ ≤ M → ∀ x, ∃ m : σ →₀ ℕ, m.degree ≤ D ∧ ¬ ϖ ^ (μ x + 1) ∣ (F M x).coeff m) :
    ∃ a : ℕ, ∀ e : σ → ℕ, (∀ i' i : Fin ρ, i' < i → e (τ i') + a ≤ e (τ i)) →
      ∃ W : ℕ, ∀ M₁, ∃ M, M₁ ≤ M ∧ ∀ x, ∃ w ≤ W, ¬ ϖ ^ (μ x + 1) ∣
        (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1)
          (F M x)).coeff w := by
  classical
  obtain ⟨K, hK⟩ := (Set.finite_range μ).bddAbove
  have hK' : ∀ x, μ x ≤ K := fun x => hK ⟨x, rfl⟩
  obtain ⟨G₀, hG₀⟩ := GlobalTheory.T.exists_limit_family_of_finite_coefficients' σ I (Fin (K + 2) → Prop)
    (fun M x m j => ϖ ^ (j : ℕ) ∣ (F M x).coeff m)
  obtain ⟨G, hG⟩ : ∃ G : I → (σ →₀ ℕ) → ℕ → Prop, ∀ N M₁ : ℕ, ∃ M, M₁ ≤ M ∧ ∀ x m,
      m.degree ≤ N → ∀ j, j ≤ K + 1 → (ϖ ^ j ∣ (F M x).coeff m ↔ G x m j) := by
    refine ⟨fun x m j => ∀ h : j < K + 2, G₀ x m ⟨j, h⟩, fun N M₁ => ?_⟩
    obtain ⟨M, hM, h⟩ := hG₀ N M₁
    refine ⟨M, hM, fun x m hm j hj => ?_⟩
    have h2 := h x m hm
    constructor
    · intro h3 h4
      rw [← h2]; exact h3
    · intro h3
      have h4 := h3 (by omega)
      rw [← h2] at h4; exact h4
  have ex0 : ∀ x, ∃ m, ¬ G x m (μ x + 1) := by
    intro x
    obtain ⟨M, hM, h⟩ := hG D M₀
    obtain ⟨m, hm, h2⟩ := hF M hM x
    exact ⟨m, fun h3 => h2 ((h x m hm _ (by have := hK' x; omega)).2 h3)⟩
  have ex : ∀ x, ∃ j, ∃ m, ¬ G x m (j + 1) := fun x => ⟨μ x, ex0 x⟩
  have hν : ∀ x, Nat.find (ex x) ≤ μ x := fun x => Nat.find_min' _ (ex0 x)
  have hS : ∀ x, ∃ m₀ : σ →₀ ℕ, ¬ G x m₀ (Nat.find (ex x) + 1) ∧ ∀ c : σ → ℕ,
      (∀ i, ∑ i' ∈ Finset.Iio i, m₀ (τ i') * c (τ i') < c (τ i)) → ∀ m : σ →₀ ℕ,
      ¬ G x m (Nat.find (ex x) + 1) → m ≠ m₀ → ∑ q, m₀ q * c q < ∑ q, m q * c q := by
    intro x
    obtain ⟨m1, hm1⟩ := Nat.find_spec (ex x)
    obtain ⟨m, ⟨m₀, hm₀, rfl⟩, h⟩ := GlobalTheory.T.exists_least_weight_exponent ρ
      {a | ∃ m : σ →₀ ℕ, ¬ G x m (Nat.find (ex x) + 1) ∧ (fun i => m (τ i)) = a}
      ⟨_, m1, hm1, rfl⟩
    refine ⟨m₀, hm₀, fun c hc m hm hne => ?_⟩
    have h2 := h (fun i => c (τ i)) hc (fun i => m (τ i)) ⟨m, hm, rfl⟩ (by
      intro h3
      apply hne
      ext q
      simpa using congrFun h3 (τ.symm q))
    rw [← τ.sum_comp (fun q => m₀ q * c q), ← τ.sum_comp (fun q => m q * c q)]
    exact h2
  choose m₀ hm₀ hmin using hS
  obtain ⟨B, hB⟩ := (Set.finite_range (fun p : I × σ => m₀ p.1 p.2)).bddAbove
  have hB' : ∀ x q, m₀ x q ≤ B := fun x q => hB ⟨(x, q), rfl⟩
  refine ⟨ρ * B, fun e he => ?_⟩
  obtain ⟨W, hW⟩ := (Set.finite_range (fun x => ∑ q, m₀ x q * l ^ e q)).bddAbove
  have hW' : ∀ x, ∑ q, m₀ x q * l ^ e q ≤ W := fun x => hW ⟨x, rfl⟩
  refine ⟨W, fun M₁ => ?_⟩
  obtain ⟨M, hM, h⟩ := hG W M₁
  refine ⟨M, hM, fun x => ⟨_, hW' x, ?_⟩⟩
  have hc : ∀ i, ∑ i' ∈ Finset.Iio i, m₀ x (τ i') * l ^ e (τ i') < l ^ e (τ i) := by
    intro i
    have h1 : (∑ i' ∈ Finset.Iio i, m₀ x (τ i') * l ^ e (τ i')) * l ^ (ρ * B)
        ≤ ρ * B * l ^ e (τ i) := by
      rw [Finset.sum_mul]
      calc _ ≤ (Finset.Iio i).card • (B * l ^ e (τ i)) := by
            apply Finset.sum_le_card_nsmul
            intro i' hi'
            rw [mul_assoc, ← pow_add]
            exact Nat.mul_le_mul (hB' _ _)
              (Nat.pow_le_pow_right hl.pos (he i' i (Finset.mem_Iio.1 hi')))
        _ ≤ _ := by
            rw [smul_eq_mul, mul_assoc]
            apply Nat.mul_le_mul_right
            simpa using (Finset.card_le_univ (Finset.Iio i))
    have h2 : ρ * B < l ^ (ρ * B) := Nat.lt_pow_self hl.one_lt
    have h3 : 0 < l ^ e (τ i) := pow_pos hl.pos _
    apply lt_of_mul_lt_mul_right (a := l ^ (ρ * B)) _ (Nat.zero_le _)
    calc _ ≤ _ := h1
      _ < l ^ (ρ * B) * l ^ e (τ i) := Nat.mul_lt_mul_of_pos_right h2 h3
      _ = _ := mul_comm _ _
  have hx := hK' x
  have hνx := hν x
  have key := GlobalTheory.T.not_dvd_coeff_aeval_one_add_X_pow_sub_one O ϖ hϖ σ l (Nat.find (ex x)) hl hd (F M x) e (m₀ x) ?_ ?_ ?_
  · exact fun h5 => key ((pow_dvd_pow ϖ (by omega)).trans h5)
  · intro m hm
    rcases Nat.eq_zero_or_pos (Nat.find (ex x)) with h0 | h0
    · rw [h0]; simp
    · have h6 := Nat.find_min (ex x) (m := Nat.find (ex x) - 1) (by omega)
      rw [h x m (hm.trans (hW' x)) _ (by omega)]
      by_contra h7
      exact h6 ⟨m, by rwa [Nat.sub_add_cancel h0]⟩
  · rw [h x _ ((degree_le_weight hl.pos e _).trans (hW' x)) _ (by omega)]
    exact hm₀ x
  · intro m hne hm
    rw [h x _ ((degree_le_weight hl.pos e _).trans (hm.trans (hW' x))) _ (by omega)]
    by_contra h7
    exact absurd (hmin x (fun q => l ^ e q) hc m h7 hne) (not_lt.2 hm)

def lowIdeal {O : Type} [CommRing O] (p : O) (T : ℕ) : Ideal (Polynomial O) where
  carrier := {h | ∀ i ≤ T, p ∣ h.coeff i}
  add_mem' := fun ha hb i hi => by
    rw [Polynomial.coeff_add]; exact dvd_add (ha i hi) (hb i hi)
  zero_mem' := fun i _ => by simp
  smul_mem' := fun c h hh i hi => by
    rw [smul_eq_mul, Polynomial.coeff_mul]
    refine Finset.dvd_sum fun x hx => Dvd.dvd.mul_left (hh _ ?_) _
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    omega

theorem pow_sub_one_mem_lowIdeal {O : Type} [CommRing O] (ϖ : O) (l : ℕ) (hl : l.Prime)
    (hd : ϖ ∣ (l : O)) (n T a : ℕ) (ha : n + T ≤ a) :
    (1 + Polynomial.X : Polynomial O) ^ (l ^ a) - 1 ∈ lowIdeal (ϖ ^ n) T := by
  intro i hi
  rw [Polynomial.coeff_sub, Polynomial.coeff_one_add_X_pow, Polynomial.coeff_one]
  rcases Nat.eq_zero_or_pos i with rfl | h0
  · simp
  · rw [if_neg h0.ne', sub_zero]
    have h1 : T + 1 < l ^ (T + 1) := Nat.lt_pow_self hl.one_lt
    have h2 := GlobalTheory.T.prime_pow_sub_dvd_choose_prime_pow_of_lt l a T i hl h0 (by omega)
    have h3 : l ^ n ∣ (l ^ a).choose i := (pow_dvd_pow l (by omega)).trans h2
    have h4 : ((l ^ n : ℕ) : O) ∣ (((l ^ a).choose i : ℕ) : O) := Nat.cast_dvd_cast h3
    rw [Nat.cast_pow] at h4
    exact (pow_dvd_pow_of_dvd hd n).trans h4

theorem coeff_zero_subst {O σ : Type} [CommRing O] (l : ℕ) (e : σ → ℕ) (g : MvPolynomial σ O) :
    (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1) g).coeff 0
      = g.coeff 0 := by
  rw [Polynomial.coeff_zero_eq_aeval_zero, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  simp only [map_sub, map_pow, map_add, map_one, Polynomial.aeval_X, add_zero, one_pow, sub_self]
  rw [MvPolynomial.aeval_zero']
  rfl

theorem map_subst {O k σ : Type} [CommRing O] [CommRing k] (φ : O →+* k) (l : ℕ) (e : σ → ℕ)
    (g : MvPolynomial σ O) :
    (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1) g).map φ
      = MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial k) ^ (l ^ e q) - 1)
        (g.map φ) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
  | mul_X p q hp => simp [Polynomial.map_mul, hp]

theorem exists_low_coeff_of_factor (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (l : ℕ) (hl : l.Prime)
    (hd : ϖ ∣ (l : O)) (R nmax V s : ℕ) :
    ∃ E W : ℕ, ∀ e : Fin R ⊕ Fin R → ℕ, (∀ i, e (Sum.inl i) ≤ s) → (∀ i, E ≤ e (Sum.inr i)) →
      ∀ M, E ≤ M → ∀ v, v ≤ V → ∀ f Dd g : MvPolynomial (Fin R ⊕ Fin R) O,
      f - Dd * g ∈ Ideal.span (Set.range (fun i : Fin R =>
        (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin R ⊕ Fin R) O)) ∪
        Set.range (fun i : Fin R => (1 + MvPolynomial.X (Sum.inl i)) ^ (l ^ M) - 1)) →
      ¬ ϖ ^ (v + 1) ∣ g.coeff 0 →
      ∀ (u : MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) (n : Fin R → ℕ),
      u.coeff 0 ≠ 0 → (∀ i, n i ≤ nmax) →
      Dd.map (IsLocalRing.residue O) - u * ∏ i, MvPolynomial.X (Sum.inl i) ^ n i ∈
        Ideal.span (Set.range fun q => (MvPolynomial.X q :
          MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) ^ (l ^ M)) →
      ∃ w ≤ W, ¬ ϖ ^ (v + 1) ∣
        (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1)
          f).coeff w := by
  set m₀ := R * (nmax * l ^ s) with hm₀
  refine ⟨V + 1 + (V + 1) * m₀, (V + 1) * m₀, ?_⟩
  intro e he1 he2 M hM v hv f Dd g hf hg u n hu hn hD
  set S : MvPolynomial (Fin R ⊕ Fin R) O →ₐ[O] Polynomial O :=
    MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1) with hS
  have hvm : (v + 1) * m₀ ≤ (V + 1) * m₀ := Nat.mul_le_mul_right _ (by omega)
  have hmem : S (f - Dd * g) ∈ lowIdeal (ϖ ^ (V + 1)) ((V + 1) * m₀) := by
    refine (Ideal.span_le (I := (lowIdeal (ϖ ^ (V + 1)) ((V + 1) * m₀)).comap S)).2 ?_ hf
    rintro p (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · change S _ ∈ lowIdeal _ _
      simp only [hS, MvPolynomial.aeval_X]
      exact pow_sub_one_mem_lowIdeal ϖ l hl hd _ _ _ (he2 i)
    · change S _ ∈ lowIdeal _ _
      simp only [hS, map_sub, map_pow, map_add, map_one, MvPolynomial.aeval_X, add_sub_cancel]
      rw [← pow_mul, ← pow_add]
      exact pow_sub_one_mem_lowIdeal ϖ l hl hd _ _ _ (by omega)
  haveI : Fact l.Prime := ⟨hl⟩
  have hl0 : (l : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact fun h => hϖ.not_isUnit (isUnit_of_dvd_unit hd h)
  haveI : CharP (IsLocalRing.ResidueField O) l := (CharP.charP_iff_prime_eq_zero hl).2 hl0
  have hw : ∑ q, Sum.elim n (fun _ => 0) q * l ^ e q ≤ m₀ := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero]
    calc _ ≤ (Finset.univ : Finset (Fin R)).card • (nmax * l ^ s) := by
          apply Finset.sum_le_card_nsmul
          intro i _
          exact Nat.mul_le_mul (hn i) (Nat.pow_le_pow_right hl.pos (he1 i))
      _ = m₀ := by simp [hm₀]
  have hlt : m₀ < l ^ M := by
    have h1 : M < l ^ M := Nat.lt_pow_self hl.one_lt
    have h2 : m₀ ≤ (V + 1) * m₀ := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have h4 := GlobalTheory.T.coeff_aeval_one_add_X_pow_sub_one_ne_zero' (IsLocalRing.ResidueField O) (Fin R ⊕ Fin R) l M
    (Dd.map (IsLocalRing.residue O)) u (Sum.elim n (fun _ => 0)) e hu
    (by simpa [Fintype.prod_sum_type] using hD) (hw.trans_lt hlt)
  rw [← map_subst, Polynomial.coeff_map, IsLocalRing.residue_ne_zero_iff_isUnit] at h4
  obtain ⟨i, hi, h5⟩ := GlobalTheory.T.exists_low_coeff_not_dvd_of_congr_mul' O ϖ hϖ (S Dd : Polynomial O) (S g : Polynomial O)
    (S f : Polynomial O) m₀ v (V + 1) ((V + 1) * m₀)
    ⟨_, hw, by rw [Polynomial.coeff_coe]; exact h4⟩
    (by rw [Polynomial.coeff_coe, hS, coeff_zero_subst]; exact hg) (by omega) hvm
    (by
      intro i hi
      rw [← Polynomial.coe_mul, ← Polynomial.coe_sub, Polynomial.coeff_coe, ← map_mul, ← map_sub]
      exact hmem i hi)
  rw [Polynomial.coeff_coe] at h5
  exact ⟨i, hi.trans hvm, h5⟩

theorem exists_levels (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (hϖ : Irreducible ϖ) (l : ℕ) (hl : l.Prime) (h0 : (l : O) ≠ 0) (hu : ¬ IsUnit (l : O))
    (J : Type) [Finite J] (v : J → ℕ) (W : ℕ) :
    ∃ N : ℕ, ∀ h : J → Polynomial O, (∀ y, ∃ w ≤ W, ¬ ϖ ^ (v y + 1) ∣ (h y).coeff w) →
      ∃ BB : Finset ℕ, BB.card ≤ N ∧ ∀ k, 1 ≤ k → k ∉ BB →
        ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
          [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') →
          ∀ ζ : O', IsPrimitiveRoot ζ (l ^ k) → ∀ y, Polynomial.aeval (ζ - 1) (h y) ≠ 0 ∧
            Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (Polynomial.aeval (ζ - 1) (h y)) ≤
              (v y : ℝ) / ((IsDiscreteValuationRing.addVal O (l : O)).toNat : ℝ)
                + W / (Nat.totient (l ^ k) : ℝ) := by
  classical
  haveI := Fintype.ofFinite J
  refine ⟨∑ y, (W + v y), fun h hh => ?_⟩
  choose w hw hd using hh
  have hne : ∀ y, (h y).coeff (w y) ≠ 0 := fun y h1 => hd y (by rw [h1]; exact dvd_zero _)
  have hval : ∀ y, (IsDiscreteValuationRing.addVal O ((h y).coeff (w y))).toNat ≤ v y :=
    fun y => ENat.toNat_le_of_le_coe ((addVal_le_iff_not_dvd hϖ _ _).2 (hd y))
  choose BB c hc hB using fun y => GlobalTheory.T.valuation_polynomial_at_root_of_unity_sub_one O l hl h0 hu (h y) (w y) (hne y)
  refine ⟨Finset.univ.biUnion BB, Finset.card_biUnion_le.trans (Finset.sum_le_sum fun y _ =>
    (hc y).trans (Nat.add_le_add (hw y) (hval y))), ?_⟩
  intro k hk hkB O' _ _ _ _ _ hinj ζ hζ y
  obtain ⟨h1, h2⟩ := hB y k hk (fun h3 => hkB (Finset.mem_biUnion.2 ⟨y, Finset.mem_univ _, h3⟩))
  obtain ⟨h3, h4⟩ := h2 O' hinj ζ hζ
  refine ⟨h3, h4 ▸ h1.trans (add_le_add ?_ ?_)⟩
  · unfold Formalism.MainNotions.BlochKatoReduction.Gen.nval
    exact div_le_div_of_nonneg_right (by exact_mod_cast hval y) (Nat.cast_nonneg _)
  · exact div_le_div_of_nonneg_right (by exact_mod_cast hw y) (Nat.cast_nonneg _)

theorem order_eval : ∀ (O₀ : Type) [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀] [Finite (IsLocalRing.ResidueField O₀)] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O₀ O] [IsLocalHom (algebraMap O₀ O)], Function.Injective (algebraMap O₀ O) → ∀ (l : ℕ), l.Prime → (l : O₀) ≠ 0 → ¬ IsUnit (l : O₀) → ∀ (R D nmax M₀ : ℕ) (I J : Type) [Finite I] [Finite J] (μ : I → ℕ) (v : J → ℕ) (F : ℕ → I → MvPolynomial (Fin R ⊕ Fin R) O₀) (f Dd g : ℕ → J → MvPolynomial (Fin R ⊕ Fin R) O), (∀ M, M₀ ≤ M → ∀ x, ∃ m : Fin R ⊕ Fin R →₀ ℕ, m.degree ≤ D ∧ IsDiscreteValuationRing.addVal O₀ ((F M x).coeff m) ≤ μ x) → (∀ M, M₀ ≤ M → ∀ y, f M y - Dd M y * g M y ∈ Ideal.span (Set.range (fun i : Fin R => (MvPolynomial.X (Sum.inr i) : MvPolynomial (Fin R ⊕ Fin R) O)) ∪ Set.range (fun i : Fin R => (1 + MvPolynomial.X (Sum.inl i)) ^ (l ^ M) - 1)) ∧ IsDiscreteValuationRing.addVal O ((g M y).coeff 0) ≤ v y ∧ ∃ (u : MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) (n : Fin R → ℕ), u.coeff 0 ≠ 0 ∧ (∀ i, n i ≤ nmax) ∧ (Dd M y).map (IsLocalRing.residue O) - u * ∏ i, MvPolynomial.X (Sum.inl i) ^ n i ∈ Ideal.span (Set.range fun q => (MvPolynomial.X q : MvPolynomial (Fin R ⊕ Fin R) (IsLocalRing.ResidueField O)) ^ (l ^ M))) → ∀ ε : ℝ, 0 < ε → ∃ (M k : ℕ) (e : Fin R ⊕ Fin R → ℕ), M₀ ≤ M ∧ 1 ≤ k ∧ k ≤ M ∧ (∀ q, e q < k ∧ (l : ℝ) ^ e q / (Nat.totient (l ^ k) : ℝ) ≤ ε) ∧ ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')], Function.Injective (algebraMap O O') → ∀ ζ : O', IsPrimitiveRoot ζ (l ^ k) → (∀ x, MvPolynomial.aeval (fun q => ζ ^ (l ^ e q) - 1) ((F M x).map (algebraMap O₀ O)) ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (MvPolynomial.aeval (fun q => ζ ^ (l ^ e q) - 1) ((F M x).map (algebraMap O₀ O))) ≤ (μ x : ℝ) / ((IsDiscreteValuationRing.addVal O₀ (l : O₀)).toNat : ℝ) + ε) ∧ (∀ y, MvPolynomial.aeval (fun q => ζ ^ (l ^ e q) - 1) (f M y) ≠ 0 ∧ Formalism.MainNotions.BlochKatoReduction.Gen.nval O' l (MvPolynomial.aeval (fun q => ζ ^ (l ^ e q) - 1) (f M y)) ≤ (v y : ℝ) / ((IsDiscreteValuationRing.addVal O (l : O)).toNat : ℝ) + ε) := by
  intro O₀ _ _ _ _ O _ _ _ _ _ hinj₀ l hl hl0 hlu R D nmax M₀ I J _ _ μ v F f Dd g hF hf ε hε
  classical
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible O₀
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hl0' : (l : O) ≠ 0 := by
    rw [← map_natCast (algebraMap O₀ O)]
    exact fun h => hl0 (hinj₀ (by rw [h, map_zero]))
  have hlu' : ¬ IsUnit (l : O) := by
    rw [← map_natCast (algebraMap O₀ O)]
    exact fun h => hlu (IsLocalHom.map_nonunit _ h)
  have hdv : ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (π : A),
      Irreducible π → ¬ IsUnit (l : A) → π ∣ (l : A) := by
    intro A _ _ _ π hπ h
    rw [← Ideal.mem_span_singleton, ← hπ.maximalIdeal_eq]
    exact h
  obtain ⟨a, ha⟩ := exists_low_coeff_of_limit O₀ ϖ₀ hϖ₀ l hl (hdv _ _ hϖ₀ hlu) (Fin R ⊕ Fin R)
    (R + R) finSumFinEquiv.symm D M₀ I μ F (fun M hM x => by
      obtain ⟨m, h1, h2⟩ := hF M hM x
      exact ⟨m, h1, (addVal_le_iff_not_dvd hϖ₀ _ _).1 h2⟩)
  obtain ⟨V, hV⟩ := (Set.finite_range v).bddAbove
  obtain ⟨E, W₂, hE⟩ := exists_low_coeff_of_factor O ϖ hϖ l hl (hdv _ _ hϖ hlu') R nmax V (a * R)
  obtain ⟨e, he0, he1, he2⟩ : ∃ e : Fin R ⊕ Fin R → ℕ,
      (∀ i' i : Fin (R + R), i' < i →
        e (finSumFinEquiv.symm i') + a ≤ e (finSumFinEquiv.symm i)) ∧
      (∀ i, e (Sum.inl i) ≤ a * R) ∧ (∀ i, E ≤ e (Sum.inr i)) := by
    refine ⟨Sum.elim (fun i => a * i) (fun i => a * (i + R) + E), ?_, ?_, ?_⟩
    · intro i' i hi
      obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i'
      obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective i
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      have aux : ∀ s t : ℕ, s < t → a * s + a ≤ a * t := fun s t h =>
        Nat.mul_le_mul_left a (Nat.succ_le_of_lt h)
      have h2 := aux _ _ (Fin.lt_def.1 hi)
      rcases p with p | p <;> rcases q with q | q
      · simpa using h2
      · simp at h2 ⊢; omega
      · exfalso
        have h3 := Fin.lt_def.1 hi
        have h4 := q.2
        simp at h3; omega
      · simp at h2 ⊢; omega
    · intro i
      exact Nat.mul_le_mul_left a i.2.le
    · intro i
      exact Nat.le_add_left _ _
  obtain ⟨W₁, hW₁⟩ := ha e he0
  obtain ⟨N₁, hN₁⟩ := exists_levels O₀ ϖ₀ hϖ₀ l hl hl0 hlu I μ W₁
  obtain ⟨N₂, hN₂⟩ := exists_levels O ϖ hϖ l hl hl0' hlu' J v W₂
  obtain ⟨C, hC⟩ := (Set.finite_range (fun q => l ^ e q)).bddAbove
  have hC' : ∀ q, l ^ e q ≤ C := fun q => hC ⟨q, rfl⟩
  obtain ⟨k₁, hk₁⟩ := exists_nat_ge (((C + W₁ + W₂ : ℕ) : ℝ) / ε)
  obtain ⟨M, hM, hMF⟩ := hW₁ (M₀ + E + (k₁ + C + 1 + (N₁ + N₂)))
  obtain ⟨B₁, hB₁, hb₁⟩ := hN₁ _ hMF
  obtain ⟨B₂, hB₂, hb₂⟩ := hN₂ (fun y => MvPolynomial.aeval
      (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1) (f M y)) (fun y => by
    obtain ⟨h1, h2, u, n, h3, h4, h5⟩ := hf M (by omega) y
    exact hE e he1 he2 M (by omega) (v y) (hV ⟨y, rfl⟩) _ _ _ h1
      ((addVal_le_iff_not_dvd hϖ _ _).1 h2) u n h3 h4 h5)
  obtain ⟨k, hk, hkB⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := B₁ ∪ B₂) (t := Finset.Icc (k₁ + C + 1) (k₁ + C + 1 + (N₁ + N₂))) (by
      have := Finset.card_union_le B₁ B₂
      rw [Nat.card_Icc]; omega)
  rw [Finset.mem_Icc] at hk
  rw [Finset.mem_union, not_or] at hkB
  have hk1 : 1 ≤ k := by omega
  have hsm : ∀ c : ℕ, c ≤ C + W₁ + W₂ → (c : ℝ) / (Nat.totient (l ^ k) : ℝ) ≤ ε := by
    intro c hc
    have h1 : (k₁ : ℝ) ≤ Nat.totient (l ^ k) := by
      have := le_totient_pow hl hk1
      exact_mod_cast (by omega : k₁ ≤ Nat.totient (l ^ k))
    have h2 : (0 : ℝ) < Nat.totient (l ^ k) := by
      have := le_totient_pow hl hk1
      exact_mod_cast (by omega : 0 < Nat.totient (l ^ k))
    have h3 : (c : ℝ) ≤ ((C + W₁ + W₂ : ℕ) : ℝ) := by exact_mod_cast hc
    rw [div_le_iff₀ hε] at hk₁
    rw [div_le_iff₀ h2]
    nlinarith
  refine ⟨M, k, e, by omega, hk1, by omega, fun q => ⟨?_, ?_⟩, ?_⟩
  · have h1 : e q < l ^ e q := Nat.lt_pow_self hl.one_lt
    have := hC' q
    omega
  · have := hsm (l ^ e q) (by have := hC' q; omega)
    rwa [Nat.cast_pow] at this
  intro O' _ _ _ _ _ hinj ζ hζ
  constructor
  · intro x
    letI : Algebra O₀ O' := ((algebraMap O O').comp (algebraMap O₀ O)).toAlgebra
    haveI : IsScalarTower O₀ O O' := IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsLocalHom (algebraMap O₀ O') :=
      RingHom.isLocalHom_comp (algebraMap O O') (algebraMap O₀ O)
    have h := hb₁ k hk1 hkB.1 O' (hinj.comp hinj₀) ζ hζ x
    rw [aeval_subst] at h
    rw [MvPolynomial.aeval_map_algebraMap]
    exact ⟨h.1, h.2.trans (add_le_add le_rfl (hsm W₁ (by omega)))⟩
  · intro y
    have h := hb₂ k hk1 hkB.2 O' hinj ζ hζ y
    rw [aeval_subst] at h
    exact ⟨h.1, h.2.trans (add_le_add le_rfl (hsm W₂ (by omega)))⟩

end GlobalTheory.OrderEval
