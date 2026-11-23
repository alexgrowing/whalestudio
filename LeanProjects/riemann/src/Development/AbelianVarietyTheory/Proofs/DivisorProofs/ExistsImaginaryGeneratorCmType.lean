import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex ComplexConjugate

noncomputable section

namespace GlobalTheory.SignGen

theorem gen_mod (R E : Type) [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
    (hinj : Function.Injective (algebraMap R E)) (M : Submodule R E) (hM : IsUnit M) (c : R) (hc : c ≠ 0) :
    ∃ ξ₀ ∈ M, M ≤ Submodule.span R {ξ₀} ⊔ Ideal.span {c} • M := by
  classical
  obtain ⟨N, hN⟩ := hM.exists_right_inv
  have h1 : (1 : E) ∈ (1 : Submodule R E) := Submodule.one_le.1 le_rfl
  have hN0 : ∃ ν ∈ N, ν ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hb : N = ⊥ := eq_bot_iff.2 (fun x hx => (Submodule.mem_bot R).2 (hcon x hx))
    rw [hb, Submodule.mul_bot] at hN
    rw [← hN, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  have hM0 : ∃ η ∈ M, η ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hb : M = ⊥ := eq_bot_iff.2 (fun x hx => (Submodule.mem_bot R).2 (hcon x hx))
    rw [hb, Submodule.bot_mul] at hN
    rw [← hN, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  obtain ⟨ν, hνN, hν0⟩ := hN0
  have hMsub : ∀ η ∈ M, ∃ a : R, η = a • ν⁻¹ := by
    intro η hη
    have hm : η * ν ∈ (1 : Submodule R E) := hN ▸ Submodule.mul_mem_mul hη hνN
    obtain ⟨a, ha⟩ := Submodule.mem_one.1 hm
    exact ⟨a, by rw [Algebra.smul_def, ha]; field_simp⟩
  let f : R →ₗ[R] E := LinearMap.toSpanSingleton R E ν⁻¹
  have hf : ∀ a, f a = a • ν⁻¹ := fun _ => rfl
  let J : Ideal R := Submodule.comap f M
  have hmapJ : Submodule.map f J = M := by
    apply le_antisymm (Submodule.map_comap_le f M)
    intro η hη
    obtain ⟨a, rfl⟩ := hMsub η hη
    exact ⟨a, by simpa [J, Submodule.mem_comap, hf] using hη, rfl⟩
  have hJ0 : Ideal.span {c} * J ≠ 0 := by
    obtain ⟨η, hη, hη0⟩ := hM0
    obtain ⟨a, rfl⟩ := hMsub η hη
    have haJ : a ∈ J := by simpa [J, Submodule.mem_comap, hf] using hη
    have ha0 : a ≠ 0 := by rintro rfl; simp at hη0
    intro h0
    have hmem : c * a ∈ Ideal.span {c} * J := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self c) haJ
    rw [h0, Submodule.zero_eq_bot, Submodule.mem_bot] at hmem
    exact mul_ne_zero hc ha0 hmem
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_sup_span_eq (I := Ideal.span {c} * J) (J := J) Ideal.mul_le_right hJ0
  have hrJ : r ∈ J := hr ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self r)
  refine ⟨f r, hrJ, ?_⟩
  have hmap := congrArg (Submodule.map f) hr
  rw [hmapJ, Submodule.map_sup, ← Ideal.smul_eq_mul, Submodule.map_smul'', hmapJ] at hmap
  rw [Ideal.span, Submodule.map_span, Set.image_singleton] at hmap
  calc M = _ := hmap.symm
    _ ≤ _ := by rw [sup_comm]

theorem nakayama_int (R E : Type) [CommRing R] [Field E] [Algebra R E] [Module.Finite ℤ R]
    (M : Submodule R E) (hM : M.FG) (l : ℕ) (ξ : E)
    (h : M ≤ Submodule.span R {ξ} ⊔ Ideal.span {(l : R)} • M) :
    ∀ η ∈ M, ∃ n : ℕ, n.Coprime l ∧ ∃ a : R, (n : E) * η = algebraMap R E a * ξ := by
  classical
  have hfg : (M.restrictScalars ℤ).FG := hM.restrictScalars
  have hle : M.restrictScalars ℤ ≤
      (Submodule.span R {ξ}).restrictScalars ℤ ⊔ Ideal.span {(l : ℤ)} • M.restrictScalars ℤ := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (h hx)
    rw [Submodule.ideal_span_singleton_smul] at hz
    obtain ⟨m, hm, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hz
    refine Submodule.add_mem_sup hy ?_
    have : (l : R) • m = (l : ℤ) • m := by
      rw [Algebra.smul_def, zsmul_eq_mul]; simp
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hm
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hfg le_rfl hle
  intro η hη
  have hrη : r • η ∈ (Submodule.span R {ξ}).restrictScalars ℤ :=
    hr (Submodule.smul_mem_pointwise_smul η r _ hη)
  rw [Submodule.restrictScalars_mem, Submodule.mem_span_singleton] at hrη
  obtain ⟨a, ha⟩ := hrη
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.1 hr1
  refine ⟨r.natAbs, ?_, ?_⟩
  · have hc : IsCoprime r (l : ℤ) := ⟨1, -k, by linarith⟩
    have := Int.isCoprime_iff_gcd_eq_one.1 hc
    simpa [Int.gcd, Nat.Coprime] using this
  · rw [zsmul_eq_mul] at ha
    rw [Algebra.smul_def] at ha
    rcases Int.natAbs_eq r with hr' | hr'
    · refine ⟨a, ?_⟩
      have e : ((r.natAbs : ℤ) : E) = (r : E) := by rw [← hr']
      rw [← Int.cast_natCast, e, ha]
    · refine ⟨-a, ?_⟩
      have e0 : (r.natAbs : ℤ) = -r := by omega
      have e : ((r.natAbs : ℤ) : E) = -(r : E) := by rw [e0, Int.cast_neg]
      rw [← Int.cast_natCast, e, map_neg, neg_mul, neg_mul, ha]

theorem cm_restrict_inj (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) (φ : I → E →+* ℂ)
    (hφ : IsCMType φ) (i j : I)
    (h : ∀ a : OF E, φ i (algebraMap (OF E) E a) = φ j (algebraMap (OF E) E a)) : i = j := by
  classical
  have key : ∀ a : OF E, φ i ((a : maximalRealSubfield E) : E) = φ j ((a : maximalRealSubfield E) : E) := h
  have hF : ∀ x : E, IsCMField.complexConj E x = x → φ i x = φ j x := by
    intro x hx
    rw [IsCMField.complexConj_eq_self_iff] at hx
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 (maximalRealSubfield E))
      (⟨x, hx⟩ : maximalRealSubfield E)
    have e : x = ((a : maximalRealSubfield E) : E) / ((b : maximalRealSubfield E) : E) := by
      have := congrArg (fun z : maximalRealSubfield E => (z : E)) hab
      simp only at this
      rw [← this]
      simp
    rw [e, map_div₀, map_div₀, key a, key b]
  have hne := IsCMField.complexConj_ne_one (K := E)
  obtain ⟨y, hy⟩ : ∃ y, IsCMField.complexConj E y ≠ y := by
    by_contra hc
    push_neg at hc
    exact hne (AlgEquiv.ext hc)
  set δ := y - IsCMField.complexConj E y with hδ
  have hδ0 : δ ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hδc : IsCMField.complexConj E δ = -δ := by
    rw [hδ, map_sub, IsCMField.complexConj_apply_apply]; ring
  have hδ2 : φ j δ ^ 2 = φ i δ ^ 2 := by
    rw [← map_pow, ← map_pow]
    refine (hF _ ?_).symm
    rw [map_pow, hδc]; ring
  have hdec : ∀ x : E, x = ((x + IsCMField.complexConj E x) +
      ((x - IsCMField.complexConj E x) / δ) * δ) / 2 := by
    intro x; field_simp; ring
  have hdec' : ∀ x : E, IsCMField.complexConj E x = ((x + IsCMField.complexConj E x) -
      ((x - IsCMField.complexConj E x) / δ) * δ) / 2 := by
    intro x; field_simp; ring
  have hs : ∀ x, IsCMField.complexConj E (x + IsCMField.complexConj E x) = x + IsCMField.complexConj E x := by
    intro x; rw [map_add, IsCMField.complexConj_apply_apply]; ring
  have ht : ∀ x, IsCMField.complexConj E ((x - IsCMField.complexConj E x) / δ) =
      (x - IsCMField.complexConj E x) / δ := by
    intro x
    rw [map_div₀, map_sub, IsCMField.complexConj_apply_apply, hδc]
    field_simp
    ring
  obtain ⟨k, -, hk⟩ := hφ (φ j)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hδ2 with h1 | h1
  · have hij : φ j = φ i := by
      refine RingHom.ext fun x => ?_
      rw [hdec x]
      have hs' := hs x
      have ht' := ht x
      set s := x + IsCMField.complexConj E x
      set t := (x - IsCMField.complexConj E x) / δ
      simp only [map_div₀, map_add, map_mul, map_ofNat]
      rw [← hF _ hs', ← hF _ ht', h1]
    exact (hk i (Or.inl hij)).trans (hk j (Or.inl rfl)).symm
  · have hij : φ j = ComplexEmbedding.conjugate (φ i) := by
      refine RingHom.ext fun x => ?_
      rw [ComplexEmbedding.conjugate_coe_eq, ← IsCMField.complexEmbedding_complexConj, hdec' x]
      conv_lhs => rw [hdec x]
      have hs' := hs x
      have ht' := ht x
      set s := x + IsCMField.complexConj E x
      set t := (x - IsCMField.complexConj E x) / δ
      simp only [map_div₀, map_add, map_sub, map_mul, map_ofNat]
      rw [← hF _ hs', ← hF _ ht', h1]
      ring
    exact (hk i (Or.inr hij)).trans (hk j (Or.inl rfl)).symm

theorem round_signs (I : Type) [Fintype I] (G : AddSubgroup (I → ℝ))
    (hG : Submodule.span ℝ (G : Set (I → ℝ)) = ⊤) (c : I → ℝ) :
    ∃ g ∈ G, ∀ i, |c i| ≤ c i * g i := by
  classical
  let s : I → ℝ := fun i => if 0 ≤ c i then 1 else -1
  have hs : ∀ i, c i * s i = |c i| := by
    intro i
    by_cases h : 0 ≤ c i
    · simp [s, h, abs_of_nonneg h]
    · simp [s, h, abs_of_neg (lt_of_not_ge h)]
  have hsmem : s ∈ Submodule.span ℝ (G : Set (I → ℝ)) := hG ▸ Submodule.mem_top
  obtain ⟨n, t, g, hsum⟩ := Submodule.mem_span_set'.1 hsmem
  let B : ℝ := ∑ k, ∑ i, |(g k : I → ℝ) i|
  let R : ℝ := B + 1
  let a : I → ℝ := ∑ k, (⌊R * t k⌋) • (g k : I → ℝ)
  have haG : a ∈ G := AddSubgroup.sum_mem _ (fun k _ => AddSubgroup.zsmul_mem _ (g k).2 _)
  refine ⟨a, haG, fun i => ?_⟩
  have hai : a i = ∑ k, (⌊R * t k⌋ : ℝ) * (g k : I → ℝ) i := by
    simp [a, Finset.sum_apply, zsmul_eq_mul]
  have hsi : s i = ∑ k, t k * (g k : I → ℝ) i := by
    rw [← hsum]; simp [Finset.sum_apply, smul_eq_mul]
  set e := a i - R * s i with he
  have he' : e = ∑ k, ((⌊R * t k⌋ : ℝ) - R * t k) * (g k : I → ℝ) i := by
    rw [he, hai, hsi, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have heB : |e| ≤ B := by
    rw [he']
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [abs_mul]
    have h1 : |(⌊R * t k⌋ : ℝ) - R * t k| ≤ 1 := by
      rw [abs_le]
      constructor
      · have := Int.lt_floor_add_one (R * t k); linarith
      · have := Int.floor_le (R * t k); linarith
    have h2 : |(g k : I → ℝ) i| ≤ ∑ j, |(g k : I → ℝ) j| :=
      Finset.single_le_sum (f := fun j => |(g k : I → ℝ) j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    calc |(⌊R * t k⌋ : ℝ) - R * t k| * |(g k : I → ℝ) i| ≤ 1 * |(g k : I → ℝ) i| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ ∑ j, |(g k : I → ℝ) j| := by rw [one_mul]; exact h2
  have hai' : a i = R * s i + e := by rw [he]; ring
  have hce : -(|c i| * B) ≤ c i * e := by
    have h1 : |c i * e| ≤ |c i| * B := by rw [abs_mul]; exact mul_le_mul_of_nonneg_left heB (abs_nonneg _)
    have h2 := neg_abs_le (c i * e)
    linarith
  rw [hai']
  have : c i * (R * s i + e) = R * |c i| + c i * e := by rw [← hs i]; ring
  rw [this]
  have hR : R = B + 1 := rfl
  rw [hR]
  nlinarith [abs_nonneg (c i)]

theorem signs (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) (φ : I → E →+* ℂ)
    (hφ : IsCMType φ) (c : I → ℝ) :
    ∃ a : OF E, ∀ i, |c i| ≤ c i * (φ i (algebraMap (OF E) E a)).re := by
  classical
  have hφinj : Function.Injective φ := by
    intro i j hij
    obtain ⟨k, -, hk⟩ := hφ (φ i)
    exact (hk i (Or.inl rfl)).trans (hk j (Or.inl hij)).symm
  haveI : Finite I := Finite.of_injective φ hφinj
  haveI : Fintype I := Fintype.ofFinite I
  let χ : I → (OF E) →* ℂ := fun i => (φ i).toMonoidHom.comp (algebraMap (OF E) E).toMonoidHom
  have hχ : ∀ i a, χ i a = φ i (algebraMap (OF E) E a) := fun _ _ => rfl
  have hχinj : Function.Injective χ := by
    intro i j hij
    exact cm_restrict_inj E I φ hφ i j (fun a => by rw [← hχ, ← hχ, hij])
  have hli : LinearIndependent ℂ (fun i => (χ i : OF E → ℂ)) :=
    (linearIndependent_monoidHom (OF E) ℂ).comp χ hχinj
  have hreal : ∀ i (a : OF E), ((φ i (algebraMap (OF E) E a)).re : ℂ) = φ i (algebraMap (OF E) E a) := by
    intro i a
    have h1 := IsCMField.complexEmbedding_complexConj (K := E) (φ i) (algebraMap (OF E) E a)
    have h2 : IsCMField.complexConj E (algebraMap (OF E) E a) = algebraMap (OF E) E a :=
      IsCMField.complexConj_apply_eq_self (K := E) (a : maximalRealSubfield E)
    rw [h2] at h1
    exact Complex.conj_eq_iff_re.1 h1.symm
  let Φ : OF E →+ (I → ℝ) :=
    { toFun := fun a i => (φ i (algebraMap (OF E) E a)).re
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hΦ : ∀ a i, Φ a i = (φ i (algebraMap (OF E) E a)).re := fun _ _ => rfl
  have hspan : Submodule.span ℝ ((Φ.range : AddSubgroup (I → ℝ)) : Set (I → ℝ)) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hfle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    let b : I → (I → ℝ) := fun i j => if i = j then 1 else 0
    have hsum : ∀ a : OF E, ∑ i, f (b i) * (φ i (algebraMap (OF E) E a)).re = 0 := by
      intro a
      have hmem : Φ a ∈ Submodule.span ℝ ((Φ.range : AddSubgroup (I → ℝ)) : Set (I → ℝ)) :=
        Submodule.subset_span ⟨a, rfl⟩
      have h1 := hfle hmem
      rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ f] at h1
      rw [← h1]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hΦ, smul_eq_mul, mul_comm]
    have hz := Fintype.linearIndependent_iff.1 hli (fun i => ((f (b i) : ℝ) : ℂ)) (by
      funext a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hχ]
      have : ∑ i, ((f (b i) : ℝ) : ℂ) * φ i (algebraMap (OF E) E a)
          = ((∑ i, f (b i) * (φ i (algebraMap (OF E) E a)).re : ℝ) : ℂ) := by
        push_cast
        exact Finset.sum_congr rfl (fun i _ => by rw [hreal])
      rw [this, hsum a, Complex.ofReal_zero])
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ f, LinearMap.zero_apply]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have := hz i
    simp only [Complex.ofReal_eq_zero] at this
    simp [b, this]
  obtain ⟨g, ⟨a, rfl⟩, hg⟩ := round_signs I Φ.range hspan c
  exact ⟨a, fun i => hg i⟩

theorem exists_signed_generator : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (M : Submodule (OF E) E), IsUnit M →
    (∀ ξ ∈ M, IsCMField.complexConj E ξ = -ξ) → ∀ (I : Type) (φ : I → E →+* ℂ), IsCMType φ → ∀ (e₀ : ℤˣ) (l : ℕ), l.Prime →
    ∃ ξ ∈ M, (∀ i, 0 < ((e₀ : ℤ) : ℝ) * (φ i ξ).im) ∧
      ∀ η ∈ M, ∃ n : ℕ, n.Coprime l ∧ ∃ a : OF E, (n : E) * η = algebraMap (OF E) E a * ξ := by
  intro E _ _ _ M hM hconj I φ hφ e₀ l hl
  have hinj : Function.Injective (algebraMap (OF E) E) := by
    intro x y hxy
    have h1 : ((x : maximalRealSubfield E) : E) = ((y : maximalRealSubfield E) : E) := hxy
    exact RingOfIntegers.ext (Subtype.ext h1)
  have hl0 : (l : OF E) ≠ 0 := by exact_mod_cast hl.ne_zero
  obtain ⟨ξ₀, hξ₀M, hgen₀⟩ := gen_mod (OF E) E hinj M hM (l : OF E) hl0
  have hfg : M.FG := Submodule.fg_of_isUnit hM
  have hM0 : M ≠ ⊥ := by
    intro h0
    obtain ⟨N, hN⟩ := hM.exists_right_inv
    rw [h0, Submodule.bot_mul] at hN
    have h1 : (1 : E) ∈ (1 : Submodule (OF E) E) := Submodule.one_le.1 le_rfl
    rw [← hN, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  have hξ₀ : ξ₀ ≠ 0 := by
    intro h0
    apply hM0
    rw [eq_bot_iff]
    intro η hη
    obtain ⟨n, hn, a, ha⟩ := nakayama_int (OF E) E M hfg l ξ₀ hgen₀ η hη
    rw [h0, mul_zero] at ha
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hl.one_lt.ne' (by simpa using hn)
    rw [Submodule.mem_bot]
    exact (mul_eq_zero.1 ha).resolve_left (by exact_mod_cast hn0)
  have him : ∀ i, (φ i ξ₀).im ≠ 0 := by
    intro i h
    have h1 := IsCMField.complexEmbedding_complexConj (K := E) (φ i) ξ₀
    rw [hconj ξ₀ hξ₀M, map_neg] at h1
    have h2 : conj (φ i ξ₀) = φ i ξ₀ := Complex.conj_eq_iff_im.2 h
    rw [h2] at h1
    have h3 : φ i ξ₀ = 0 := by
      have : (2 : ℂ) * φ i ξ₀ = 0 := by linear_combination -h1
      simpa using this
    exact hξ₀ ((map_eq_zero _).1 h3)
  obtain ⟨a, ha⟩ := signs E I φ hφ (fun i => ((e₀ : ℤ) : ℝ) * (φ i ξ₀).im)
  have hreal : ∀ i, (φ i (algebraMap (OF E) E a)).im = 0 := by
    intro i
    have h1 := IsCMField.complexEmbedding_complexConj (K := E) (φ i) (algebraMap (OF E) E a)
    have h2 : IsCMField.complexConj E (algebraMap (OF E) E a) = algebraMap (OF E) E a :=
      IsCMField.complexConj_apply_eq_self (K := E) (a : maximalRealSubfield E)
    rw [h2] at h1
    exact Complex.conj_eq_iff_im.1 h1.symm
  set ξ := algebraMap (OF E) E (1 + (l : OF E) * a) * ξ₀ with hξdef
  have hξM : ξ ∈ M := by
    rw [hξdef, ← Algebra.smul_def]; exact M.smul_mem _ hξ₀M
  refine ⟨ξ, hξM, ?_, ?_⟩
  · intro i
    have he : ((e₀ : ℤ) : ℝ) = 1 ∨ ((e₀ : ℤ) : ℝ) = -1 := by
      rcases Int.units_eq_one_or e₀ with h | h <;> simp [h]
    have hc := ha i
    have hx := hreal i
    have hφξ : φ i ξ = (1 + (l : ℂ) * φ i (algebraMap (OF E) E a)) * φ i ξ₀ := by
      rw [hξdef]; simp [map_mul, map_add, map_one, map_natCast]
    rw [hφξ, Complex.mul_im]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.add_im, Complex.one_im, Complex.mul_im, hx, mul_zero, sub_zero, zero_mul, add_zero, zero_add]
    have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
    have hc0 : 0 < |((e₀ : ℤ) : ℝ) * (φ i ξ₀).im| := by
      rcases he with h | h <;> rw [h] <;> simpa using him i
    set x := (φ i (algebraMap (OF E) E a)).re
    set c := ((e₀ : ℤ) : ℝ) * (φ i ξ₀).im
    have hc' : c * (1 + l * x) = c + l * (c * x) := by ring
    have key : 0 < c * (1 + l * x) := by
      rw [hc']
      have : -|c| ≤ c := neg_abs_le c
      nlinarith
    have : ((e₀ : ℤ) : ℝ) * ((1 + l * x) * (φ i ξ₀).im) = c * (1 + l * x) := by ring
    linarith
  · apply nakayama_int (OF E) E M hfg l ξ
    have hsub : Submodule.span (OF E) {ξ₀} ≤ Submodule.span (OF E) {ξ} ⊔ Ideal.span {(l : OF E)} • M := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      have hm : (l : OF E) • (a • ξ₀) ∈ Ideal.span {(l : OF E)} • M :=
        Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (M.smul_mem a hξ₀M)
      have heq : ξ₀ = ξ + -((l : OF E) • (a • ξ₀)) := by
        rw [hξdef, Algebra.smul_def, Algebra.smul_def]; simp [map_add, map_mul]; ring
      rw [heq]
      exact Submodule.add_mem_sup (Submodule.mem_span_singleton_self ξ) (Submodule.neg_mem _ hm)
    exact hgen₀.trans (sup_le hsub le_sup_right)

end GlobalTheory.SignGen
