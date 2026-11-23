import Mathlib
import GroundTheory.GlobalFields.TateThesis.PrimeSumBounded
import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass
import GroundTheory.GlobalFields.TateThesis.DegreeOneDensity

open NumberField IsDedekindDomain Topology Filter Set

namespace GroundTheory.Global

open IdeleGroup

noncomputable section

section FiniteCharacters

variable {A : Type*} [AddCommGroup A] [Finite A]

theorem norm_addChar_apply (φ : AddChar A ℂ) (a : A) : ‖φ a‖ = 1 := by
  have h : φ a ^ Nat.card A = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero', AddChar.map_zero_eq_one]
  have h2 : ‖φ a‖ ^ Nat.card A = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Nat.card_pos.ne').1 h2

theorem eq_of_forall_addChar_eq {a b : A} (h : ∀ φ : AddChar A ℂ, φ a = φ b) : a = b := by
  rw [← sub_eq_zero, ← AddChar.forall_apply_eq_zero]
  intro φ
  have hb : φ b ≠ 0 := fun h0 ↦ by
    have := norm_addChar_apply φ b
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  rw [AddChar.map_sub_eq_div, h φ, div_self hb]

variable {G : Type*} [CommGroup G] [Finite G]

def circleChar (φ : AddChar (Additive G) ℂ) : G →* Circle where
  toFun g := ⟨φ (Additive.ofMul g), mem_sphere_zero_iff_norm.2 (norm_addChar_apply φ _)⟩
  map_one' := Circle.ext (by simp)
  map_mul' g h := Circle.ext (by
    change φ (Additive.ofMul (g * h)) = φ (Additive.ofMul g) * φ (Additive.ofMul h)
    rw [ofMul_mul, AddChar.map_add_eq_mul])

theorem coe_circleChar (φ : AddChar (Additive G) ℂ) (g : G) :
    (circleChar φ g : ℂ) = φ (Additive.ofMul g) :=
  rfl

end FiniteCharacters

variable {K : Type*} [Field K] [NumberField K]

namespace HeckeCharacter

variable {G : Type*} [Group G]

def ofHom (q : IdeleGroup K →* G) (hq : IsOpen (q.ker : Set (IdeleGroup K)))
    (hK : (IdeleGroup.diagonal K).range ≤ q.ker) (ψ : G →* Circle) : HeckeCharacter K where
  toMonoidHom := QuotientGroup.lift (IdeleGroup.diagonal K).range (ψ.comp q) fun x hx ↦ by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, (MonoidHom.mem_ker.1 (hK hx)), map_one]
  continuous_toFun := by
    have : DiscreteTopology (IdeleGroup K ⧸ q.ker) := QuotientGroup.discreteTopology hq
    refine (QuotientGroup.isQuotientMap_mk (IdeleGroup.diagonal K).range).continuous_iff.2 ?_
    have hc : Continuous fun y : IdeleGroup K ⧸ q.ker ↦ ψ (QuotientGroup.kerLift q y) :=
      continuous_of_discreteTopology
    exact hc.comp (QuotientGroup.continuous_mk (N := q.ker))

theorem ofHom_toIdele (q : IdeleGroup K →* G) (hq : IsOpen (q.ker : Set (IdeleGroup K)))
    (hK : (IdeleGroup.diagonal K).range ≤ q.ker) (ψ : G →* Circle) (x : IdeleGroup K) :
    (ofHom q hq hK ψ).toIdele x = ψ (q x) :=
  rfl

end HeckeCharacter

def uniformizerClass {G : Type*} [Group G] (q : IdeleGroup K →* G) (v : HeightOneSpectrum (𝓞 K)) :
    G :=
  q (finiteEmbedding v (exists_uniformizer v).choose)

theorem hasDirichletDensity_of_isBoundedUnder_abs_sub {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (h : IsBoundedUnder (· ≤ ·) (𝓝[>] 1) fun s ↦
      |S.primeIdealZetaSum s - δ * (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s|) :
    S.HasDirichletDensity δ := by
  have hZ := tendsto_primeIdealZetaSum_univ_atTop K
  have h0 : Tendsto (fun s ↦ ((univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s)⁻¹ *
      (S.primeIdealZetaSum s - δ * (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s))
      (𝓝[>] 1) (𝓝 0) :=
    hZ.inv_tendsto_atTop.zero_mul_isBoundedUnder_le
      (by simpa only [Function.comp_def, Real.norm_eq_abs] using h)
  have h1 := h0.const_add δ
  rw [add_zero] at h1
  unfold Set.HasDirichletDensity
  refine h1.congr' ?_
  filter_upwards [hZ.eventually_gt_atTop 0] with s hs
  field_simp
  ring

section Density

variable {G : Type*} [CommGroup G] [Finite G] (q : IdeleGroup K →* G)
  (hq : IsOpen (q.ker : Set (IdeleGroup K))) (hK : (IdeleGroup.diagonal K).range ≤ q.ker)

include hq hK

def classChar (φ : AddChar (Additive G) ℂ) : HeckeCharacter K :=
  HeckeCharacter.ofHom q hq hK (circleChar φ)

theorem classChar_toIdele (φ : AddChar (Additive G) ℂ) (x : IdeleGroup K) :
    ((classChar q hq hK φ).toIdele x : ℂ) = φ (Additive.ofMul (q x)) :=
  rfl

def ramifiedPrimes : Set (HeightOneSpectrum (𝓞 K)) :=
  {v | ∃ φ : AddChar (Additive G) ℂ, v.asIdeal ∣ (classChar q hq hK φ).conductor}

theorem finite_ramifiedPrimes : (ramifiedPrimes q hq hK).Finite := by
  have h : ramifiedPrimes q hq hK = ⋃ φ : AddChar (Additive G) ℂ,
      {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ (classChar q hq hK φ).conductor} := by
    ext v
    simp only [ramifiedPrimes, mem_iUnion, mem_ofPred_eq]
  rw [h]
  exact finite_iUnion fun φ ↦ Ideal.finite_factors (classChar q hq hK φ).conductor_ne_bot

theorem coeff_classChar {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ ramifiedPrimes q hq hK)
    (φ : AddChar (Additive G) ℂ) :
    (classChar q hq hK φ).coeff v.asIdeal = φ (Additive.ofMul (uniformizerClass q v)) := by
  have hv' : ¬ v.asIdeal ∣ (classChar q hq hK φ).conductor := fun h ↦ hv ⟨φ, h⟩
  rw [(classChar q hq hK φ).coeff_asIdeal_eq_toIdele hv' (exists_uniformizer v).choose_spec,
    classChar_toIdele]
  rfl

theorem map_finiteEmbedding_eq_uniformizerClass {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ ramifiedPrimes q hq hK) {π : (v.adicCompletion K)ˣ}
    (hπ : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    q (finiteEmbedding v π) = uniformizerClass q v := by
  refine Additive.ofMul.injective (eq_of_forall_addChar_eq fun φ ↦ ?_)
  have hv' : ¬ v.asIdeal ∣ (classChar q hq hK φ).conductor := fun h ↦ hv ⟨φ, h⟩
  have h := (classChar q hq hK φ).localComponent_uniformizer_eq hv' hπ
    (exists_uniformizer v).choose_spec
  rw [HeckeCharacter.localComponent_apply, HeckeCharacter.localComponent_apply] at h
  exact congrArg (fun z : Circle ↦ (z : ℂ)) h

theorem classChar_pow_card (φ : AddChar (Additive G) ℂ) :
    classChar q hq hK φ ^ Nat.card G = 1 := by
  refine ContinuousMonoidHom.ext fun c ↦ ?_
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective K c
  have h := (classChar q hq hK φ).pow_toIdele (Nat.card G) x
  rw [HeckeCharacter.toIdele_apply] at h
  have h2 : (classChar q hq hK φ).toIdele x ^ Nat.card G = 1 := by
    rw [show (classChar q hq hK φ).toIdele x = circleChar φ (q x) from rfl, ← map_pow,
      pow_card_eq_one', map_one]
  rw [h, h2]
  rfl

theorem classChar_ne_one (hqs : Function.Surjective q) {φ : AddChar (Additive G) ℂ} (hφ : φ ≠ 0) :
    classChar q hq hK φ ≠ 1 := by
  obtain ⟨a, ha⟩ := AddChar.ne_zero_iff.1 hφ
  obtain ⟨x, hx⟩ := hqs (Additive.toMul a)
  intro h1
  apply ha
  have h := classChar_toIdele q hq hK φ x
  rw [HeckeCharacter.toIdele_apply, h1, hx, ofMul_toMul] at h
  rw [← h]
  rfl

def goodTerm (φ : AddChar (Additive G) ℂ) (s : ℝ) (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  (ramifiedPrimes q hq hK)ᶜ.indicator (fun v ↦ (classChar q hq hK φ).coeffTerm (s : ℂ) v.asIdeal) v

theorem summable_goodTerm (φ : AddChar (Additive G) ℂ) {s : ℝ} (hs : 1 < s) :
    Summable (goodTerm q hq hK φ s) :=
  (Summable.of_norm ((classChar q hq hK φ).summable_norm_coeffTerm_asIdeal hs)).indicator _

theorem card_mul_primeIdealZetaSum_uniformizerClass_eq (c : G) {s : ℝ} (hs : 1 < s) :
    (Nat.card G : ℂ) *
      (({v | v ∉ ramifiedPrimes q hq hK ∧ uniformizerClass q v = c} : Set _).primeIdealZetaSum s :
        ℂ) =
      ∑ φ : AddChar (Additive G) ℂ, φ (-Additive.ofMul c) * ∑' v, goodTerm q hq hK φ s v := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set S := {v | v ∉ ramifiedPrimes q hq hK ∧ uniformizerClass q v = c}
  rw [Set.primeIdealZetaSum_def,
    tsum_subtype S (fun v : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm v.asIdeal : ℝ) ^ (-s)),
    Complex.ofReal_tsum, ← tsum_mul_left]
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum fun φ _ ↦ (summable_goodTerm q hq hK φ hs).mul_left _]
  refine tsum_congr fun v ↦ ?_
  by_cases hv : v ∈ ramifiedPrimes q hq hK
  · have h1 : v ∉ S := fun h ↦ h.1 hv
    have h2 : ∀ φ, goodTerm q hq hK φ s v = 0 := fun φ ↦
      indicator_of_notMem (not_not.2 hv) _
    simp [indicator_of_notMem h1, h2]
  · have hN : (0 : ℝ) ≤ Ideal.absNorm v.asIdeal := Nat.cast_nonneg _
    have h2 : ∀ φ : AddChar (Additive G) ℂ, φ (-Additive.ofMul c) * goodTerm q hq hK φ s v =
        φ (Additive.ofMul (uniformizerClass q v) - Additive.ofMul c) *
          ((Ideal.absNorm v.asIdeal : ℂ) ^ (s : ℂ))⁻¹ := fun φ ↦ by
      rw [goodTerm, indicator_of_mem (show v ∈ (ramifiedPrimes q hq hK)ᶜ from hv),
        HeckeCharacter.coeffTerm_apply, coeff_classChar q hq hK hv, sub_eq_add_neg,
        AddChar.map_add_eq_mul, div_eq_mul_inv]
      ring
    simp_rw [h2]
    rw [← Finset.sum_mul, AddChar.sum_apply_eq_ite]
    simp only [sub_eq_zero, EmbeddingLike.apply_eq_iff_eq]
    have hcard : (Fintype.card (Additive G) : ℂ) = Nat.card G := by
      rw [Nat.card_eq_fintype_card, Fintype.card_congr (Additive.ofMul (α := G))]
    have hpow : (((Ideal.absNorm v.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) =
        ((Ideal.absNorm v.asIdeal : ℂ) ^ (s : ℂ))⁻¹ := by
      rw [Complex.ofReal_cpow hN, Complex.ofReal_neg, Complex.cpow_neg, Complex.ofReal_natCast]
    by_cases hc : uniformizerClass q v = c
    · rw [indicator_of_mem (show v ∈ S from ⟨hv, hc⟩), if_pos hc, hcard, hpow]
    · rw [indicator_of_notMem (show v ∉ S from fun h ↦ hc h.2), if_neg hc]
      simp

theorem exists_norm_tsum_goodTerm_le (hqs : Function.Surjective q) {φ : AddChar (Additive G) ℂ}
    (hφ : φ ≠ 0) :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ), ‖∑' v, goodTerm q hq hK φ s v‖ ≤ C := by
  obtain ⟨C, hC⟩ := (classChar q hq hK φ).isBoundedUnder_norm_primeSum_of_pow_eq_one
    Nat.card_pos.ne' (classChar_pow_card q hq hK φ) (classChar_ne_one q hq hK hqs hφ)
  have hC' : ∀ᶠ s in 𝓝[>] (1 : ℝ), ‖(classChar q hq hK φ).primeSum s‖ ≤ C := eventually_map.mp hC
  have hR := finite_ramifiedPrimes q hq hK
  refine ⟨C + hR.toFinset.card, ?_⟩
  filter_upwards [hC', self_mem_nhdsWithin] with s hs hs1
  have hs1' : (1 : ℝ) < s := hs1
  set f : HeightOneSpectrum (𝓞 K) → ℂ := fun v ↦ (classChar q hq hK φ).coeffTerm (s : ℂ) v.asIdeal
  have hf : Summable f := Summable.of_norm ((classChar q hq hK φ).summable_norm_coeffTerm_asIdeal hs1')
  have hsplit : ∑' v, goodTerm q hq hK φ s v =
      (classChar q hq hK φ).primeSum s - ∑' v, (ramifiedPrimes q hq hK).indicator f v := by
    rw [HeckeCharacter.primeSum, eq_sub_iff_add_eq]
    have e : ∀ v, goodTerm q hq hK φ s v = (ramifiedPrimes q hq hK)ᶜ.indicator f v := fun v ↦ rfl
    simp_rw [e]
    rw [← (hf.indicator _).tsum_add (hf.indicator _)]
    exact tsum_congr fun v ↦ congrFun (indicator_compl_add_self (ramifiedPrimes q hq hK) f) v
  have hfin : ∑' v, (ramifiedPrimes q hq hK).indicator f v =
      ∑ v ∈ hR.toFinset, (ramifiedPrimes q hq hK).indicator f v :=
    tsum_eq_sum fun v hv ↦ indicator_of_notMem (by simpa using hv) _
  have hbd : ‖∑ v ∈ hR.toFinset, (ramifiedPrimes q hq hK).indicator f v‖ ≤ hR.toFinset.card := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ v ∈ hR.toFinset, ‖(ramifiedPrimes q hq hK).indicator f v‖
        ≤ ∑ _v ∈ hR.toFinset, (1 : ℝ) := by
          refine Finset.sum_le_sum fun v _ ↦ ?_
          rw [norm_indicator_eq_indicator_norm]
          refine (indicator_le_self' fun _ _ ↦ norm_nonneg _ ) v |>.trans ?_
          exact ((classChar q hq hK φ).norm_coeffTerm_asIdeal_le_half hs1'.le v).trans
            (by norm_num)
      _ = hR.toFinset.card := by simp
  rw [hsplit, hfin]
  exact (norm_sub_le _ _).trans (add_le_add hs hbd)

theorem isBoundedUnder_abs_sub_uniformizerClass (hqs : Function.Surjective q) (c : G) :
    IsBoundedUnder (· ≤ ·) (𝓝[>] 1) fun s ↦
      |({v | v ∉ ramifiedPrimes q hq hK ∧ uniformizerClass q v = c} : Set _).primeIdealZetaSum s -
        1 / Nat.card G * (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s| := by
  classical
  set R := ramifiedPrimes q hq hK
  have hR := finite_ramifiedPrimes q hq hK
  have hb : ∀ φ : AddChar (Additive G) ℂ, ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      φ ≠ 0 → ‖∑' v, goodTerm q hq hK φ s v‖ ≤ C := by
    intro φ
    by_cases hφ : φ = 0
    · exact ⟨0, Eventually.of_forall fun _ h ↦ absurd hφ h⟩
    · obtain ⟨C, hC⟩ := exists_norm_tsum_goodTerm_le q hq hK hqs hφ
      exact ⟨C, hC.mono fun _ h _ ↦ h⟩
  choose C hC using hb
  have hall : ∀ᶠ s in 𝓝[>] (1 : ℝ), ∀ φ : AddChar (Additive G) ℂ,
      φ ≠ 0 → ‖∑' v, goodTerm q hq hK φ s v‖ ≤ C φ :=
    eventually_all.2 hC
  set B := ∑ φ ∈ Finset.univ.erase (0 : AddChar (Additive G) ℂ), C φ
  have hG : (0 : ℝ) < Nat.card G := Nat.cast_pos.2 Nat.card_pos
  refine isBoundedUnder_of_eventually_le (a := (B + R.ncard) / Nat.card G) ?_
  filter_upwards [hall, self_mem_nhdsWithin] with s hs hs1
  have hs1' : (1 : ℝ) < s := hs1
  set Q := ({v | v ∉ R ∧ uniformizerClass q v = c} : Set _).primeIdealZetaSum s
  set Z := (univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s

  have h0 : ∑' v, goodTerm q hq hK 0 s v = ((Rᶜ.primeIdealZetaSum s : ℝ) : ℂ) := by
    rw [Set.primeIdealZetaSum_def,
      tsum_subtype Rᶜ (fun v : HeightOneSpectrum (𝓞 K) ↦ (Ideal.absNorm v.asIdeal : ℝ) ^ (-s)),
      Complex.ofReal_tsum]
    refine tsum_congr fun v ↦ ?_
    by_cases hv : v ∈ R
    · rw [goodTerm, indicator_of_notMem (not_not.2 hv), indicator_of_notMem (not_not.2 hv),
        Complex.ofReal_zero]
    · rw [goodTerm, indicator_of_mem (show v ∈ Rᶜ from hv), indicator_of_mem (show v ∈ Rᶜ from hv),
        HeckeCharacter.coeffTerm_apply, coeff_classChar q hq hK hv, AddChar.zero_apply,
        Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg, Complex.cpow_neg,
        Complex.ofReal_natCast, one_div]
  have hid := card_mul_primeIdealZetaSum_uniformizerClass_eq q hq hK c hs1'
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 0), AddChar.zero_apply, one_mul, h0] at hid

  have hcmp : |Nat.card G * Q - Rᶜ.primeIdealZetaSum s| ≤ B := by
    have e : (((Nat.card G * Q - Rᶜ.primeIdealZetaSum s : ℝ)) : ℂ) =
        ∑ φ ∈ Finset.univ.erase (0 : AddChar (Additive G) ℂ),
          φ (-Additive.ofMul c) * ∑' v, goodTerm q hq hK φ s v := by
      push_cast
      rw [hid]
      ring
    rw [← Real.norm_eq_abs, ← Complex.norm_real, e]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun φ hφ ↦ ?_)
    rw [norm_mul, norm_addChar_apply, one_mul]
    exact hs φ (Finset.ne_of_mem_erase hφ)
  have hunion : Z = R.primeIdealZetaSum s + Rᶜ.primeIdealZetaSum s := by
    rw [← primeIdealZetaSum_union disjoint_compl_right hs1', union_compl_self]
  have hR0 := R.primeIdealZetaSum_nonneg s
  have hR1 := Set.primeIdealZetaSum_le_card_of_finite hR (by linarith : (0 : ℝ) ≤ s)
  have key : |Nat.card G * Q - Z| ≤ B + R.ncard := by
    rw [hunion]
    calc |(Nat.card G : ℝ) * Q - (R.primeIdealZetaSum s + Rᶜ.primeIdealZetaSum s)|
        = |((Nat.card G : ℝ) * Q - Rᶜ.primeIdealZetaSum s) - R.primeIdealZetaSum s| := by
          ring_nf
      _ ≤ |(Nat.card G : ℝ) * Q - Rᶜ.primeIdealZetaSum s| + |R.primeIdealZetaSum s| :=
          abs_sub _ _
      _ ≤ B + R.ncard := add_le_add hcmp (by rw [abs_of_nonneg hR0]; exact hR1)
  have e2 : Q - 1 / Nat.card G * Z = (Nat.card G * Q - Z) / Nat.card G := by
    field_simp
  rw [e2, abs_div, abs_of_pos hG]
  exact div_le_div_of_nonneg_right key hG.le

theorem hasDirichletDensity_setOf_map_eq (hqs : Function.Surjective q) (c : G) :
    {v : HeightOneSpectrum (𝓞 K) | ∀ π : (v.adicCompletion K)ˣ,
      Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) →
        q (finiteEmbedding v π) = c}.HasDirichletDensity (1 / Nat.card G) := by
  have hR := finite_ramifiedPrimes q hq hK
  have hT : ({v | v ∉ ramifiedPrimes q hq hK ∧ uniformizerClass q v = c} : Set _).HasDirichletDensity
      (1 / Nat.card G) :=
    hasDirichletDensity_of_isBoundedUnder_abs_sub (isBoundedUnder_abs_sub_uniformizerClass q hq hK hqs c)
  have hsub : ({v | v ∉ ramifiedPrimes q hq hK ∧ uniformizerClass q v = c} : Set _) ⊆
      {v : HeightOneSpectrum (𝓞 K) | ∀ π : (v.adicCompletion K)ˣ,
        Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) → q (finiteEmbedding v π) = c} :=
    fun v hv π hπ ↦ (map_finiteEmbedding_eq_uniformizerClass q hq hK hv.1 hπ).trans hv.2
  have hdiff : {v : HeightOneSpectrum (𝓞 K) | ∀ π : (v.adicCompletion K)ˣ,
        Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) → q (finiteEmbedding v π) = c} \
      {v | v ∉ ramifiedPrimes q hq hK ∧ uniformizerClass q v = c} ⊆ ramifiedPrimes q hq hK := by
    intro v hv
    by_contra hvR
    exact hv.2 ⟨hvR, hv.1 _ (exists_uniformizer v).choose_spec⟩
  exact (hasDirichletDensity_iff_of_subset_of_isBoundedUnder hsub
    (isBoundedUnder_primeIdealZetaSum_of_finite (hR.subset hdiff)) _).1 hT

end Density

theorem hasDirichletDensity_setOf_mk_eq {H : Subgroup (IdeleGroup K)}
    (hH : IsOpen (H : Set (IdeleGroup K))) (hK : (IdeleGroup.diagonal K).range ≤ H) [H.FiniteIndex]
    (c : IdeleGroup K ⧸ H) :
    {v : HeightOneSpectrum (𝓞 K) | ∀ π : (v.adicCompletion K)ˣ,
      Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) →
        ((finiteEmbedding v π : IdeleGroup K) : IdeleGroup K ⧸ H) = c}.HasDirichletDensity
      (1 / Nat.card (IdeleGroup K ⧸ H)) := by
  have : Finite (IdeleGroup K ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  let _ : CommGroup (IdeleGroup K ⧸ H) := QuotientGroup.Quotient.commGroup H
  let q : IdeleGroup K →* IdeleGroup K ⧸ H :=
    { toFun := fun x ↦ (x : IdeleGroup K ⧸ H)
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hker : q.ker = H := by
    ext x
    exact QuotientGroup.eq_one_iff x
  have hH' : IsOpen (q.ker : Set (IdeleGroup K)) := by rw [hker]; exact hH
  have hK' : (IdeleGroup.diagonal K).range ≤ q.ker := by rw [hker]; exact hK
  exact hasDirichletDensity_setOf_map_eq q hH' hK' QuotientGroup.mk_surjective c

end

end GroundTheory.Global
