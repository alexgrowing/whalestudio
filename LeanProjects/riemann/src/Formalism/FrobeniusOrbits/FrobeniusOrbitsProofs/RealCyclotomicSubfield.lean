import Mathlib
import Formalism.FrobeniusOrbits.Statement

open NumberField IntermediateField Polynomial

noncomputable section

namespace Formalism.FrobeniusOrbits

open Formalism.TwoAdicCyclotomicDecomposition

namespace RealCyclotomicSubfield

lemma conj_root {z : ℂ} {m : ℕ} (hm : m ≠ 0) (hz : z ^ m = 1) : starRingEnd ℂ z = z⁻¹ := by
  have hn : ‖z‖ = 1 := by
    have h1 := congrArg norm hz
    rw [norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hm).mp h1
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
  simp

lemma real_theta {K : Type*} [Field K] {m : ℕ} (hm : m ≠ 0) {ζ : K} (hζ : IsPrimitiveRoot ζ m)
    (ψ : K →+* ℂ) : starRingEnd ℂ (ψ (ζ + ζ⁻¹)) = ψ (ζ + ζ⁻¹) := by
  have h1 : (ψ ζ) ^ m = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hc := conj_root hm h1
  simp only [map_add, map_inv₀]
  rw [hc, inv_inv, add_comm]

lemma not_real_zeta {K : Type*} [Field K] {m : ℕ} (hm : m ≠ 0) (h2 : ¬ m ∣ 2) {ζ : K}
    (hζ : IsPrimitiveRoot ζ m) (ψ : K →+* ℂ) : starRingEnd ℂ (ψ ζ) ≠ ψ ζ := by
  intro h
  have h1 : (ψ ζ) ^ m = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  have hc := conj_root hm h1
  have hne : ψ ζ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hm] at h1
    exact zero_ne_one h1
  have heq : ψ ζ = (ψ ζ)⁻¹ := h.symm.trans hc
  have hsq : ψ (ζ ^ 2) = ψ 1 := by
    rw [map_pow, map_one, sq]
    calc ψ ζ * ψ ζ = ψ ζ * (ψ ζ)⁻¹ := congrArg (ψ ζ * ·) heq
      _ = 1 := mul_inv_cancel₀ hne
  exact h2 (hζ.dvd_of_pow_eq_one 2 (ψ.injective hsq))

lemma real_on_adjoin {K : Type*} [Field K] [Algebra ℚ K] (t : K) (φ : K →+* ℂ)
    (ht : starRingEnd ℂ (φ t) = φ t) : ∀ x ∈ ℚ⟮t⟯, starRingEnd ℂ (φ x) = φ x := by
  intro x hx
  have key : Subfield.closure (Set.range (algebraMap ℚ K) ∪ {t}) ≤
      ((starRingEnd ℂ).comp φ).eqLocusField φ := by
    rw [Subfield.closure_le]
    rintro y (⟨q, rfl⟩ | hy)
    · show (starRingEnd ℂ) (φ (algebraMap ℚ K q)) = φ (algebraMap ℚ K q)
      simp only [RingHom.map_rat_algebraMap]
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ht
  exact key hx

lemma fix_on_adjoin {L : Type*} [Field L] [Algebra ℚ L] {E : IntermediateField ℚ L}
    (σ : E ≃ₐ[ℚ] E) {t : L} (hle : ℚ⟮t⟯ ≤ E)
    (hσ : ((σ ⟨t, hle (mem_adjoin_simple_self ℚ t)⟩ : E) : L) = t) :
    ∀ x : E, (x : L) ∈ ℚ⟮t⟯ → σ x = x := by
  intro x hx
  have key : Subfield.closure (Set.range (algebraMap ℚ L) ∪ {t}) ≤
      (((σ : E →+* E).eqLocusField (RingHom.id E)).map (E.val : E →+* L)) := by
    rw [Subfield.closure_le]
    rintro y (⟨q, rfl⟩ | hy)
    · refine Subfield.mem_map.mpr ⟨(q : E), ?_, ?_⟩
      · show σ (q : E) = (q : E)
        exact map_ratCast σ q
      · rw [eq_ratCast (algebraMap ℚ L) q]
        exact map_ratCast (E.val : E →+* L) q
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      refine Subfield.mem_map.mpr ⟨⟨y, hle (mem_adjoin_simple_self ℚ y)⟩, ?_, rfl⟩
      show σ _ = _
      exact Subtype.ext hσ
  obtain ⟨y, hy, hyx⟩ := Subfield.mem_map.mp (key hx)
  have hyx' : y = x := Subtype.ext hyx
  subst hyx'
  exact hy

variable {L : Type} [Field L] [NumberField L]

lemma two_pow_not_dvd (e : ℕ) : ¬ (2 ^ (e + 2)) ∣ 2 := by
  intro h
  have h1 := Nat.le_of_dvd (by norm_num) h
  have h2 : 2 ^ 2 ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

lemma real_subfield_real_embeddings {e : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (e + 2))) :
    ∀ x ∈ F1 ζ, ∀ φ : L →+* ℂ, starRingEnd ℂ (φ x) = φ x := by
  intro x hx φ
  exact real_on_adjoin (ζ + ζ⁻¹) φ (real_theta (by positivity) hζ φ) x hx

lemma zeta_not_mem {e : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (e + 2))) : ζ ∉ F1 ζ := by
  intro h
  let φ : L →+* ℂ := (IsAlgClosed.lift : L →ₐ[ℚ] ℂ).toRingHom
  exact not_real_zeta (by positivity) (two_pow_not_dvd e) hζ φ (real_subfield_real_embeddings hζ ζ h φ)

lemma theta_mem_adj (ζ : L) : ζ + ζ⁻¹ ∈ ℚ⟮ζ⟯ := by
  exact add_mem (mem_adjoin_simple_self ℚ ζ) (inv_mem (mem_adjoin_simple_self ℚ ζ))

lemma attached_subfield_le_adjoin_simple (ζ : L) : F1 ζ ≤ ℚ⟮ζ⟯ := by
  exact adjoin_simple_le_iff.mpr (theta_mem_adj ζ)

lemma finrank_cyc {e : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (e + 2))) :
    Module.finrank ℚ ℚ⟮ζ⟯ = 2 ^ (e + 1) := by
  have hint : IsIntegral ℚ ζ := Algebra.IsIntegral.isIntegral ζ
  rw [IntermediateField.adjoin.finrank hint, ← Polynomial.cyclotomic_eq_minpoly_rat hζ (by positivity),
    Polynomial.natDegree_cyclotomic, Nat.totient_prime_pow Nat.prime_two (by omega)]
  have h3 : e + 2 - 1 = e + 1 := by omega
  rw [h3]
  simp

private lemma mem_adjoin_of_val_mem_adjoin_image {L' : Type*} [Field L'] [CharZero L'] (Z : IntermediateField ℚ L')
    (S : Set Z) (x : Z) (hx : (x : L') ∈ adjoin ℚ (Z.val '' S)) : x ∈ adjoin ℚ S := by
  rw [← IntermediateField.adjoin_map] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : y = x := Subtype.ext hyx
  subst hyx'
  exact hy

private lemma finrank_adjoin_add_inv_eq_two_of_isPrimitiveRoot {M : Type*} [Field M] [CharZero M] [FiniteDimensional ℚ M]
    {m : ℕ} (hm : m ≠ 0) (h2 : ¬ m ∣ 2) {z : M} (hz : IsPrimitiveRoot z m) (htop : ℚ⟮z⟯ = ⊤) :
    Module.finrank ℚ⟮z + z⁻¹⟯ M = 2 := by
  have hzK : z ∉ ℚ⟮z + z⁻¹⟯ := by
    intro hz'
    let φ : M →+* ℂ := (IsAlgClosed.lift : M →ₐ[ℚ] ℂ).toRingHom
    exact not_real_zeta hm h2 hz φ (real_on_adjoin _ φ (real_theta hm hz φ) z hz')
  have htop' : adjoin ℚ⟮z + z⁻¹⟯ ({z} : Set M) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ ℚ⟮z⟯ := htop ▸ IntermediateField.mem_top
    have key : Subfield.closure (Set.range (algebraMap ℚ M) ∪ {z}) ≤
        (adjoin ℚ⟮z + z⁻¹⟯ ({z} : Set M)).toSubfield := by
      rw [Subfield.closure_le]
      rintro y (⟨q, rfl⟩ | hy)
      · rw [eq_ratCast (algebraMap ℚ M) q]
        exact SubfieldClass.ratCast_mem _ q
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact mem_adjoin_simple_self _ y
    exact key hx
  have hint : IsIntegral ℚ⟮z + z⁻¹⟯ z := IsIntegral.tower_top (Algebra.IsIntegral.isIntegral (R := ℚ) z)
  rw [← IntermediateField.finrank_top', ← htop', IntermediateField.adjoin.finrank hint]
  apply le_antisymm
  · let θK : ℚ⟮z + z⁻¹⟯ := ⟨z + z⁻¹, mem_adjoin_simple_self ℚ _⟩
    have hmon : (X ^ 2 - C θK * X + 1 : (ℚ⟮z + z⁻¹⟯)[X]).Monic := by monicity!
    have hdeg : (X ^ 2 - C θK * X + 1 : (ℚ⟮z + z⁻¹⟯)[X]).natDegree = 2 := by compute_degree!
    have hroot : aeval z (X ^ 2 - C θK * X + 1 : (ℚ⟮z + z⁻¹⟯)[X]) = 0 := by
      have hz0 : z ≠ 0 := hz.ne_zero hm
      simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_one]
      show z ^ 2 - (z + z⁻¹) * z + 1 = 0
      rw [add_mul, inv_mul_cancel₀ hz0]
      ring
    rw [← hdeg]
    exact natDegree_le_natDegree (minpoly.min _ z hmon hroot)
  · by_contra hlt
    push_neg at hlt
    have hpos := minpoly.natDegree_pos hint
    have h1 : (minpoly ℚ⟮z + z⁻¹⟯ z).natDegree = 1 := by omega
    obtain ⟨k, hk⟩ := minpoly.natDegree_eq_one_iff.mp h1
    have hk' : (k : M) = z := hk
    exact hzK ((congrArg (fun w => w ∈ ℚ⟮z + z⁻¹⟯) hk').mp k.2)

lemma finrank_real_subfield {e : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (e + 2))) :
    Module.finrank ℚ (F1 ζ) = 2 ^ e := by
  have hint : IsIntegral ℚ ζ := Algebra.IsIntegral.isIntegral ζ
  haveI : FiniteDimensional ℚ ℚ⟮ζ⟯ := adjoin.finiteDimensional hint
  let z : ℚ⟮ζ⟯ := AdjoinSimple.gen ℚ ζ
  have hz : IsPrimitiveRoot z (2 ^ (e + 2)) :=
    (show IsPrimitiveRoot ((ℚ⟮ζ⟯).val z) (2 ^ (e + 2)) from hζ).of_map_of_injective Subtype.val_injective
  have htop : ℚ⟮z⟯ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    apply mem_adjoin_of_val_mem_adjoin_image
    rw [Set.image_singleton]
    exact x.2
  have h2 := finrank_adjoin_add_inv_eq_two_of_isPrimitiveRoot (by positivity) (two_pow_not_dvd e) hz htop
  have hmul := Module.finrank_mul_finrank ℚ ℚ⟮z + z⁻¹⟯ ℚ⟮ζ⟯
  rw [h2, finrank_cyc hζ] at hmul
  have hval : (ℚ⟮ζ⟯).val (z + z⁻¹) = ζ + ζ⁻¹ := rfl
  have hmin : minpoly ℚ (z + z⁻¹) = minpoly ℚ (ζ + ζ⁻¹) := by
    have h5 := minpoly.algHom_eq (ℚ⟮ζ⟯).val Subtype.val_injective (z + z⁻¹)
    rw [hval] at h5
    exact h5.symm
  have heq : Module.finrank ℚ ℚ⟮z + z⁻¹⟯ = Module.finrank ℚ (F1 ζ) := by
    rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (z + z⁻¹)), hmin]
    exact (IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral (ζ + ζ⁻¹))).symm
  rw [← heq]
  rw [pow_succ] at hmul
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) hmul

lemma maxReal_iff {e : ℕ} {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ (e + 2))) :
    ∀ x : ℚ⟮ζ⟯, x ∈ maximalRealSubfield ℚ⟮ζ⟯ ↔ (x : L) ∈ F1 ζ := by
  intro x
  have hint : IsIntegral ℚ ζ := Algebra.IsIntegral.isIntegral ζ
  haveI : FiniteDimensional ℚ ℚ⟮ζ⟯ := adjoin.finiteDimensional hint
  let z : ℚ⟮ζ⟯ := AdjoinSimple.gen ℚ ζ
  have hz : IsPrimitiveRoot z (2 ^ (e + 2)) :=
    (show IsPrimitiveRoot ((ℚ⟮ζ⟯).val z) (2 ^ (e + 2)) from hζ).of_map_of_injective Subtype.val_injective
  have hm : (2 : ℕ) ^ (e + 2) ≠ 0 := by positivity
  have hK : ∀ y ∈ ℚ⟮z + z⁻¹⟯, y ∈ maximalRealSubfield ℚ⟮ζ⟯ := by
    intro y hy
    rw [NumberField.mem_maximalRealSubfield_iff]
    intro φ
    exact real_on_adjoin _ φ (real_theta hm hz φ) y hy
  have himg : (ℚ⟮ζ⟯).val '' {z + z⁻¹} = {ζ + ζ⁻¹} := by
    rw [Set.image_singleton]
    rfl
  constructor
  · intro hx
    have hxK : x ∈ ℚ⟮z + z⁻¹⟯ := by
      have htop : ℚ⟮z⟯ = ⊤ := by
        rw [eq_top_iff]
        intro w _
        apply mem_adjoin_of_val_mem_adjoin_image
        rw [Set.image_singleton]
        exact w.2
      have h2 := finrank_adjoin_add_inv_eq_two_of_isPrimitiveRoot hm (two_pow_not_dvd e) hz htop
      have hintx : IsIntegral ℚ⟮z + z⁻¹⟯ x :=
        IsIntegral.tower_top (Algebra.IsIntegral.isIntegral (R := ℚ) x)
      have hle : (minpoly ℚ⟮z + z⁻¹⟯ x).natDegree ≤ 2 := h2 ▸ minpoly.natDegree_le x
      by_contra hxK
      have hne1 : (minpoly ℚ⟮z + z⁻¹⟯ x).natDegree ≠ 1 := by
        intro h1
        obtain ⟨k, hk⟩ := minpoly.natDegree_eq_one_iff.mp h1
        apply hxK
        rw [← hk]
        exact k.2
      have hpos := minpoly.natDegree_pos hintx
      have hdeg2 : (minpoly ℚ⟮z + z⁻¹⟯ x).natDegree = 2 := by omega
      have hA : adjoin ℚ⟮z + z⁻¹⟯ ({x} : Set ℚ⟮ζ⟯) = ⊤ :=
        IntermediateField.eq_of_le_of_finrank_eq le_top
          (by rw [IntermediateField.adjoin.finrank hintx, hdeg2, IntermediateField.finrank_top', h2])
      have hsub : (adjoin ℚ⟮z + z⁻¹⟯ ({x} : Set ℚ⟮ζ⟯)).toSubfield ≤ maximalRealSubfield ℚ⟮ζ⟯ := by
        show Subfield.closure (Set.range (algebraMap ℚ⟮z + z⁻¹⟯ ℚ⟮ζ⟯) ∪ {x}) ≤ _
        rw [Subfield.closure_le]
        rintro y (⟨k, rfl⟩ | hy)
        · exact hK _ k.2
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          exact hx
      have hzA : z ∈ adjoin ℚ⟮z + z⁻¹⟯ ({x} : Set ℚ⟮ζ⟯) := by
        rw [hA]
        exact IntermediateField.mem_top
      have hzR : z ∈ maximalRealSubfield ℚ⟮ζ⟯ := hsub hzA
      rw [NumberField.mem_maximalRealSubfield_iff] at hzR
      let φ : ℚ⟮ζ⟯ →+* ℂ := (IsAlgClosed.lift : ℚ⟮ζ⟯ →ₐ[ℚ] ℂ).toRingHom
      exact not_real_zeta hm (two_pow_not_dvd e) hz φ (hzR φ)
    have key : Subfield.closure (Set.range (algebraMap ℚ ℚ⟮ζ⟯) ∪ {z + z⁻¹}) ≤
        (F1 ζ).toSubfield.comap ((ℚ⟮ζ⟯).val : ℚ⟮ζ⟯ →+* L) := by
      rw [Subfield.closure_le]
      rintro y (⟨q, rfl⟩ | hy)
      · show ((ℚ⟮ζ⟯).val : ℚ⟮ζ⟯ →+* L) (algebraMap ℚ ℚ⟮ζ⟯ q) ∈ (F1 ζ).toSubfield
        rw [eq_ratCast (algebraMap ℚ ℚ⟮ζ⟯) q, map_ratCast]
        exact SubfieldClass.ratCast_mem _ q
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        show ζ + ζ⁻¹ ∈ F1 ζ
        exact mem_adjoin_simple_self ℚ _
    exact key hxK
  · intro hx
    apply hK
    apply mem_adjoin_of_val_mem_adjoin_image
    rw [himg]
    exact hx

end RealCyclotomicSubfield

open RealCyclotomicSubfield in
theorem real_subfield_of_galois_spec (hSpec : HostGalSpec) : TwoPowerCyclotomicLayerRealSubfieldCharacterization := by
  intro e q d hq L _ _ ζ a b h
  have hζ : IsPrimitiveRoot ζ (2 ^ (e + 2)) := h.1
  refine ⟨?_, maxReal_iff hζ, finrank_real_subfield hζ, real_subfield_real_embeddings hζ, ?_⟩
  · exact hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  · intro σ
    obtain ⟨-, -, h3, -⟩ := hSpec e q d hq L ζ a b h σ
    haveI : Fact (1 < 2 ^ (e + 2)) := ⟨by
      calc 1 < 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)⟩
    have key := h3 1
    have hc1 : hcl e 1 = 1 := QuotientGroup.mk_one _
    simp only [Units.val_one, ZMod.val_one, pow_one, hc1] at key
    rw [key]
    constructor
    · intro hσ
      exact fix_on_adjoin (t := ζ + ζ⁻¹) σ (le_sup_right : F1 ζ ≤ E0 a b ⊔ F1 ζ) hσ
    · intro hfix
      have h4 := hfix (thE ζ a b) (mem_adjoin_simple_self ℚ _)
      rw [h4]
      rfl

theorem hostCMType_of (hGal : HostGalois) (hSpec : HostGalSpec) : HostCMType := by
  intro e q d hq L _ _ ζ a b h
  obtain ⟨-, hfin, -, -⟩ := hGal e q d hq L ζ a b h
  have hb : b ^ 2 = -(d : L) := h.2.2.1
  have hbE : (bE ζ a b) ^ 2 = -(d : hostE ζ a b) := Subtype.ext (by push_cast; exact hb)
  set c : ℂ := Complex.I * (Real.sqrt d : ℂ) with hcdef
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hq.2.1.pos
  have hc2 : c ^ 2 = -(d : ℂ) := by
    rw [hcdef, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt hd0.le]
    simp
  have hc0 : c ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr hd0).ne')
  have hcc : starRingEnd ℂ c = -c := by
    rw [hcdef, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hcne : c ≠ -c := by
    intro h'
    apply hc0
    have h2c : (2 : ℂ) * c = 0 := by linear_combination h'
    simpa using h2c
  have hroots : ∀ φ : hostE ζ a b →+* ℂ, φ (bE ζ a b) = c ∨ φ (bE ζ a b) = -c := by
    intro φ
    have hsq : (φ (bE ζ a b)) ^ 2 = c ^ 2 := by
      rw [hc2, ← map_pow, hbE, map_neg, map_natCast]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq
  have ha : ∀ φ : hostE ζ a b →+* ℂ,
      φ ∈ cmType ζ a b d ↔ (starRingEnd ℂ).comp φ ∉ cmType ζ a b d := by
    intro φ
    show φ (bE ζ a b) = c ↔ ¬ ((starRingEnd ℂ).comp φ) (bE ζ a b) = c
    rw [RingHom.comp_apply]
    rcases hroots φ with h1 | h1 <;> rw [h1]
    · rw [hcc]
      exact ⟨fun _ => hcne.symm, fun _ => rfl⟩
    · rw [map_neg, hcc, neg_neg]
      exact ⟨fun h' => absurd h' hcne.symm, fun h' => absurd rfl h'⟩
  refine ⟨ha, ?_, ?_⟩
  · haveI : NumberField (hostE ζ a b) := {}
    let f : (hostE ζ a b →+* ℂ) → (hostE ζ a b →+* ℂ) := fun φ => (starRingEnd ℂ).comp φ
    have hinv : Function.Involutive f := fun φ => RingHom.ext fun x => by simp [f]
    have hpre : f ⁻¹' (cmType ζ a b d) = (cmType ζ a b d)ᶜ := by
      ext φ
      simp only [Set.mem_preimage, Set.mem_compl_iff]
      exact ⟨fun h1 h2 => ((ha φ).mp h2) h1, fun h1 => by
        by_contra h2
        exact h1 ((ha φ).mpr h2)⟩
    have himg : f '' (cmType ζ a b d) = (cmType ζ a b d)ᶜ := by
      rw [Set.image_eq_preimage_of_inverse hinv.leftInverse hinv.rightInverse, hpre]
    have hcard := Set.ncard_add_ncard_compl (cmType ζ a b d)
    rw [← himg, Set.ncard_image_of_injective _ hinv.injective, Nat.card_eq_fintype_card,
      NumberField.Embeddings.card, hfin, pow_succ] at hcard
    omega
  · intro φ hφ σ
    have hφ' : φ (bE ζ a b) = c := hφ
    show φ (σ (bE ζ a b)) = c ↔ galE e ζ a b σ ∈ Psi e
    rw [Psi, MonoidHom.mem_ker]
    show _ ↔ sgn σ (bE ζ a b) = 1
    unfold sgn
    by_cases hs : σ (bE ζ a b) = bE ζ a b
    · rw [if_pos hs, hs, hφ']
      exact ⟨fun _ => rfl, fun _ => rfl⟩
    · have hsb : σ (bE ζ a b) = -(bE ζ a b) := by
        have hsq : (σ (bE ζ a b)) ^ 2 = (bE ζ a b) ^ 2 := by
          rw [← map_pow, hbE, map_neg, map_natCast]
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h' | h'
        · exact absurd h' hs
        · exact h'
      rw [if_neg hs, hsb, map_neg, hφ']
      exact ⟨fun h' => absurd h'.symm hcne, fun h' => absurd h' (by decide)⟩

theorem real_subfield_and_cm_type (hGal : HostGalois) (hSpec : HostGalSpec) : TwoPowerCyclotomicLayerRealSubfieldCharacterization ∧ HostCMType := by
  exact ⟨real_subfield_of_galois_spec hSpec, hostCMType_of hGal hSpec⟩

end Formalism.FrobeniusOrbits
