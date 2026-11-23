import Mathlib
import Formalism.TameInertiaTowers.StatementField
import Lemmata.FirstBlockLemmaE.Imports
import Lemmata.GeneralBFactRightTerForm.Imports

open NumberField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.TwoAdicCyclotomicDecomposition

theorem two_intCast_mem_iff {L : Type} [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [P.LiesOver (span {(2 : ℤ)})] (m : ℤ) :
    (m : 𝓞 L) ∈ P ↔ (2 : ℤ) ∣ m := by
  rw [← Ideal.mem_span_singleton, Ideal.over_def P (span {(2 : ℤ)}), Ideal.under_def,
    Ideal.mem_comap, eq_intCast]

theorem exists_int_quad {L : Type} [Field L] [NumberField L] (x : L) (c : ℤ)
    (hx : x ^ 2 = x + c) : ∃ X : 𝓞 L, (X : L) = x ∧ X ^ 2 = X + (c : 𝓞 L) := by
  first | exact Bl.FirstBlockLemmaE.goal1 .. | (apply Bl.FirstBlockLemmaE.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaE.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaE.goal1 <;> assumption) | (intros; apply @Bl.FirstBlockLemmaE.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaE.goal1 <;> first | assumption | infer_instance) | exact @Bl.FirstBlockLemmaE.goal1 L ‹_› ‹_› x c hx | exact @Bl.FirstBlockLemmaE.goal1 L ‹_› ‹_› x c | exact @Bl.FirstBlockLemmaE.goal1 L ‹_› ‹_› x | exact @Bl.FirstBlockLemmaE.goal1 L ‹_› ‹_› | exact @Bl.FirstBlockLemmaE.goal1 L ‹_› | exact @Bl.FirstBlockLemmaE.goal1 L

theorem gal_sq_fix {L : Type} [Field L] [Algebra ℚ L] (σ : Gal(L/ℚ)) (x : L) (m : ℤ)
    (hx : x ^ 2 = (m : L)) : σ x = x ∨ σ x = -x := by
  have : (σ x) ^ 2 = x ^ 2 := by rw [← map_pow, hx, map_intCast]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp this

theorem half_elt {L : Type} [Field L] [NumberField L] (σ : Gal(L/ℚ)) (x : L) (c : ℤ)
    (hx : x ^ 2 = ((4 * c + 1 : ℤ) : L)) (hσ : σ x = -x) :
    ∃ W : 𝓞 L, W ^ 2 = W + (c : 𝓞 L) ∧ σ • W = 1 - W := by
  have hW2 : ((1 + x) / 2) ^ 2 = (1 + x) / 2 + (c : L) := by
    push_cast at hx
    linear_combination (1 / 4 : L) * hx
  obtain ⟨W, hWc, hW⟩ := exists_int_quad _ c hW2
  refine ⟨W, hW, ?_⟩
  apply RingOfIntegers.coe_injective
  show σ (W : L) = ((1 - W : 𝓞 L) : L)
  have e1 : ((1 - W : 𝓞 L) : L) = 1 - (W : L) := by push_cast; rfl
  rw [e1, hWc, map_div₀, map_add, map_one, hσ, map_ofNat]
  ring

theorem stab_fix {L : Type} [Field L] [NumberField L] (x : L) (c : ℤ)
    (hx : x ^ 2 = ((4 * (2 * c) + 1 : ℤ) : L))
    (P : Ideal (𝓞 L)) [hP : P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] (σ : Gal(L/ℚ))
    (hσ : σ ∈ MulAction.stabilizer Gal(L/ℚ) P) : σ x = x := by
  exact Bl.general_b_fact_right_ter_form.goal1 x c hx P σ hσ

theorem inertia_fix {L : Type} [Field L] [NumberField L] (x : L) (c : ℤ)
    (hx : x ^ 2 = ((4 * c + 1 : ℤ) : L))
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] (σ : Gal(L/ℚ))
    (hσ : ∀ y : 𝓞 L, σ • y - y ∈ P) : σ x = x := by
  rcases gal_sq_fix σ x _ hx with h | h
  · exact h
  exfalso
  obtain ⟨W, hW2, hσW⟩ := half_elt σ x c hx h
  have h1 : 1 - 2 * W ∈ P := by
    have := hσ W
    rw [hσW] at this
    convert this using 1
    ring
  have h2 : (1 - 2 * W) ^ 2 ∈ P := P.pow_mem_of_mem h1 2 (by norm_num)
  have h3 : (1 - 2 * W) ^ 2 = ((4 * c + 1 : ℤ) : 𝓞 L) := by
    push_cast
    linear_combination 4 * hW2
  rw [h3, two_intCast_mem_iff P] at h2
  omega

theorem two_le_inertiaDeg {L : Type} [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [hP : P.IsPrime] [P.LiesOver (span {(2 : ℤ)})]
    (W : 𝓞 L) (c : ℤ) (hW : W ^ 2 = W + (c : 𝓞 L)) (hc : ¬ (2 : ℤ) ∣ c) :
    2 ≤ P.inertiaDeg ℤ := by
  have hpos := P.inertiaDeg_pos ℤ
  by_contra hlt
  have h1 : P.inertiaDeg ℤ = 1 := by omega
  have : P.LiesOver (span {((2 : ℕ) : ℤ)}) := by simpa using (inferInstance : P.LiesOver (span {(2 : ℤ)}))
  have hcard : Nat.card (𝓞 L ⧸ P) = 2 := by
    have := Ideal.pow_inertiaDeg 2 P
    rw [h1, pow_one, Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
    exact this.symm
  obtain ⟨x, y, -, huniv⟩ := Nat.card_eq_two_iff.mp hcard
  have mem : ∀ z : 𝓞 L ⧸ P, z = x ∨ z = y := fun z => by
    have : z ∈ ({x, y} : Set (𝓞 L ⧸ P)) := huniv ▸ Set.mem_univ z
    simpa using this
  have hcP : (c : 𝓞 L) ∉ P := fun h => hc ((two_intCast_mem_iff P c).mp h)
  have hW0 : Ideal.Quotient.mk P W ≠ 0 := by
    intro h
    rw [Ideal.Quotient.eq_zero_iff_mem] at h
    apply hcP
    have : (c : 𝓞 L) = W * W - W := by linear_combination -hW
    rw [this]
    exact P.sub_mem (P.mul_mem_left _ h) h
  have hW1 : Ideal.Quotient.mk P W ≠ 1 := by
    intro h
    rw [← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq] at h
    apply hcP
    have : (c : 𝓞 L) = W * (W - 1) := by linear_combination -hW
    rw [this]
    exact P.mul_mem_left _ h
  have h01 : (0 : 𝓞 L ⧸ P) ≠ 1 := zero_ne_one
  rcases mem 0 with h0 | h0 <;> rcases mem 1 with h1' | h1' <;>
    rcases mem (Ideal.Quotient.mk P W) with h2 | h2 <;>
    first
    | exact h01 (h0.trans h1'.symm)
    | exact hW0 (h2.trans h0.symm)
    | exact hW1 (h2.trans h1'.symm)

theorem le_ramificationIdx {L : Type} [Field L] [NumberField L] (k : ℕ) (ζ : L)
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1)))
    (P : Ideal (𝓞 L)) [hP : P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] :
    2 ^ k ≤ P.ramificationIdx ℤ := by
  set Z : 𝓞 L := ⟨ζ, hζ.isIntegral (by positivity)⟩ with hZdef
  have hZ : IsPrimitiveRoot Z (2 ^ (k + 1)) :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 L) L) hζ RingOfIntegers.coe_injective
  have hassoc : Associated ((Z - 1) ^ (2 ^ k)) (2 : 𝓞 L) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2 : (Polynomial.cyclotomic (2 ^ (k + 1)) (𝓞 L)).eval 1 = 2 := by
      simp [Polynomial.eval_one_cyclotomic_prime_pow (R := 𝓞 L) (p := 2) k]
    rw [← h2, Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hZ, Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    have htot : (2 : ℕ) ^ k = (2 ^ (k + 1)).totient := by
      rw [Nat.totient_prime_pow_succ Nat.prime_two]
      simp
    rw [htot, ← hZ.card_primitiveRoots, ← Finset.prod_const]
    refine Associated.prod _ _ _ fun η hη => ?_
    obtain ⟨i, -, hi, rfl⟩ := hZ.isPrimitiveRoot_iff.mp (isPrimitiveRoot_of_mem_primitiveRoots hη)
    simpa using (hZ.associated_sub_one_pow_sub_one_of_coprime hi).neg_right
  have h2P : (2 : 𝓞 L) ∈ P := by
    have := (two_intCast_mem_iff P 2).mpr dvd_rfl
    simpa using this
  have hZP : Z - 1 ∈ P := by
    obtain ⟨u, hu⟩ := hassoc
    have : (Z - 1) ^ (2 ^ k) = 2 * ↑u⁻¹ := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    exact hP.mem_of_pow_mem _ (this ▸ P.mul_mem_right _ h2P)
  have hmap : map (algebraMap ℤ (𝓞 L)) (span {(2 : ℤ)}) = span {(2 : 𝓞 L)} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have hle : span {(2 : 𝓞 L)} ≤ P ^ (2 ^ k) := by
    rw [← Ideal.span_singleton_eq_span_singleton.mpr hassoc, ← Ideal.span_singleton_pow]
    exact pow_le_pow_left' ((Ideal.span_singleton_le_iff_mem P).mpr hZP) _
  have hne : map (algebraMap ℤ (𝓞 L)) (span {(2 : ℤ)}) ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]
    exact two_ne_zero
  rw [IsDedekindDomain.ramificationIdx_eq_multiplicity (span {(2 : ℤ)}) P hne]
  apply FiniteMultiplicity.le_multiplicity_of_pow_dvd
  · exact FiniteMultiplicity.of_not_isUnit (Ideal.isUnit_iff.not.mpr hP.ne_top) hne
  · rw [Ideal.dvd_iff_le, hmap]
    exact hle

theorem sgn_eq_one_iff {L : Type} [Field L] [Algebra ℚ L] (σ : Gal(L/ℚ)) (x : L) :
    sgn σ x = 1 ↔ σ x = x := by
  unfold sgn
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]
    decide

theorem decomposition_subgroup_index (n : ℕ) : (D2 n).index = 2 := by
  rw [D2, Subgroup.index_ker, MonoidHom.range_eq_top.mpr, Subgroup.card_top,
    Nat.card_eq_fintype_card, Fintype.card_units_int]
  intro u
  exact ⟨(1, 1, u), rfl⟩

theorem inertia_subgroup_index (n : ℕ) : (I2 n).index = 4 := by
  rw [I2, Subgroup.index_ker, MonoidHom.range_eq_top.mpr, Subgroup.card_top, Nat.card_prod,
    Nat.card_eq_fintype_card, Fintype.card_units_int]
  intro u
  exact ⟨(1, u), rfl⟩

theorem two_isPrime : (span {(2 : ℤ)}).IsPrime := by
  rw [Ideal.span_singleton_prime two_ne_zero]
  exact Int.prime_two

theorem efg_L (hG : LayerGalois) {n q d : ℕ} (hn : 1 ≤ n) (hqd : HypQD q d)
    {L : Type} [Field L] [NumberField L] {ζ a b : L} (h : IsLayer n q d ζ a b)
    (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver (span {(2 : ℤ)})] :
    P.ramificationIdx ℤ = 2 ^ (n - 1) ∧ P.inertiaDeg ℤ = 2 ∧
      (primesOver (span {(2 : ℤ)}) (𝓞 L)).ncard = 2 := by
  obtain ⟨hGal, hdeg, hmul, hbij⟩ := hG n q d hn hqd.toHypOdd L ζ a b h
  have : IsGaloisGroup Gal(L/ℚ) ℤ (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ L
  have : (span {(2 : ℤ)}).IsPrime := two_isPrime
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (span {(2 : ℤ)}) (𝓞 L) Gal(L/ℚ)
  rw [ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) P Gal(L/ℚ),
    inertiaDegIn_eq_inertiaDeg (span {(2 : ℤ)}) P Gal(L/ℚ), IsGalois.card_aut_eq_finrank,
    hdeg] at hfund
  obtain ⟨hq, hd, hq8, hd8⟩ := hqd
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have he := le_ramificationIdx k ζ h.1 P

  obtain ⟨c, hc⟩ : ∃ c : ℤ, -(q : ℤ) = 4 * (2 * c + 1) + 1 := ⟨(-(q : ℤ) - 5) / 8, by omega⟩
  have ha : a ^ 2 = ((4 * (2 * c + 1) + 1 : ℤ) : L) := by
    rw [← hc, h.2.1]
    push_cast
    ring
  have hf : 2 ≤ P.inertiaDeg ℤ := by
    have hx2 : ((1 + a) / 2) ^ 2 = (1 + a) / 2 + (((2 * c + 1 : ℤ)) : L) := by
      push_cast at ha ⊢
      linear_combination (1 / 4 : L) * ha
    obtain ⟨W, -, hW⟩ := exists_int_quad _ _ hx2
    exact two_le_inertiaDeg P W _ hW (by omega)

  obtain ⟨c', hc'⟩ : ∃ c : ℤ, -(d : ℤ) = 4 * (2 * c) + 1 := ⟨(-(d : ℤ) - 1) / 8, by omega⟩
  have hb : b ^ 2 = ((4 * (2 * c') + 1 : ℤ) : L) := by
    rw [← hc', h.2.2.1]
    push_cast
    ring
  obtain ⟨τ, hτ⟩ := hbij.2 ((1, 1, -1) : GalL (k + 1))
  have hτb : τ b ≠ b := by
    intro hfix
    have : (galMap h.1 a b τ).2.2 = -1 := by rw [hτ]
    change sgn τ b = -1 at this
    rw [(sgn_eq_one_iff τ b).mpr hfix] at this
    exact absurd this (by decide)
  have hτP : τ • P ≠ P := fun heq =>
    hτb (stab_fix b c' hb P τ (MulAction.mem_stabilizer_iff.mpr heq))
  have hne0 : (primesOver (span {(2 : ℤ)}) (𝓞 L)).ncard ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hfund
    exact absurd hfund.symm (pow_pos two_pos _).ne'
  have hsub : ({P, τ • P} : Set (Ideal (𝓞 L))) ⊆ primesOver (span {(2 : ℤ)}) (𝓞 L) := by
    intro Q hQ
    rcases hQ with rfl | hQ
    · exact ⟨inferInstance, inferInstance⟩
    · rw [Set.mem_singleton_iff] at hQ
      subst hQ
      exact ⟨inferInstance, inferInstance⟩
  have hg : 2 ≤ (primesOver (span {(2 : ℤ)}) (𝓞 L)).ncard := by
    rw [← Set.ncard_pair hτP.symm]
    exact Set.ncard_le_ncard hsub (Set.finite_of_ncard_ne_zero hne0)

  set g := (primesOver (span {(2 : ℤ)}) (𝓞 L)).ncard
  set e := P.ramificationIdx ℤ
  set f := P.inertiaDeg ℤ
  have hN : 2 ^ (k + 1 + 1) = 2 ^ k * 4 := by ring
  rw [hN] at hfund
  simp only [Nat.add_sub_cancel]
  have hef : 2 ^ k * 2 ≤ e * f := Nat.mul_le_mul he hf
  have hef2 : e * f ≤ 2 ^ k * 2 := by nlinarith
  have hef3 : e * f = 2 ^ k * 2 := le_antisymm hef2 hef
  have hpk : 0 < 2 ^ k := by positivity
  have hg2 : g = 2 := by
    rw [hef3] at hfund
    nlinarith
  have he2 : e = 2 ^ k := by
    apply le_antisymm _ he
    nlinarith
  refine ⟨he2, ?_, hg2⟩
  rw [he2] at hef3
  nlinarith

theorem layerDecompTwo_of (hG : LayerGalois) : LayerDecompTwo := by
  intro n q d hn hqd L _ _ ζ a b h P _ _ σ
  obtain ⟨he, hf, -⟩ := efg_L hG hn hqd h P
  obtain ⟨hGal, hdeg, hmul, hbij⟩ := hG n q d hn hqd.toHypOdd L ζ a b h
  have : IsGaloisGroup Gal(L/ℚ) ℤ (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ L
  have : (span {(2 : ℤ)}).IsPrime := two_isPrime
  obtain ⟨hq, hd, hq8, hd8⟩ := hqd
  obtain ⟨c', hc'⟩ : ∃ c : ℤ, -(d : ℤ) = 4 * (2 * c) + 1 := ⟨(-(d : ℤ) - 1) / 8, by omega⟩
  have hb : b ^ 2 = ((4 * (2 * c') + 1 : ℤ) : L) := by
    rw [← hc', h.2.2.1]
    push_cast
    ring
  let φ : Gal(L/ℚ) →* GalL n := MonoidHom.mk' (galMap h.1 a b) hmul
  have hle : MulAction.stabilizer Gal(L/ℚ) P ≤ (D2 n).comap φ := by
    intro τ hτ
    show galMap h.1 a b τ ∈ D2 n
    rw [D2, MonoidHom.mem_ker]
    exact (sgn_eq_one_iff τ b).mpr (stab_fix b c' hb P τ hτ)
  have hcardS : Nat.card (MulAction.stabilizer Gal(L/ℚ) P) = 2 ^ n := by
    rw [card_stabilizer_eq (G := Gal(L/ℚ)) (span {(2 : ℤ)}) P,
      ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) P Gal(L/ℚ),
      inertiaDegIn_eq_inertiaDeg (span {(2 : ℤ)}) P Gal(L/ℚ), he, hf, ← pow_succ]
    congr 1
    omega
  have hcardD : Nat.card ((D2 n).comap φ) = 2 ^ n := by
    have h1 := Subgroup.card_mul_index ((D2 n).comap φ)
    rw [Subgroup.index_comap_of_surjective _ hbij.2, decomposition_subgroup_index, IsGalois.card_aut_eq_finrank, hdeg,
      pow_succ] at h1
    exact Nat.eq_of_mul_eq_mul_right two_pos h1
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardS, hcardD])
  rw [heq]
  rfl

theorem layerInertiaTwo_of (hG : LayerGalois) : LayerInertiaTwo := by
  intro n q d hn hqd L _ _ ζ a b h P _ _ σ
  obtain ⟨he, -, -⟩ := efg_L hG hn hqd h P
  obtain ⟨hGal, hdeg, hmul, hbij⟩ := hG n q d hn hqd.toHypOdd L ζ a b h
  have : IsGaloisGroup Gal(L/ℚ) ℤ (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ L
  have : (span {(2 : ℤ)}).IsPrime := two_isPrime
  obtain ⟨hq, hd, hq8, hd8⟩ := hqd
  obtain ⟨c, hc⟩ : ∃ c : ℤ, -(q : ℤ) = 4 * c + 1 := ⟨(-(q : ℤ) - 1) / 4, by omega⟩
  have ha : a ^ 2 = ((4 * c + 1 : ℤ) : L) := by
    rw [← hc, h.2.1]
    push_cast
    ring
  obtain ⟨c', hc'⟩ : ∃ c : ℤ, -(d : ℤ) = 4 * c + 1 := ⟨(-(d : ℤ) - 1) / 4, by omega⟩
  have hb : b ^ 2 = ((4 * c' + 1 : ℤ) : L) := by
    rw [← hc', h.2.2.1]
    push_cast
    ring
  let φ : Gal(L/ℚ) →* GalL n := MonoidHom.mk' (galMap h.1 a b) hmul
  have hle : P.inertia Gal(L/ℚ) ≤ (I2 n).comap φ := by
    intro τ hτ
    show galMap h.1 a b τ ∈ I2 n
    rw [I2, MonoidHom.mem_ker]
    show (sgn τ a, sgn τ b) = 1
    rw [(sgn_eq_one_iff τ a).mpr (inertia_fix a c ha P τ hτ),
      (sgn_eq_one_iff τ b).mpr (inertia_fix b c' hb P τ hτ)]
    rfl
  have hcardI : Nat.card (P.inertia Gal(L/ℚ)) = 2 ^ (n - 1) := by
    rw [card_inertia_eq_ramificationIdxIn (G := Gal(L/ℚ)) (span {(2 : ℤ)}) P,
      ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) P Gal(L/ℚ), he]
  have hcardD : Nat.card ((I2 n).comap φ) = 2 ^ (n - 1) := by
    have h1 := Subgroup.card_mul_index ((I2 n).comap φ)
    rw [Subgroup.index_comap_of_surjective _ hbij.2, inertia_subgroup_index, IsGalois.card_aut_eq_finrank,
      hdeg, show n + 1 = (n - 1) + 2 by omega, pow_add] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardI, hcardD])
  change σ ∈ P.inertia Gal(L/ℚ) ↔ _
  rw [heq]
  rfl

theorem layerEFGTwo_of (hG : LayerGalois) (hR : LayerReal) : LayerEFGTwo := by
  intro n q d hn hqd L _ _ ζ a b h
  obtain ⟨hGal, hdeg, hmul, hbij⟩ := hG n q d hn hqd.toHypOdd L ζ a b h
  obtain ⟨-, hmemK, hdegK⟩ := hR n q d hn hqd.toHypOdd L ζ a b h
  have : IsGaloisGroup Gal(L/ℚ) ℤ (𝓞 L) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ L
  have : (span {(2 : ℤ)}).IsPrime := two_isPrime
  obtain ⟨⟨P, hPp, hPl⟩⟩ : Nonempty (primesOver (span {(2 : ℤ)}) (𝓞 L)) := inferInstance
  obtain ⟨he, hf, hg⟩ := efg_L hG hn hqd h P
  have hq8 := hqd.2.2.2
  obtain ⟨c', hc'⟩ : ∃ c : ℤ, -(d : ℤ) = 4 * (2 * c) + 1 := ⟨(-(d : ℤ) - 1) / 8, by omega⟩
  have hb : b ^ 2 = ((4 * (2 * c') + 1 : ℤ) : L) := by
    rw [← hc', h.2.2.1]
    push_cast
    ring
  refine ⟨by rw [ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) P Gal(L/ℚ), he],
    by rw [inertiaDegIn_eq_inertiaDeg (span {(2 : ℤ)}) P Gal(L/ℚ), hf], hg, ?_⟩

  set K := maximalRealSubfield L with hKdef
  obtain ⟨τ, hτ⟩ := hbij.2 (JJ n)
  have hτK : ∀ x : L, x ∈ K → τ x = x := fun x hx => (hmemK x).mp hx τ hτ
  have hτb : τ b ≠ b := by
    intro hfix
    have : (galMap h.1 a b τ).2.2 = -1 := by rw [hτ]; rfl
    change sgn τ b = -1 at this
    rw [(sgn_eq_one_iff τ b).mpr hfix] at this
    exact absurd this (by decide)
  have hτP : τ • P ≠ P := fun heq =>
    hτb (stab_fix b c' hb P τ (MulAction.mem_stabilizer_iff.mpr heq))
  have hset : primesOver (span {(2 : ℤ)}) (𝓞 L) = {P, τ • P} := by
    symm
    apply Set.eq_of_subset_of_ncard_le
    · intro Q hQ
      rcases hQ with rfl | hQ
      · exact ⟨inferInstance, inferInstance⟩
      · rw [Set.mem_singleton_iff] at hQ
        subst hQ
        exact ⟨inferInstance, inferInstance⟩
    · rw [hg, Set.ncard_pair hτP.symm]
    · exact Set.finite_of_ncard_ne_zero (by rw [hg]; norm_num)
  set S := 𝓞 K
  set Pp : Ideal S := P.under S with hPp_def
  have hunder : (τ • P).under S = Pp := by
    ext x
    rw [Ideal.under_def, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
      hPp_def, Ideal.under_def, Ideal.mem_comap]
    have hfx : τ⁻¹ • (algebraMap S (𝓞 L) x) = algebraMap S (𝓞 L) x := by
      apply RingOfIntegers.coe_injective
      show τ⁻¹ ((algebraMap S (𝓞 L) x : 𝓞 L) : L) = ((algebraMap S (𝓞 L) x : 𝓞 L) : L)
      have hmem : ((algebraMap S (𝓞 L) x : 𝓞 L) : L) ∈ K := by
        show ((x : K) : L) ∈ K
        exact (x : K).2
      have h1 := hτK _ hmem
      calc τ⁻¹ ((algebraMap S (𝓞 L) x : 𝓞 L) : L)
          = τ⁻¹ (τ ((algebraMap S (𝓞 L) x : 𝓞 L) : L)) := by rw [h1]
        _ = _ := by rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    rw [hfx]
  have hsetK : primesOver (span {(2 : ℤ)}) S = {Pp} := by
    ext Q
    constructor
    · rintro ⟨hQp, hQl⟩
      obtain ⟨⟨R, hRp, hRl⟩⟩ : Nonempty (Q.primesOver (𝓞 L)) := inferInstance
      have : R.LiesOver (span {(2 : ℤ)}) := Ideal.LiesOver.trans R Q (span {(2 : ℤ)})
      have hR2 : R ∈ primesOver (span {(2 : ℤ)}) (𝓞 L) := ⟨hRp, this⟩
      rw [hset] at hR2
      rw [Set.mem_singleton_iff, Ideal.over_def R Q]
      rcases hR2 with rfl | hR2
      · rfl
      · rw [Set.mem_singleton_iff] at hR2
        rw [hR2, hunder]
    · rintro hQ
      rw [Set.mem_singleton_iff] at hQ
      subst hQ
      exact ⟨inferInstance, inferInstance⟩

  have : IsMulCommutative Gal(L/ℚ) := ⟨⟨fun x y => hbij.1 (by rw [hmul, hmul, mul_comm])⟩⟩
  have : IsAbelianGalois ℚ L := { }
  have : IsGalois ℚ K := (IsAbelianGalois.tower_bot ℚ K L).toIsGalois
  have : IsGaloisGroup Gal(K/ℚ) ℤ S := IsGaloisGroup.of_isFractionRing _ _ _ ℚ K
  have hfundK := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (span {(2 : ℤ)}) S Gal(K/ℚ)
  rw [IsGalois.card_aut_eq_finrank, hdegK, hsetK, Set.ncard_singleton, one_mul,
    ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) Pp Gal(K/ℚ),
    inertiaDegIn_eq_inertiaDeg (span {(2 : ℤ)}) Pp Gal(K/ℚ)] at hfundK
  rw [hsetK, Set.ncard_singleton,
    ramificationIdxIn_eq_ramificationIdx (span {(2 : ℤ)}) Pp Gal(K/ℚ),
    inertiaDegIn_eq_inertiaDeg (span {(2 : ℤ)}) Pp Gal(K/ℚ)]
  have hte := Ideal.ramificationIdx_tower (R := ℤ) Pp P
  have htf := Ideal.inertiaDeg_tower (R := ℤ) Pp P
  have hte' := P.ramificationIdx_pos S
  have htf' := P.inertiaDeg_pos S
  rw [he] at hte
  rw [hf] at htf
  set e := Pp.ramificationIdx ℤ
  set f := Pp.inertiaDeg ℤ
  have he1 : e ≤ 2 ^ (n - 1) := by rw [hte]; exact Nat.le_mul_of_pos_right _ hte'
  have hf1 : f ≤ 2 := by rw [htf]; exact Nat.le_mul_of_pos_right _ htf'
  have hN : 2 ^ n = 2 ^ (n - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  rw [hN] at hfundK
  have hpk : 0 < 2 ^ (n - 1) := by positivity
  have he2 : e = 2 ^ (n - 1) := by
    apply le_antisymm he1
    by_contra hlt
    push Not at hlt
    have : e * f < 2 ^ (n - 1) * 2 := by
      calc e * f ≤ e * 2 := Nat.mul_le_mul_left _ hf1
        _ < 2 ^ (n - 1) * 2 := by omega
    omega
  refine ⟨rfl, he2, ?_⟩
  rw [he2] at hfundK
  exact Nat.eq_of_mul_eq_mul_left hpk hfundK

end Formalism.TwoAdicCyclotomicDecomposition
