import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

open Complex NumberField Module
open scoped nonZeroDivisors

namespace GlobalTheory

namespace CMLattice

variable {K : Type} [Field K] [NumberField K]

theorem exists_im_ne_zero (σ : K →+* ℂ) (hσ : ¬ ComplexEmbedding.IsReal σ) :
    ∃ a : 𝓞 K, (σ (a : K)).im ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hσ
  rw [NumberField.ComplexEmbedding.isReal_iff]
  ext x
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have key : ∀ y : 𝓞 K, starRingEnd ℂ (σ (algebraMap (𝓞 K) K y)) = σ (algebraMap (𝓞 K) K y) :=
    fun y => Complex.conj_eq_iff_im.2 (hcon y)
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq, map_div₀, map_div₀, key, key]

theorem ω₁_ne_zero (L : PeriodPair) : L.ω₁ ≠ 0 := by
  simpa using L.indep.ne_zero 0

theorem exists_ideal (σ : K →+* ℂ) (hσ : ¬ ComplexEmbedding.IsReal σ) (L : PeriodPair)
    (hL : ∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice) :
    ∃ (𝔞 : Ideal (𝓞 K)) (c : ℂ), 𝔞 ≠ ⊥ ∧ c ≠ 0 ∧
      ∀ z, z ∈ L.lattice ↔ ∃ a ∈ 𝔞, z = c * σ (a : K) := by
  obtain ⟨a, ha⟩ := exists_im_ne_zero σ hσ
  have hω : L.ω₁ ≠ 0 := ω₁_ne_zero L
  obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.1 (hL a _ L.ω₁_mem_lattice)
  have hn : (n : ℂ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul, add_zero] at hmn
    have : σ (a : K) = m := (mul_right_cancel₀ hω hmn).symm
    rw [this] at ha
    simp at ha
  set t : K := ((a : K) - m) / n with ht
  have hσt : σ t * L.ω₁ = L.ω₂ := by
    rw [ht, map_div₀, map_sub, map_intCast, map_intCast, div_mul_eq_mul_div, div_eq_iff hn]
    linear_combination (-1 : ℂ) * hmn
  have hstab : ∀ (r : 𝓞 K) (p q : ℤ), ∃ p' q' : ℤ, (r : K) * (p + q * t) = p' + q' * t := by
    intro r p q
    have hmem : (p : ℂ) * L.ω₁ + q * L.ω₂ ∈ L.lattice := PeriodPair.mem_lattice.2 ⟨p, q, rfl⟩
    obtain ⟨p', q', hpq⟩ := PeriodPair.mem_lattice.1 (hL r _ hmem)
    refine ⟨p', q', σ.injective ?_⟩
    apply mul_right_cancel₀ hω
    simp only [map_mul, map_add, map_intCast]
    rw [← hσt] at hpq
    linear_combination (-1 : ℂ) * hpq
  obtain ⟨u, v, hv, htuv⟩ := IsFractionRing.div_surjective (A := 𝓞 K) t
  have hv0 : v ≠ 0 := nonZeroDivisors.ne_zero hv
  have hV0 : (v : K) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hv
  have hσV : σ (v : K) ≠ 0 := (map_ne_zero σ).2 hV0
  have hu : (u : K) = (v : K) * t := by
    rw [← htuv]; field_simp
  let 𝔞 : Ideal (𝓞 K) :=
    { carrier := {x | ∃ p q : ℤ, (x : K) = (v : K) * (p + q * t)}
      add_mem' := by
        rintro x y ⟨p, q, hx⟩ ⟨p', q', hy⟩
        exact ⟨p + p', q + q', by
          rw [RingOfIntegers.coe_eq_algebraMap, map_add, ← RingOfIntegers.coe_eq_algebraMap,
            ← RingOfIntegers.coe_eq_algebraMap, hx, hy]
          push_cast; ring⟩
      zero_mem' := ⟨0, 0, by simp⟩
      smul_mem' := by
        rintro r x ⟨p, q, hx⟩
        obtain ⟨p', q', h'⟩ := hstab r p q
        refine ⟨p', q', ?_⟩
        rw [smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul, ← RingOfIntegers.coe_eq_algebraMap,
          ← RingOfIntegers.coe_eq_algebraMap, hx, ← h']
        ring }
  have hmem𝔞 : ∀ x : 𝓞 K, x ∈ 𝔞 ↔ ∃ p q : ℤ, (x : K) = (v : K) * (p + q * t) := fun x => Iff.rfl
  refine ⟨𝔞, L.ω₁ / σ (v : K), ?_, div_ne_zero hω hσV, ?_⟩
  · intro hbot
    have h1 : v ∈ 𝔞 := (hmem𝔞 v).2 ⟨1, 0, by simp⟩
    rw [hbot] at h1
    exact hv0 ((Submodule.mem_bot _).1 h1)
  · intro z
    constructor
    · intro hz
      obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.1 hz
      refine ⟨v * p + q * u, (hmem𝔞 _).2 ⟨p, q, ?_⟩, ?_⟩
      · rw [RingOfIntegers.coe_eq_algebraMap]
        simp only [map_add, map_mul, map_intCast, ← RingOfIntegers.coe_eq_algebraMap, hu]
        ring
      · rw [RingOfIntegers.coe_eq_algebraMap]
        simp only [map_add, map_mul, map_intCast, ← RingOfIntegers.coe_eq_algebraMap, hu]
        rw [← hσt]
        field_simp
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨p, q, hpq⟩ := (hmem𝔞 x).1 hx
      refine PeriodPair.mem_lattice.2 ⟨p, q, ?_⟩
      rw [hpq, ← hσt]
      simp only [map_mul, map_add, map_intCast]
      field_simp

theorem im_mul_conj_eq_det (σ : K →+* ℂ) (b : Basis (Fin 2) ℚ K) (v : Fin 2 → K) :
    (σ (v 0) * starRingEnd ℂ (σ (v 1))).im =
      (b.det v : ℚ) * (σ (b 0) * starRingEnd ℂ (σ (b 1))).im := by
  have hv : ∀ j, σ (v j) = ∑ i, ((b.toMatrix v i j : ℚ) : ℂ) * σ (b i) := by
    intro j
    conv_lhs => rw [← b.sum_toMatrix_smul_self v j]
    simp [Rat.smul_def, map_mul, map_ratCast]
  rw [hv 0, hv 1, Basis.det_apply, Matrix.det_fin_two]
  simp only [Fin.sum_univ_two, map_add, map_mul, map_ratCast, Complex.mul_im, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.ratCast_re,
    Complex.ratCast_im]
  push_cast
  ring

theorem covol_eq (σ : K →+* ℂ) (b : Basis (Fin 2) ℤ (𝓞 K)) (L : PeriodPair)
    (I : FractionalIdeal (𝓞 K)⁰ K) (c : ℂ) (hc : c ≠ 0)
    (h : ∀ z, z ∈ L.lattice ↔ ∃ x ∈ I, z = c * σ x) :
    |(L.ω₁ * starRingEnd ℂ L.ω₂).im| = ‖c‖ ^ 2 * (FractionalIdeal.absNorm I : ℚ) *
      |(σ (b 0 : K) * starRingEnd ℂ (σ (b 1 : K))).im| := by
  obtain ⟨u0, hu0, e0⟩ := (h L.ω₁).1 L.ω₁_mem_lattice
  obtain ⟨u1, hu1, e1⟩ := (h L.ω₂).1 L.ω₂_mem_lattice
  let w : Fin 2 → (I : Submodule (𝓞 K) K) := ![⟨u0, hu0⟩, ⟨u1, hu1⟩]
  have hli : LinearIndependent ℤ w := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hK : (s : K) * u0 + t * u1 = 0 := by
      have := congrArg Subtype.val hst
      simpa [zsmul_eq_mul] using this
    have h' : (s : ℝ) • L.ω₁ + (t : ℝ) • L.ω₂ = 0 := by
      rw [e0, e1, Complex.real_smul, Complex.real_smul]
      have := congrArg (fun y => c * σ y) hK
      simp only [map_add, map_mul, map_intCast, map_zero, mul_zero] at this
      push_cast
      linear_combination this
    have := LinearIndependent.pair_iff.1 L.indep s t h'
    exact_mod_cast this
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range w) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.1 ((h (c * σ x)).2 ⟨x, hx, rfl⟩)
    have hxK : x = p * u0 + q * u1 := by
      apply σ.injective
      apply mul_left_cancel₀ hc
      rw [map_add, map_mul, map_mul, map_intCast, map_intCast, ← hpq, e0, e1]
      ring
    have hx' : (⟨x, hx⟩ : (I : Submodule (𝓞 K) K)) = p • w 0 + q • w 1 := by
      ext
      simp [w, hxK, zsmul_eq_mul]
    rw [hx']
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  let bI : Basis (Fin 2) ℤ (I : Submodule (𝓞 K) K) := Basis.mk hli hsp
  have hdet := FractionalIdeal.abs_det_basis_change b I bI
  have hcomp : ((↑) ∘ bI : Fin 2 → K) = ![u0, u1] := by
    ext i
    fin_cases i <;> simp [bI, w]
  rw [hcomp] at hdet
  have him := im_mul_conj_eq_det σ (b.localizationLocalization ℚ ℤ⁰ K) ![u0, u1]
  simp only [Basis.localizationLocalization_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at him
  have hsq : (c * σ u0 * starRingEnd ℂ (c * σ u1)).im = ‖c‖ ^ 2 * (σ u0 * starRingEnd ℂ (σ u1)).im := by
    rw [map_mul, show c * σ u0 * (starRingEnd ℂ c * starRingEnd ℂ (σ u1)) =
      (c * starRingEnd ℂ c) * (σ u0 * starRingEnd ℂ (σ u1)) by ring, Complex.mul_conj,
      Complex.im_ofReal_mul, Complex.normSq_eq_norm_sq]
  rw [e0, e1, hsq, abs_mul, abs_of_nonneg (by positivity), him, abs_mul, ← Rat.cast_abs, hdet]
  simp only [RingOfIntegers.coe_eq_algebraMap]
  ring

theorem mem_iff (σ : K →+* ℂ) (L L' : PeriodPair) (𝔟 : Ideal (𝓞 K)) (β : ℂ) (h𝔟 : 𝔟 ≠ ⊥)
    (hβ : β ≠ 0)
    (h1 : ∀ x : K, (∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K))) → ∀ z ∈ L.lattice,
      β * σ x * z ∈ L'.lattice)
    (h2 : ∀ y ∈ 𝔟, ∀ z ∈ L'.lattice, β⁻¹ * σ (y : K) * z ∈ L.lattice) (z : ℂ) :
    z ∈ L'.lattice ↔ ∀ y ∈ 𝔟, β⁻¹ * σ (y : K) * z ∈ L.lattice := by
  constructor
  · intro hz y hy
    exact h2 y hy z hz
  · intro hz
    have hb0 : (𝔟 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔟
    have h1mem : (1 : K) ∈ (𝔟 : FractionalIdeal (𝓞 K)⁰ K)⁻¹ * 𝔟 := by
      rw [inv_mul_cancel₀ hb0]
      exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
    have key : σ 1 * z ∈ L'.lattice := by
      refine FractionalIdeal.mul_induction_on (C := fun w => σ w * z ∈ L'.lattice) h1mem ?_ ?_
      · intro x hx y hy
        obtain ⟨y', hy', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
        have hx' : ∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K)) := by
          intro b hb
          obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 ((FractionalIdeal.mem_inv_iff hb0).1 hx _
            ((FractionalIdeal.mem_coeIdeal _).2 ⟨b, hb, rfl⟩))
          rw [RingOfIntegers.coe_eq_algebraMap, ← hr]
          exact RingOfIntegers.isIntegral_coe r
        have hmem := h1 x hx' _ (hz y' hy')
        have e : σ (x * algebraMap (𝓞 K) K y') * z = β * σ x * (β⁻¹ * σ (y' : K) * z) := by
          rw [map_mul, RingOfIntegers.coe_eq_algebraMap]
          field_simp
        show σ (x * algebraMap (𝓞 K) K y') * z ∈ L'.lattice
        rw [e]
        exact hmem
      · intro x y hx hy
        show σ (x + y) * z ∈ L'.lattice
        rw [map_add, add_mul]
        exact add_mem hx hy
    simpa using key

end CMLattice

open CMLattice in

theorem lattice_cm_eq_ideal_and_covolume :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ : K →+* ℂ), ¬ NumberField.ComplexEmbedding.IsReal σ →
  ∀ (L L' : PeriodPair), (∀ (a : 𝓞 K), ∀ z ∈ L.lattice, σ (a : K) * z ∈ L.lattice) →
  (∃ (𝔞 : Ideal (𝓞 K)) (c : ℂ), 𝔞 ≠ ⊥ ∧ c ≠ 0 ∧ ∀ z, z ∈ L.lattice ↔ ∃ a ∈ 𝔞, z = c * σ (a : K)) ∧
  ∀ (𝔟 : Ideal (𝓞 K)) (β : ℂ), 𝔟 ≠ ⊥ → β ≠ 0 →
    (∀ x : K, (∀ b ∈ 𝔟, IsIntegral ℤ (x * (b : K))) → ∀ z ∈ L.lattice, β * σ x * z ∈ L'.lattice) →
    (∀ y ∈ 𝔟, ∀ z ∈ L'.lattice, β⁻¹ * σ (y : K) * z ∈ L.lattice) →
    (∀ z, z ∈ L'.lattice ↔ ∀ y ∈ 𝔟, β⁻¹ * σ (y : K) * z ∈ L.lattice) ∧
    |(L'.ω₁ * starRingEnd ℂ L'.ω₂).im| * Ideal.absNorm 𝔟 = ‖β‖ ^ 2 * |(L.ω₁ * starRingEnd ℂ L.ω₂).im| := by
  intro K _ _ hK σ hσ L L' hL
  refine ⟨exists_ideal σ hσ L hL, ?_⟩
  intro 𝔟 β h𝔟 hβ h1 h2
  have hmem := mem_iff σ L L' 𝔟 β h𝔟 hβ h1 h2
  refine ⟨hmem, ?_⟩
  obtain ⟨𝔞, c, -, hc, hLc⟩ := exists_ideal σ hσ L hL
  let b : Basis (Fin 2) ℤ (𝓞 K) :=
    Module.finBasisOfFinrankEq ℤ (𝓞 K) ((RingOfIntegers.rank K).trans hK)
  set A0 : FractionalIdeal (𝓞 K)⁰ K := (𝔞 : FractionalIdeal (𝓞 K)⁰ K) with hA0
  set Bb : FractionalIdeal (𝓞 K)⁰ K := (𝔟 : FractionalIdeal (𝓞 K)⁰ K) with hBb
  have hb0 : Bb ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔟
  have hL1 : ∀ z, z ∈ L.lattice ↔ ∃ x ∈ A0, z = c * σ x := by
    intro z
    rw [hLc z]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨_, (FractionalIdeal.mem_coeIdeal _).2 ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      exact ⟨a, ha, rfl⟩
  have hL2 : ∀ z, z ∈ L'.lattice ↔ ∃ x ∈ Bb⁻¹ * A0, z = (β * c) * σ x := by
    intro z
    constructor
    · intro hz
      have h1mem : (1 : K) ∈ Bb⁻¹ * Bb := by
        rw [inv_mul_cancel₀ hb0]
        exact (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
      have key : ∃ x ∈ Bb⁻¹ * A0, σ 1 * z = (β * c) * σ x := by
        refine FractionalIdeal.mul_induction_on
          (C := fun w => ∃ x ∈ Bb⁻¹ * A0, σ w * z = (β * c) * σ x) h1mem ?_ ?_
        · intro x hx y hy
          obtain ⟨y', hy', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
          obtain ⟨a, ha, hae⟩ := (hL1 _).1 ((hmem z).1 hz y' hy')
          refine ⟨x * a, FractionalIdeal.mul_mem_mul hx ha, ?_⟩
          rw [map_mul, map_mul]
          calc σ x * σ (algebraMap (𝓞 K) K y') * z
              = β * σ x * (β⁻¹ * σ (y' : K) * z) := by
                rw [RingOfIntegers.coe_eq_algebraMap]; field_simp
            _ = β * c * (σ x * σ a) := by rw [hae]; ring
        · rintro x y ⟨x1, hx1, e1⟩ ⟨y1, hy1, e2⟩
          exact ⟨x1 + y1, Submodule.add_mem (↑(Bb⁻¹ * A0) : Submodule (𝓞 K) K) hx1 hy1, by rw [map_add, add_mul, e1, e2, map_add]; ring⟩
      simpa using key
    · rintro ⟨x, hx, rfl⟩
      rw [hmem]
      intro y hy
      refine (hL1 _).2 ⟨(y : K) * x, ?_, ?_⟩
      · have hyx : (y : K) * x ∈ Bb * (Bb⁻¹ * A0) :=
          FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨y, hy, rfl⟩) hx
        rwa [← mul_assoc, mul_inv_cancel₀ hb0, one_mul] at hyx
      · rw [map_mul]
        field_simp
  have hcL := covol_eq σ b L A0 c hc hL1
  have hcL' := covol_eq σ b L' (Bb⁻¹ * A0) (β * c) (mul_ne_zero hβ hc) hL2
  have hN : (Ideal.absNorm 𝔟 : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 h𝔟)
  rw [hcL, hcL', map_mul, map_inv₀, hA0, hBb, FractionalIdeal.coeIdeal_absNorm,
    FractionalIdeal.coeIdeal_absNorm, norm_mul]
  push_cast
  field_simp

end GlobalTheory
