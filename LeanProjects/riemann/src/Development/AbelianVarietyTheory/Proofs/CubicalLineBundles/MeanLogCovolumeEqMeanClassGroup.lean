import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SumLogNormEmbeddingEqFinrankMulLogAbsNorm
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeCmEqIdealAndCovolume
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants

open Complex NumberField
open scoped nonZeroDivisors Real UpperHalfPlane

noncomputable section

namespace GlobalTheory

def latticeNormDisc (L : PeriodPair) : ℝ := latticeArea L ^ 6 * ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖

theorem latticeArea_eq_abs_im_mul_conj (L : PeriodPair) :
    latticeArea L = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| := by
  rw [latticeArea_eq, ← abs_neg]
  congr 1
  simp
  ring

theorem latticeNormDisc_eq (L : PeriodPair) :
    latticeNormDisc L = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| ^ 6 * ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖ := by
  rw [latticeNormDisc, latticeArea_eq_abs_im_mul_conj]

theorem latticeNormDisc_pos (L : PeriodPair) : 0 < latticeNormDisc L :=
  mul_pos (pow_pos (latticeArea_pos L) _) (norm_pos_iff.2 (g₂_cube_sub_g₃_sq_ne_zero L))

theorem IsHomothetic.latticeNormDisc_eq {L L' : PeriodPair} {c : ℂ} (h : IsHomothetic c L L') :
    latticeNormDisc L' = latticeNormDisc L := by
  have hc : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 h.ne_zero
  have e : L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 = (c ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    rw [h.g₂_eq, h.g₃_eq]
    ring
  rw [latticeNormDisc, latticeNormDisc, h.latticeArea_eq, e, norm_mul, norm_inv, norm_pow]
  field_simp

def conjPeriods (L : PeriodPair) : PeriodPair where
  ω₁ := starRingEnd ℂ L.ω₁
  ω₂ := starRingEnd ℂ L.ω₂
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    refine LinearIndependent.pair_iff.1 L.indep s t ?_
    have := congrArg (starRingEnd ℂ) h
    simpa using this

theorem mem_conjPeriods_lattice (L : PeriodPair) (z : ℂ) :
    z ∈ (conjPeriods L).lattice ↔ starRingEnd ℂ z ∈ L.lattice := by
  simp only [PeriodPair.mem_lattice, conjPeriods]
  refine exists₂_congr fun m n => ⟨fun h => ?_, fun h => ?_⟩
  · simpa using congrArg (starRingEnd ℂ) h
  · simpa using congrArg (starRingEnd ℂ) h

theorem G_conjPeriods (L : PeriodPair) (n : ℕ) :
    (conjPeriods L).G n = starRingEnd ℂ (L.G n) := by
  let e : L.lattice ≃ (conjPeriods L).lattice :=
    { toFun := fun x => ⟨starRingEnd ℂ x, (mem_conjPeriods_lattice L _).2 (by simp)⟩
      invFun := fun y => ⟨starRingEnd ℂ y, (mem_conjPeriods_lattice L _).1 y.2⟩
      left_inv := fun x => by simp
      right_inv := fun y => by simp }
  simp only [PeriodPair.G]
  rw [← e.tsum_eq, Complex.conj_tsum]
  simp [e]

theorem latticeNormDisc_conjPeriods (L : PeriodPair) :
    latticeNormDisc (conjPeriods L) = latticeNormDisc L := by
  have e : (conjPeriods L).g₂ ^ 3 - 27 * (conjPeriods L).g₃ ^ 2 =
      starRingEnd ℂ (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    simp only [PeriodPair.g₂, PeriodPair.g₃, G_conjPeriods, map_sub, map_mul, map_pow, map_ofNat]
  have a : latticeArea (conjPeriods L) = latticeArea L := by
    rw [latticeArea_eq, latticeArea_eq_abs_im_mul_conj]
    simp [conjPeriods]
  rw [latticeNormDisc, latticeNormDisc, e, a, Complex.norm_conj]

theorem latticeNormDisc_eq_eta {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    latticeNormDisc L = (4 * π ^ 2 * τ.im * ‖ModularForm.eta τ‖ ^ 4) ^ 6 := by
  have hp : ((periodsOfUpperHalfPlane τ).ω₁ = 1 ∧ (periodsOfUpperHalfPlane τ).ω₂ = τ) ∨
      ((periodsOfUpperHalfPlane τ).ω₁ = τ ∧ (periodsOfUpperHalfPlane τ).ω₂ = 1) := by
    simp [periodsOfUpperHalfPlane]
  have H : IsHomothetic a (periodsOfUpperHalfPlane τ) L := by
    intro x
    rw [h, mem_lattice_iff_of_periods_eq hp]
    simp [ha]
  rw [H.latticeNormDisc_eq, latticeNormDisc, latticeArea_periodsOfUpperHalfPlane,
    (invariants_of_periods_eq hp).2.1]
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_ofNat]
  ring

theorem log_pi_sub_log_latticeNormDisc {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    Real.log π - Real.log (|(L.ω₁ * starRingEnd ℂ L.ω₂).im| ^ 6 *
        ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖) / 6 =
      -Real.log (4 * π * τ.im * ‖ModularForm.eta τ‖ ^ 4) := by
  have hpos := latticeNormDisc_pos L
  rw [← latticeNormDisc_eq]
  rw [latticeNormDisc_eq_eta ha h] at hpos ⊢
  have hne : 4 * π * τ.im * ‖ModularForm.eta τ‖ ^ 4 ≠ 0 := by
    intro h0
    rw [show 4 * π ^ 2 * τ.im * ‖ModularForm.eta τ‖ ^ 4 =
      π * (4 * π * τ.im * ‖ModularForm.eta τ‖ ^ 4) by ring, h0] at hpos
    simp at hpos
  rw [Real.log_pow, show 4 * π ^ 2 * τ.im * ‖ModularForm.eta τ‖ ^ 4 =
      π * (4 * π * τ.im * ‖ModularForm.eta τ‖ ^ 4) by ring, Real.log_mul Real.pi_ne_zero hne]
  push_cast
  ring

section CM

variable {K : Type} [Field K] [NumberField K]

theorem embedding_eq_or_eq_conjugate (hK : Module.finrank ℚ K = 2) {σ₀ : K →+* ℂ}
    (h₀ : ¬ ComplexEmbedding.IsReal σ₀) (σ : K →+* ℂ) :
    σ = σ₀ ∨ σ = ComplexEmbedding.conjugate σ₀ := by
  classical
  have hne : σ₀ ≠ ComplexEmbedding.conjugate σ₀ := fun h =>
    h₀ (ComplexEmbedding.isReal_iff.2 h.symm)
  have : ({σ₀, ComplexEmbedding.conjugate σ₀} : Finset (K →+* ℂ)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, Embeddings.card, hK]
  have hm := this ▸ Finset.mem_univ σ
  simpa using hm

theorem exists_mul_mem_iff_of_mk0_eq (𝔞 𝔟 𝔡 : (Ideal (𝓞 K))⁰)
    (h : ClassGroup.mk0 𝔡 * ClassGroup.mk0 𝔟 = ClassGroup.mk0 𝔞) :
    ∃ u : K, u ≠ 0 ∧ ∀ t : K, (∀ b ∈ (𝔟 : Ideal (𝓞 K)), ∃ a ∈ (𝔞 : Ideal (𝓞 K)),
      u * t * (b : K) = a) ↔ ∃ d ∈ (𝔡 : Ideal (𝓞 K)), t = d := by
  rw [← map_mul, ClassGroup.mk0_eq_mk0_iff] at h
  obtain ⟨x, y, hx, hy, e⟩ := h
  have hx' : (x : K) ≠ 0 := by exact_mod_cast hx
  have hy' : (y : K) ≠ 0 := by exact_mod_cast hy
  have hB : ((𝔟 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (nonZeroDivisors.coe_ne_zero 𝔟)
  have e' := congrArg (fun I : Ideal (𝓞 K) => (I : FractionalIdeal (𝓞 K)⁰ K)) e
  simp only [Submonoid.coe_mul, FractionalIdeal.coeIdeal_mul,
    FractionalIdeal.coeIdeal_span_singleton] at e'
  have hY : FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K y) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.2 hy'
  have key : ((𝔞 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) / (𝔟 : Ideal (𝓞 K)) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ ((x : K) / (y : K)) * (𝔡 : Ideal (𝓞 K)) := by
    rw [div_eq_iff hB]
    apply mul_left_cancel₀ hY
    rw [← e', ← mul_assoc, ← mul_assoc, ← mul_assoc,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 3
    change (x : K) = (y : K) * _
    field_simp
  refine ⟨x / y, div_ne_zero hx' hy', fun t => ?_⟩
  have h1 : (∀ b ∈ (𝔟 : Ideal (𝓞 K)), ∃ a ∈ (𝔞 : Ideal (𝓞 K)), (x : K) / y * t * (b : K) = a) ↔
      (x : K) / y * t ∈ ((𝔞 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) / (𝔟 : Ideal (𝓞 K)) := by
    rw [FractionalIdeal.mem_div_iff_of_ne_zero hB]
    constructor
    · intro h b hb
      obtain ⟨b, hb', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hb
      obtain ⟨a, ha, e⟩ := h b hb'
      exact (FractionalIdeal.mem_coeIdeal _).2 ⟨a, ha, e.symm⟩
    · intro h b hb
      obtain ⟨a, ha, e⟩ := (FractionalIdeal.mem_coeIdeal _).1
        (h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hb))
      exact ⟨a, ha, e.symm⟩
  rw [h1, key, FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨d, hd, e⟩
    obtain ⟨d, hd', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hd
    exact ⟨d, hd', mul_left_cancel₀ (div_ne_zero hx' hy') e⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨_, FractionalIdeal.mem_coeIdeal_of_mem _ hd, rfl⟩

theorem exists_isHomothetic_of_mk0_eq (σ : K →+* ℂ) (𝔞 𝔟 𝔡 : (Ideal (𝓞 K))⁰)
    (h : ClassGroup.mk0 𝔡 * ClassGroup.mk0 𝔟 = ClassGroup.mk0 𝔞) {L L' P : PeriodPair}
    {c β : ℂ} (hc : c ≠ 0) (hβ : β ≠ 0)
    (hL : ∀ z, z ∈ L.lattice ↔ ∃ a ∈ (𝔞 : Ideal (𝓞 K)), z = c * σ (a : K))
    (hL' : ∀ z, z ∈ L'.lattice ↔ ∀ y ∈ (𝔟 : Ideal (𝓞 K)), β⁻¹ * σ (y : K) * z ∈ L.lattice)
    (hP : ∀ z, z ∈ P.lattice ↔ ∃ d ∈ (𝔡 : Ideal (𝓞 K)), z = σ (d : K)) :
    ∃ κ : ℂ, IsHomothetic κ P L' := by
  obtain ⟨u, hu, H⟩ := exists_mul_mem_iff_of_mk0_eq 𝔞 𝔟 𝔡 h
  have hu' : σ u ≠ 0 := (map_ne_zero σ).2 hu
  refine ⟨β * c * σ u, fun z => ?_⟩
  have e : ∀ (y : 𝓞 K) (t : K), β⁻¹ * σ (y : K) * (β * c * σ u * σ t) = c * σ (u * t * y) := by
    intro y t
    rw [map_mul, map_mul]
    field_simp
  rw [hL', hP]
  constructor
  · intro hz
    obtain ⟨t, rfl⟩ : ∃ t : K, z = σ t := by
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (nonZeroDivisors.coe_ne_zero 𝔟)
      obtain ⟨a, -, ha⟩ := (hL _).1 (hz y hy)
      have hy1 : σ (y : K) ≠ 0 := by
        rw [map_ne_zero]; exact_mod_cast hy0
      refine ⟨a / (u * y), ?_⟩
      rw [map_div₀, map_mul]
      field_simp
      field_simp at ha
      linear_combination ha
    obtain ⟨d, hd, rfl⟩ := (H t).1 fun b hb => by
      obtain ⟨a, ha, e'⟩ := (hL _).1 (hz b hb)
      rw [e] at e'
      exact ⟨a, ha, σ.injective (mul_left_cancel₀ hc e')⟩
    exact ⟨d, hd, rfl⟩
  · rintro ⟨d, hd, rfl⟩ y hy
    obtain ⟨a, ha, e'⟩ := (H d).2 ⟨d, hd, rfl⟩ y hy
    rw [e, e']
    exact (hL _).2 ⟨a, ha, rfl⟩

end CM

theorem mean_log_covolume_eq_mean_classGroup :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M], Module.finrank ℚ K = 2 →
  ∀ (σ₀ : K →+* ℂ), ¬ NumberField.ComplexEmbedding.IsReal σ₀ →
  ∀ (𝔟 : ClassGroup (𝓞 K) → nonZeroDivisors (Ideal (𝓞 K))) (Lc : ClassGroup (𝓞 K) → PeriodPair), (∀ C, ClassGroup.mk0 (𝔟 C) = C) →
  (∀ C z, z ∈ (Lc C).lattice ↔ ∃ a ∈ (𝔟 C : Ideal (𝓞 K)), z = σ₀ (a : K)) →
  ∀ (L₀ : (M →+* ℂ) → PeriodPair) (L : ClassGroup (𝓞 K) → (M →+* ℂ) → PeriodPair) (δ : ClassGroup (𝓞 K) → (𝓞 M)ˣ) (β : ClassGroup (𝓞 K) → M),
  (∀ s (a : 𝓞 K), ∀ z ∈ (L₀ s).lattice, s (algebraMap K M a) * z ∈ (L₀ s).lattice) →
  (∀ C s, (L C s).g₂ ^ 3 - 27 * (L C s).g₃ ^ 2 = s ((δ C : 𝓞 M) : M)) → (∀ C, β C ≠ 0) →
  (∀ C (x : K), (∀ b ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K))) → IsIntegral ℤ (β C * algebraMap K M x) ∧
    ∀ s, ∀ z ∈ (L₀ s).lattice, s (β C * algebraMap K M x) * z ∈ (L C s).lattice) →
  (∀ C, ∀ y ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ ((β C)⁻¹ * algebraMap K M (y : K)) ∧
    ∀ s, ∀ z ∈ (L C s).lattice, s ((β C)⁻¹ * algebraMap K M (y : K)) * z ∈ (L₀ s).lattice) →
  (∑ s : M →+* ℂ, Real.log |((L₀ s).ω₁ * starRingEnd ℂ (L₀ s).ω₂).im|) / Module.finrank ℚ M =
    (∑ C, Real.log (|((Lc C).ω₁ * starRingEnd ℂ (Lc C).ω₂).im| ^ 6 * ‖(Lc C).g₂ ^ 3 - 27 * (Lc C).g₃ ^ 2‖)) / (6 * Fintype.card (ClassGroup (𝓞 K))) := by
  intro K M _ _ _ _ _ hK σ₀ h₀ 𝔟 Lc h𝔟 hLc L₀ L δ β hst hδ hβ h1 h2
  simp only [← latticeNormDisc_eq]
  simp only [← latticeArea_eq_abs_im_mul_conj]
  have hb0 : ∀ C, (𝔟 C : Ideal (𝓞 K)) ≠ ⊥ := fun C => nonZeroDivisors.coe_ne_zero _
  have hnr : ∀ s : M →+* ℂ, ¬ ComplexEmbedding.IsReal (s.comp (algebraMap K M)) := by
    intro s
    rcases embedding_eq_or_eq_conjugate hK h₀ (s.comp (algebraMap K M)) with h | h <;> rw [h]
    · exact h₀
    · rwa [ComplexEmbedding.isReal_conjugate_iff]
  have hlat := fun C s => lattice_cm_eq_ideal_and_covolume K hK (s.comp (algebraMap K M)) (hnr s)
    (L₀ s) (L C s) (hst s)
  have hsβ : ∀ C (s : M →+* ℂ), s (β C) ≠ 0 := fun C s => (map_ne_zero s).2 (hβ C)
  have hdiv := fun C s => (hlat C s).2 (𝔟 C) (s (β C)) (hb0 C) (hsβ C s)
    (fun x hx z hz => by simpa using (h1 C x hx).2 s z hz)
    (fun y hy z hz => by simpa using (h2 C y hy).2 s z hz)

  have hA : ∀ C, ∑ s, Real.log (latticeNormDisc (L C s)) =
      6 * ∑ s, Real.log (latticeArea (L₀ s)) := by
    intro C
    have hN : (Ideal.absNorm (𝔟 C : Ideal (𝓞 K)) : ℝ) ≠ 0 := by
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.2 (hb0 C)
    have hδ0 : ((δ C : 𝓞 M) : M) ≠ 0 := by exact_mod_cast (δ C).ne_zero
    have e1 : ∑ s : M →+* ℂ, Real.log ‖s ((δ C : 𝓞 M) : M)‖ = 0 := by
      have := sum_log_norm_embedding_eq_finrank_mul_log_absNorm M M ⊤ ((δ C : 𝓞 M) : M)
        top_ne_bot hδ0
        (fun x hx => (RingOfIntegers.isIntegral_coe _).mul (by simpa using hx 1 trivial))
        (fun y _ => by
          have : (((δ C : 𝓞 M) : M))⁻¹ = (((δ C)⁻¹ : (𝓞 M)ˣ) : 𝓞 M) := by
            apply inv_eq_of_mul_eq_one_right
            rw [← map_mul]; simp
          rw [this]
          exact (RingOfIntegers.isIntegral_coe _).mul (RingOfIntegers.isIntegral_coe _))
      simpa using this
    have e2 := sum_log_norm_embedding_eq_finrank_mul_log_absNorm K M (𝔟 C) (β C) (hb0 C) (hβ C)
      (fun x hx => (h1 C x hx).1) (fun y hy => (h2 C y hy).1)
    have e3 : ∀ s : M →+* ℂ, Real.log (latticeNormDisc (L C s)) =
        6 * (2 * Real.log ‖s (β C)‖ + Real.log (latticeArea (L₀ s)) -
          Real.log (Ideal.absNorm (𝔟 C : Ideal (𝓞 K)) : ℝ)) +
          Real.log ‖s ((δ C : 𝓞 M) : M)‖ := by
      intro s
      have h := congrArg Real.log (hdiv C s).2
      rw [← latticeArea_eq_abs_im_mul_conj, ← latticeArea_eq_abs_im_mul_conj,
        Real.log_mul (latticeArea_pos _).ne' hN,
        Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 (hsβ C s))) (latticeArea_pos _).ne',
        Real.log_pow] at h
      rw [latticeNormDisc, Real.log_mul (pow_pos (latticeArea_pos _) _).ne'
        (norm_ne_zero_iff.2 (g₂_cube_sub_g₃_sq_ne_zero _)), Real.log_pow, hδ]
      push_cast at h ⊢
      linarith
    have e4 : (Fintype.card (M →+* ℂ) : ℝ) = 2 * Module.finrank K M := by
      rw [Embeddings.card, ← Module.finrank_mul_finrank ℚ K M, hK]
      push_cast; ring
    simp only [e3, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, e1, e2,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, e4]
    ring

  have hB : ∀ s, ∑ C, Real.log (latticeNormDisc (L C s)) =
      ∑ C, Real.log (latticeNormDisc (Lc C)) := by
    intro s
    obtain ⟨𝔞, c, h𝔞, hc, hL⟩ := (hlat 1 s).1
    let 𝔞' : (Ideal (𝓞 K))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩
    refine Fintype.sum_equiv (Equiv.divLeft (ClassGroup.mk0 𝔞')) _ _ fun C => ?_
    congr 1
    have hcl : ClassGroup.mk0 (𝔟 (ClassGroup.mk0 𝔞' / C)) * ClassGroup.mk0 (𝔟 C) =
        ClassGroup.mk0 𝔞' := by
      rw [h𝔟, h𝔟, div_mul_cancel]
    change _ = latticeNormDisc (Lc (ClassGroup.mk0 𝔞' / C))
    rcases embedding_eq_or_eq_conjugate hK h₀ (s.comp (algebraMap K M)) with h | h
    · obtain ⟨κ, H⟩ := exists_isHomothetic_of_mk0_eq (s.comp (algebraMap K M)) 𝔞' _ _ hcl hc
        (hsβ C s) hL (hdiv C s).1 (P := Lc (ClassGroup.mk0 𝔞' / C)) (by rw [h]; exact hLc _)
      exact H.latticeNormDisc_eq
    · obtain ⟨κ, H⟩ := exists_isHomothetic_of_mk0_eq (s.comp (algebraMap K M)) 𝔞' _ _ hcl hc
        (hsβ C s) hL (hdiv C s).1 (P := conjPeriods (Lc (ClassGroup.mk0 𝔞' / C))) (by
          intro z
          rw [h, mem_conjPeriods_lattice, hLc]
          refine exists_congr fun a => and_congr_right fun _ => ?_
          rw [ComplexEmbedding.conjugate_coe_eq]
          constructor
          · intro e; rw [← e]; simp
          · intro e; rw [e]; simp)
      rw [H.latticeNormDisc_eq, latticeNormDisc_conjPeriods]
  have hS := Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun C s => Real.log (latticeNormDisc (L C s)))
  simp only [hA, hB, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Embeddings.card] at hS
  have hm : (Module.finrank ℚ M : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hh : (Fintype.card (ClassGroup (𝓞 K)) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  linear_combination hS

end GlobalTheory
