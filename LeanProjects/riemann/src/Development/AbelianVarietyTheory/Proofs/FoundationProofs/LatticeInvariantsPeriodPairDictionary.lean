import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.LatticeInvariants

lemma tsum_subtype_congr {p q : ℂ → Prop} (f : ℂ → ℂ) (h : ∀ w, f w ≠ 0 → (p w ↔ q w)) :
    ∑' w : {w // p w}, f w = ∑' w : {w // q w}, f w := by
  refine (tsum_subtype {w | p w} f).trans (Eq.trans ?_ (tsum_subtype {w | q w} f).symm)
  congr with w
  by_cases h0 : f w = 0
  · simp [Set.indicator, h0]
  · simp [Set.indicator, h w h0]

lemma eisG_eq_tsum (Λ : AddSubgroup ℂ) {k : ℕ} (hk : k ≠ 0) :
    eisG Λ k = ∑' w : Λ, ((w : ℂ) ^ (2 * k))⁻¹ := by
  simp only [eisG, one_div]
  refine tsum_subtype_congr (p := fun w ↦ w ∈ Λ ∧ w ≠ 0) (q := fun w ↦ w ∈ Λ)
    (fun w ↦ (w ^ (2 * k))⁻¹) fun w hw ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
  rintro rfl
  simp [hk] at hw

section

variable {L : PeriodPair} {Λ : AddSubgroup ℂ} (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
include h

lemma eisG_eq_G {k : ℕ} (hk : k ≠ 0) : eisG Λ k = L.G (2 * k) := by
  rw [eisG_eq_tsum Λ hk]
  exact tsum_subtype_congr (p := fun w ↦ w ∈ Λ) (q := fun w ↦ w ∈ L.lattice)
    (fun w ↦ (w ^ (2 * k))⁻¹) fun w _ ↦ h w

lemma g2_eq : g2 Λ = L.g₂ := by rw [g2, eisG_eq_G h two_ne_zero]; rfl

lemma lattice_invariant_g3_eq : g3 Λ = L.g₃ := by rw [g3, eisG_eq_G h three_ne_zero]; rfl

lemma wpD_eq (z : ℂ) : wpD Λ z = L.derivWeierstrassP z := by
  rw [wpD, PeriodPair.derivWeierstrassP, neg_mul, ← tsum_mul_left]
  simp only [mul_one_div]
  congr 1
  exact tsum_subtype_congr (p := fun w ↦ w ∈ Λ) (q := fun w ↦ w ∈ L.lattice)
    (fun w ↦ 2 / (z - w) ^ 3) fun w _ ↦ h w

lemma wpF_eq (z : ℂ) : wpF Λ z = L.weierstrassP z := by
  rw [← L.weierstrassPExcept_add 0, wpF, add_comm]
  congr 1
  · refine Eq.trans (tsum_congr fun w ↦ ?_) (tsum_subtype_congr (p := fun w ↦ w ∈ Λ ∧ w ≠ 0)
      (q := fun w ↦ w ∈ L.lattice)
      (fun w ↦ if w = 0 then 0 else 1 / (z - w) ^ 2 - 1 / w ^ 2) fun w hw ↦ ?_)
    · rw [if_neg w.2.2]
    · have : w ≠ 0 := by rintro rfl; simp at hw
      simp [h, this]
  · simp

lemma area_eq : area Λ = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| := by
  refine IsLeast.csInf_eq ⟨⟨?_, L.ω₂, (h _).2 L.ω₂_mem_lattice, L.ω₁, (h _).2 L.ω₁_mem_lattice,
    by rw [mul_comm]⟩, ?_⟩
  · rw [abs_pos]
    intro h0
    have hi := LinearIndependent.pair_iff.mp L.indep
    simp only [Complex.mul_im, Complex.conj_im, Complex.conj_re] at h0
    have h1 := hi L.ω₂.re (-L.ω₁.re) (by
      apply Complex.ext <;> simp
      · ring
      · linarith)
    have h2 := hi L.ω₂.im (-L.ω₁.im) (by
      apply Complex.ext <;> simp
      · linarith
      · ring)
    have h3 : L.ω₂ = 0 := Complex.ext h1.1 h2.1
    simpa using (hi 0 1 (by simp [h3])).2
  · rintro a ⟨ha, w₁, h₁, w₂, h₂, rfl⟩
    obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 ((h _).1 h₁)
    obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.1 ((h _).1 h₂)
    have e : (starRingEnd ℂ (m * L.ω₁ + n * L.ω₂) * (p * L.ω₁ + q * L.ω₂)).im =
        (n * p - m * q : ℤ) * (L.ω₁ * starRingEnd ℂ L.ω₂).im := by
      simp
      ring
    rw [e, abs_mul] at ha ⊢
    have h1 : (n * p - m * q : ℤ) ≠ 0 := by
      intro h0
      simp [h0] at ha
    have h2 : (1 : ℝ) ≤ |((n * p - m * q : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs h1
    exact le_mul_of_one_le_left (abs_nonneg _) h2

end

lemma discrete_of_eisG_ne_zero {Λ : AddSubgroup ℂ} {k : ℕ} (hk : k ≠ 0) (h : eisG Λ k ≠ 0) :
    DiscreteTopology Λ := by
  rw [eisG_eq_tsum Λ hk] at h
  have hs : Summable fun w : Λ ↦ ((w : ℂ) ^ (2 * k))⁻¹ := by
    by_contra hs
    exact h (tsum_eq_zero_of_not_summable hs)
  have hf : {w : Λ | ¬ ‖((w : ℂ) ^ (2 * k))⁻¹‖ < 1}.Finite :=
    Filter.eventually_cofinite.1
      ((tendsto_zero_iff_norm_tendsto_zero.1 hs.tendsto_cofinite_zero).eventually_lt_const one_pos)
  refine discreteTopology_iff_isOpen_singleton_zero.2 ?_
  have ho : IsOpen {w : Λ | ‖(w : ℂ)‖ < 1} := isOpen_lt (by fun_prop) continuous_const
  convert ho.sdiff hf.isClosed using 1
  ext w
  simp only [Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_setOf_eq, not_not]
  constructor
  · rintro rfl
    simp [hk]
  · rintro ⟨h1, h2⟩
    by_contra h0
    have h3 : 0 < ‖(w : ℂ)‖ := by simpa using h0
    rw [norm_inv, norm_pow] at h2
    exact absurd h2 (not_lt.2 ((one_le_inv₀ (by positivity)).2 (pow_le_one₀ h3.le h1.le)))

lemma eisG_of_cyclic {Λ : AddSubgroup ℂ} {a : ℂ} (ha : a ∈ Λ) (h : ∀ w ∈ Λ, ∃ m : ℤ, m • a = w)
    {k : ℕ} (hk : k ≠ 0) : eisG Λ k = (a ^ (2 * k))⁻¹ * (2 * riemannZeta (2 * k : ℕ)) := by
  rw [eisG_eq_tsum Λ hk]
  rcases eq_or_ne a 0 with rfl | h0
  · have : ∀ w : Λ, (w : ℂ) = 0 := fun w ↦ by simpa [eq_comm] using h w w.2
    simp [this, hk]
  let e : ℤ → Λ := fun m ↦ ⟨m • a, Λ.zsmul_mem ha m⟩
  have he : Function.Bijective e := ⟨fun m n hmn ↦ by simpa [e, h0] using hmn,
    fun w ↦ (h w w.2).imp fun m hm ↦ Subtype.ext hm⟩
  rw [← (Equiv.ofBijective e he).tsum_eq,
    two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (by omega) (even_two_mul k), ← tsum_mul_left]
  congr with m
  simp [e, mul_pow]

lemma discr_of_cyclic {Λ : AddSubgroup ℂ} {a : ℂ} (ha : a ∈ Λ)
    (h : ∀ w ∈ Λ, ∃ m : ℤ, m • a = w) : TaylorLogMetric.discr Λ = 0 := by
  have h6 : riemannZeta 6 = Real.pi ^ 6 / 945 := by
    have := riemannZeta_two_mul_nat (k := 3) (by norm_num)
    rw [show bernoulli (2 * 3) = 1 / 42 by decide +kernel] at this
    norm_num [Nat.factorial] at this
    rw [this]
    ring
  rw [TaylorLogMetric.discr, g2, g3, eisG_of_cyclic ha h two_ne_zero, eisG_of_cyclic ha h three_ne_zero]
  norm_num only [riemannZeta_four, h6]
  simp only [← inv_pow]
  ring

lemma exists_periodPair_of_discr_ne_zero {Λ : AddSubgroup ℂ} (h : TaylorLogMetric.discr Λ ≠ 0) :
    ∃ L : PeriodPair, ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
  have hd : DiscreteTopology Λ := by
    by_cases h2 : eisG Λ 2 = 0
    · refine discrete_of_eisG_ne_zero three_ne_zero fun h3 ↦ h ?_
      simp [TaylorLogMetric.discr, g2, g3, h2, h3]
    · exact discrete_of_eisG_ne_zero two_ne_zero h2
  let M : Submodule ℤ ℂ := AddSubgroup.toIntSubmodule Λ
  have hM : DiscreteTopology M := hd
  by_cases hs : Submodule.span ℝ (M : Set ℂ) = ⊤
  · have hZ : IsZLattice ℝ M := ⟨hs⟩
    let b := Module.finBasisOfFinrankEq ℤ M ((ZLattice.rank ℝ M).trans Complex.finrank_real_complex)
    have hi := (b.ofZLatticeBasis ℝ M).linearIndependent
    have e : ⇑(b.ofZLatticeBasis ℝ M) = ![(b 0 : ℂ), b 1] := by
      ext i
      fin_cases i <;> simp
    refine ⟨⟨b 0, b 1, e ▸ hi⟩, fun z ↦ ?_⟩
    change z ∈ M ↔ z ∈ Submodule.span ℤ {(b 0 : ℂ), (b 1 : ℂ)}
    rw [← Matrix.range_cons_cons_empty _ _ ![], ← e, b.ofZLatticeBasis_span ℝ M]
  · have h1 : Module.finrank ℤ M ≤ 1 := by
      have e := Real.finrank_eq_int_finrank_of_discrete (s := (M : Set ℂ))
        (by rw [Submodule.span_eq]; exact hM)
      rw [Set.finrank, Set.finrank, Submodule.span_eq] at e
      have := Submodule.finrank_lt hs
      rw [Complex.finrank_real_complex] at this
      omega
    obtain ⟨v, hv⟩ := finrank_le_one_iff.1 h1
    exact absurd (discr_of_cyclic (a := v) v.2 fun w hw ↦
      (hv ⟨w, hw⟩).imp fun m hm ↦ congrArg Subtype.val hm) h

lemma exists_periodPair_of_invariants {a b : ℂ} (h : a ^ 3 - 27 * b ^ 2 ≠ 0) :
    ∃ L : PeriodPair, L.g₂ = a ∧ L.g₃ = b := by
  obtain ⟨τ, hτ⟩ := exists_E₄_cube_div_discriminant_eq (1728 * a ^ 3 / (a ^ 3 - 27 * b ^ 2))
  let L := periodPairOfTau τ
  have h1 := g₂_cube_div_eq_modularJ one_ne_zero (mem_lattice_periodPairOfTau τ)
  have h0 := g₂_cube_sub_g₃_sq_ne_zero L
  rw [modularJ_def, hτ, div_eq_div_iff h0 h] at h1
  obtain ⟨u, hu, h2, h3⟩ := exists_scale_of_j_eq h0 h (by linear_combination h1 / 1728)
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq u⁻¹ (n := 2) (by norm_num)
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact inv_ne_zero hu (by simpa using hc.symm)
  have H := isHomothetic_scalePeriods L c hc0
  refine ⟨scalePeriods L c hc0, ?_, ?_⟩
  · rw [H.g₂_eq, h2, show c ^ 4 = (c ^ 2) ^ 2 by ring, hc]; simp
  · rw [H.g₃_eq, h3, show c ^ 6 = (c ^ 2) ^ 3 by ring, hc]; simp

theorem invariants_dictionary : ∀ (L : PeriodPair) (Λ : AddSubgroup ℂ), (∀ z, z ∈ Λ ↔ z ∈ L.lattice) → g2 Λ = L.g₂ ∧ g3 Λ = L.g₃ ∧ TaylorLogMetric.discr Λ ≠ 0 ∧ area Λ = |(L.ω₁ * starRingEnd ℂ L.ω₂).im| ∧ (∀ z, z ∉ Λ → wpF Λ z = L.weierstrassP z ∧ wpD Λ z = L.derivWeierstrassP z) ∧ (∀ (Λ' : AddSubgroup ℂ), g2 Λ' = g2 Λ → g3 Λ' = g3 Λ → Λ' = Λ) ∧ ∀ a b : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 → ∃ (L' : PeriodPair), L'.g₂ = a ∧ L'.g₃ = b := by
  intro L Λ h
  have hΔ : TaylorLogMetric.discr Λ ≠ 0 := by
    rw [TaylorLogMetric.discr, g2_eq h, lattice_invariant_g3_eq h]
    exact g₂_cube_sub_g₃_sq_ne_zero L
  refine ⟨g2_eq h, lattice_invariant_g3_eq h, hΔ, area_eq h, fun z _ ↦ ⟨wpF_eq h z, wpD_eq h z⟩,
    fun Λ' h2 h3 ↦ ?_, fun a b ↦ exists_periodPair_of_invariants⟩
  obtain ⟨L', h'⟩ := exists_periodPair_of_discr_ne_zero (Λ := Λ')
    (by rwa [TaylorLogMetric.discr, h2, h3])
  rw [g2_eq h, g2_eq h'] at h2
  rw [lattice_invariant_g3_eq h, lattice_invariant_g3_eq h'] at h3
  ext z
  rw [h, h', lattice_eq_of_g₂_eq_of_g₃_eq h2 h3]

end GlobalTheory.LatticeInvariants
