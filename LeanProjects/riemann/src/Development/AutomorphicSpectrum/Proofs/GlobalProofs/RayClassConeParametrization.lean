import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

variable {F : Type} [Field F] [NumberField F]

theorem TotPos.ne_zero [IsTotallyReal F] {x : F} (h : TotPos F x) : x ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hw : w.IsReal := IsTotallyReal.isReal w
  have := h (InfinitePlace.embedding_of_isReal hw)
  rintro rfl
  simp at this

def RayPoint (𝔣 𝔟 : Ideal (𝓞 F)) (ξ : 𝓞 F) : Prop := ξ ∈ 𝔟 ∧ ξ - 1 ∈ 𝔣 ∧ TotPos F (ξ : F)

theorem exists_complement {𝔣 𝔞 : Ideal (𝓞 F)} (h𝔣 : 𝔣 ≠ ⊥) (h𝔞 : CoprimeTo F 𝔣 𝔞) :
    ∃ (𝔟 : Ideal (𝓞 F)) (x₀ : 𝓞 F), CoprimeTo F 𝔣 𝔟 ∧ x₀ ≠ 0 ∧ x₀ - 1 ∈ 𝔣 ∧ TotPos F (x₀ : F) ∧
      𝔞 * 𝔟 = Ideal.span {x₀} := by
  classical
  have h0 : 𝔞 ∈ nonZeroDivisors (Ideal (𝓞 F)) := mem_nonZeroDivisors_of_ne_zero h𝔞.1
  obtain ⟨h, hh, hp⟩ : ∃ h : ℕ, 0 < h ∧ (𝔞 ^ h).IsPrincipal := by
    refine ⟨Fintype.card (ClassGroup (𝓞 F)), Fintype.card_pos, ?_⟩
    have hmem : 𝔞 ^ Fintype.card (ClassGroup (𝓞 F)) ∈ nonZeroDivisors (Ideal (𝓞 F)) :=
      mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ h𝔞.1)
    have h1 : ClassGroup.mk0 ⟨𝔞 ^ Fintype.card (ClassGroup (𝓞 F)), hmem⟩ = 1 := by
      have e : (⟨𝔞 ^ Fintype.card (ClassGroup (𝓞 F)), hmem⟩ : nonZeroDivisors (Ideal (𝓞 F))) =
          ⟨𝔞, h0⟩ ^ Fintype.card (ClassGroup (𝓞 F)) := Subtype.ext (by simp)
      rw [e, map_pow, pow_card_eq_one]
    exact (ClassGroup.mk0_eq_one_iff hmem).1 h1
  obtain ⟨α, hα⟩ := hp.principal
  have hα' : 𝔞 ^ h = Ideal.span {α} := hα
  have hne : ∀ n : ℕ, 𝔞 ^ n ≠ ⊥ := fun n => pow_ne_zero n h𝔞.1
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact hne h (by rw [hα']; simp)
  have hco : IsCoprime 𝔞 𝔣 := Ideal.isCoprime_iff_sup_eq.2 h𝔞.2
  have hsup : Ideal.span {α} ⊔ 𝔣 = ⊤ := by rw [← hα']; exact Ideal.isCoprime_iff_sup_eq.1 hco.pow_left
  obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.1 (hsup ▸ Submodule.mem_top : (1 : 𝓞 F) ∈ Ideal.span {α} ⊔ 𝔣)
  haveI : Finite (𝓞 F ⧸ 𝔣) := Ideal.finiteQuotientOfFreeOfNeBot 𝔣 h𝔣
  have hu : IsUnit (Ideal.Quotient.mk 𝔣 α) := by
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk 𝔣 a) ?_
    have : Ideal.Quotient.mk 𝔣 b = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hb
    rw [mul_comm, ← map_mul, ← map_one (Ideal.Quotient.mk 𝔣), ← hab, map_add, this, add_zero]
  obtain ⟨u, hu⟩ := hu
  set e := Nat.card (𝓞 F ⧸ 𝔣)ˣ with he
  have he0 : 0 < e := Nat.card_pos
  have hpow : Ideal.Quotient.mk 𝔣 (α ^ (2 * e)) = 1 := by
    rw [map_pow, ← hu, pow_mul', ← Units.val_pow_eq_pow_val, pow_card_eq_one']
    simp
  refine ⟨𝔞 ^ (h * (2 * e) - 1), α ^ (2 * e), ⟨hne _, ?_⟩, pow_ne_zero _ hα0, ?_, ?_, ?_⟩
  · exact Ideal.isCoprime_iff_sup_eq.1 hco.pow_left
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hpow, map_one, sub_self]
  · intro σ
    have : σ ((α : F)) ≠ 0 := (map_ne_zero σ).2 (by simpa using hα0)
    have e1 : ((α ^ (2 * e) : 𝓞 F) : F) = (α : F) ^ (2 * e) := rfl
    rw [e1, map_pow]
    exact (even_two_mul e).pow_pos this
  · have hpos : 0 < h * (2 * e) := by positivity
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_mul, hα', Ideal.span_singleton_pow]

theorem RayPoint.exists_ideal [IsTotallyReal F] {𝔣 𝔞 𝔟 : Ideal (𝓞 F)} {x₀ ξ : 𝓞 F} (hx0 : x₀ ≠ 0) (hx1 : x₀ - 1 ∈ 𝔣)
    (hxp : TotPos F (x₀ : F)) (hab : 𝔞 * 𝔟 = Ideal.span {x₀}) (h : RayPoint 𝔣 𝔟 ξ) :
    ∃ I : Ideal (𝓞 F), (CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞) ∧ I * 𝔟 = Ideal.span {ξ} := by
  obtain ⟨h1, h2, h3⟩ := h
  have hξ : ξ ≠ 0 := fun e => h3.ne_zero (by simp [e])
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h1)
  refine ⟨I, ⟨⟨?_, ?_⟩, x₀, ξ, hx0, hξ, hx1, h2, fun σ => ⟨hxp σ, h3 σ⟩, ?_⟩, by rw [mul_comm, hI]⟩
  · rintro rfl
    simp at hI
    exact hξ hI
  · have hle : ξ ∈ I := (Ideal.mul_le_right : 𝔟 * I ≤ I) (hI ▸ Ideal.mem_span_singleton_self ξ)
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 F) = ξ - (ξ - 1) := by ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.mem_sup_left hle) (Ideal.mem_sup_right h2)
  · rw [← hab, hI]
    ring

theorem RayPoint.of_ideal {𝔣 𝔞 𝔟 I : Ideal (𝓞 F)} {x₀ : 𝓞 F} (hx0 : x₀ ≠ 0) (hx1 : x₀ - 1 ∈ 𝔣)
    (hxp : TotPos F (x₀ : F)) (hab : 𝔞 * 𝔟 = Ideal.span {x₀}) (hI : RayRel F 𝔣 I 𝔞) :
    ∃ ξ : 𝓞 F, RayPoint 𝔣 𝔟 ξ ∧ I * 𝔟 = Ideal.span {ξ} := by
  obtain ⟨a, b, ha, hb, ha1, hb1, hp, e⟩ := hI
  have e1 : Ideal.span {a} * (I * 𝔟) = Ideal.span {b * x₀} := by
    rw [← mul_assoc, e, mul_assoc, hab, Ideal.span_singleton_mul_span_singleton]
  obtain ⟨ξ, hξ, hξe⟩ := Ideal.mem_span_singleton_mul.1 (e1 ▸ Ideal.mem_span_singleton_self (b * x₀))
  have e2 : I * 𝔟 = Ideal.span {ξ} := by
    rw [← Ideal.span_singleton_mul_right_inj ha, e1, ← hξe, Ideal.span_singleton_mul_span_singleton]
  refine ⟨ξ, ⟨(Ideal.mul_le_right : I * 𝔟 ≤ 𝔟) hξ, ?_, fun σ => ?_⟩, e2⟩
  · have : ξ - 1 = (b * (x₀ - 1) + (b - 1) - (a - 1)) - (a - 1) * (ξ - 1) := by linear_combination hξe
    rw [this]
    exact 𝔣.sub_mem (𝔣.sub_mem (𝔣.add_mem (𝔣.mul_mem_left _ hx1) hb1) ha1) (𝔣.mul_mem_right _ ha1)
  · have e3 : σ (a : F) * σ (ξ : F) = σ (b : F) * σ (x₀ : F) := by
      have : (a : F) * (ξ : F) = (b : F) * (x₀ : F) := congrArg (fun z : 𝓞 F => (z : F)) hξe
      have h2 := congrArg σ this
      rwa [map_mul, map_mul] at h2
    exact (mul_pos_iff_of_pos_left (hp σ).1).1 (e3 ▸ mul_pos (hp σ).2 (hxp σ))

theorem RayPoint.exists_unit [IsTotallyReal F] {𝔣 𝔟 : Ideal (𝓞 F)} {ξ ξ' : 𝓞 F} (h : RayPoint 𝔣 𝔟 ξ) (h' : RayPoint 𝔣 𝔟 ξ')
    (e : Ideal.span {ξ} = Ideal.span {ξ'}) : ∃ u ∈ congUnits 𝔣, ξ' = (u : 𝓞 F) * ξ := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1 e
  refine ⟨u, ⟨?_, fun σ => ?_⟩, by rw [← hu, mul_comm]⟩
  · have : (u : 𝓞 F) - 1 = ((ξ' - 1) - (ξ - 1)) - (ξ - 1) * ((u : 𝓞 F) - 1) := by linear_combination hu
    rw [this]
    exact 𝔣.sub_mem (𝔣.sub_mem h'.2.1 h.2.1) (𝔣.mul_mem_right _ h.2.1)
  · have e3 : σ (ξ : F) * σ (((u : 𝓞 F)) : F) = σ (ξ' : F) := by
      rw [← map_mul]
      congr 1
      exact congrArg (fun z : 𝓞 F => (z : F)) hu
    exact (mul_pos_iff_of_pos_left (h.2.2 σ)).1 (e3 ▸ h'.2.2 σ)

theorem RayPoint.unit_mul {𝔣 𝔟 : Ideal (𝓞 F)} {ξ : 𝓞 F} (h : RayPoint 𝔣 𝔟 ξ) {u : (𝓞 F)ˣ} (hu : u ∈ congUnits 𝔣) :
    RayPoint 𝔣 𝔟 ((u : 𝓞 F) * ξ) := by
  refine ⟨𝔟.mul_mem_left _ h.1, ?_, fun σ => ?_⟩
  · have : (u : 𝓞 F) * ξ - 1 = (u : 𝓞 F) * (ξ - 1) + ((u : 𝓞 F) - 1) := by ring
    rw [this]
    exact 𝔣.add_mem (𝔣.mul_mem_left _ h.2.1) hu.1
  · have e1 : (((u : 𝓞 F) * ξ : 𝓞 F) : F) = ((u : 𝓞 F) : F) * (ξ : F) := rfl
    rw [e1, map_mul]
    exact mul_pos (hu.2 σ) (h.2.2 σ)

theorem exists_nat_mul_integer (x : F) : ∃ (D : ℕ) (z : 𝓞 F), 0 < D ∧ (z : F) = (D : F) * x := by
  obtain ⟨y, hy, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic x)).exists_integral_multiple
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 F, (z : F) = y • x := ⟨⟨_, hi⟩, rfl⟩
  refine ⟨y.natAbs * y.natAbs, (y : 𝓞 F) * z, Nat.mul_pos (Int.natAbs_pos.2 hy) (Int.natAbs_pos.2 hy), ?_⟩
  have e1 : (((y : 𝓞 F) * z : 𝓞 F) : F) = (y : F) * (z : F) := by simp [RingOfIntegers.coe_eq_algebraMap]
  have e2 : ((y.natAbs * y.natAbs : ℕ) : F) = (y : F) * (y : F) := by
    have := congrArg (Int.cast : ℤ → F) (Int.natAbs_mul_self' y)
    rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast] at this
    rw [Nat.cast_mul]
    exact this
  rw [e1, hz, e2, zsmul_eq_mul]
  ring

theorem exists_scaled {𝔪 : Ideal (𝓞 F)} (h𝔪 : 𝔪 ≠ ⊥) {ι : Type} [Fintype ι] (r : ι → ℕ) (v : ∀ c, Fin (r c) → F) :
    ∃ (N : ℕ) (w : ∀ c, Fin (r c) → 𝓞 F), 0 < N ∧ ∀ c i, w c i ∈ 𝔪 ∧ (w c i : F) = (N : F) * v c i := by
  classical
  choose D z hD hz using fun c i => exists_nat_mul_integer (v c i)
  set P : ℕ := ∏ c, ∏ i, D c i with hP
  have hP0 : 0 < P := Finset.prod_pos fun c _ => Finset.prod_pos fun i _ => hD c i
  have hdvd : ∀ c i, D c i ∣ P := fun c i =>
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)).trans (Finset.dvd_prod_of_mem (fun c => ∏ i, D c i) (Finset.mem_univ c))
  choose k hk using hdvd
  set M : ℕ := Ideal.absNorm 𝔪 with hM
  have hM0 : 0 < M := Nat.pos_of_ne_zero (by simpa [hM, Ideal.absNorm_eq_zero_iff] using h𝔪)
  refine ⟨M * P, fun c i => (M : 𝓞 F) * ((k c i : 𝓞 F) * z c i), Nat.mul_pos hM0 hP0, fun c i => ⟨𝔪.mul_mem_right _ (Ideal.absNorm_mem 𝔪), ?_⟩⟩
  have e1 : (((M : 𝓞 F) * ((k c i : 𝓞 F) * z c i) : 𝓞 F) : F) = (M : F) * ((k c i : F) * (z c i : F)) := by
    simp [RingOfIntegers.coe_eq_algebraMap]
  rw [e1, hz, hk c i]
  push_cast
  ring

theorem mem_openCone_scale {r : ℕ} {v : Fin r → F} {N : ℕ} (hN : 0 < N) {u : Fin r → F} (hu : ∀ i, u i = (N : F) * v i) {x : F} :
    x ∈ openCone u ↔ x ∈ openCone v := by
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hNF : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun i => t i * N, fun i => mul_pos (ht i) hNq, Finset.sum_congr rfl fun i _ => ?_⟩
    rw [hu]
    push_cast
    ring
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun i => t i / N, fun i => div_pos (ht i) hNq, Finset.sum_congr rfl fun i _ => ?_⟩
    rw [hu]
    push_cast
    field_simp

theorem IsConeDomain.scale {𝔣 : Ideal (𝓞 F)} {ι : Type} {r : ι → ℕ} {v : ∀ c, Fin (r c) → F} (h : IsConeDomain 𝔣 r v) {N : ℕ} (hN : 0 < N)
    {u : ∀ c, Fin (r c) → F} (hu : ∀ c i, u c i = (N : F) * v c i) : IsConeDomain 𝔣 r u := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨h1, fun c => ?_, fun c i σ => ?_, fun x hx => ?_⟩
  · have := (h2 c).units_smul (fun _ => Units.mk0 (N : ℚ) hNq)
    convert this using 1
    funext i
    simp [hu, Units.smul_def, Rat.smul_def]
  · rw [hu, map_mul, map_natCast]
    exact mul_pos (by exact_mod_cast hN) (h3 c i σ)
  · simpa only [mem_openCone_scale hN (hu _)] using h4 x hx

theorem sum_coef_unique {r : ℕ} {u : Fin r → F} (h : LinearIndependent ℚ u) {t s : Fin r → ℚ}
    (e : ∑ i, (t i : F) * u i = ∑ i, (s i : F) * u i) : t = s := by
  funext i
  have := Fintype.linearIndependent_iff.1 h (fun i => t i - s i) (by
    simp only [Rat.smul_def, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib, e, sub_self]) i
  linarith

theorem frac_unique {s s' : ℚ} {m m' : ℕ} (h0 : 0 < s) (h1 : s ≤ 1) (h0' : 0 < s') (h1' : s' ≤ 1) (e : s + m = s' + m') : m = m' := by
  have a : (m : ℚ) < m' + 1 := by linarith
  have b : (m' : ℚ) < m + 1 := by linarith
  have a' : m < m' + 1 := by exact_mod_cast a
  have b' : m' < m + 1 := by exact_mod_cast b
  omega

theorem exists_frac {t : ℚ} (h : 0 < t) : ∃ (m : ℕ) (s : ℚ), 0 < s ∧ s ≤ 1 ∧ t = s + m := by
  have hc : 0 < ⌈t⌉₊ := Nat.ceil_pos.2 h
  refine ⟨⌈t⌉₊ - 1, t - ((⌈t⌉₊ - 1 : ℕ) : ℚ), ?_, ?_, by ring⟩
  · rw [Nat.cast_sub hc]
    have := Nat.ceil_lt_add_one h.le
    push_cast
    linarith
  · rw [Nat.cast_sub hc]
    have := Nat.le_ceil t
    push_cast
    linarith

theorem totPos_sum {r : ℕ} (hr : 0 < r) {u : Fin r → F} (hu : ∀ i, TotPos F (u i)) {t : Fin r → ℚ} (ht : ∀ i, 0 < t i) :
    TotPos F (∑ i, (t i : F) * u i) := fun σ => by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  rw [map_sum]
  refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
  rw [map_mul, map_ratCast]
  exact mul_pos (by exact_mod_cast ht i) (hu i σ)

def coneBox (𝔣 𝔟 : Ideal (𝓞 F)) {r : ℕ} (w : Fin r → 𝓞 F) : Set (𝓞 F) :=
  {y | RayPoint 𝔣 𝔟 y ∧ ∃ t : Fin r → ℚ, (∀ i, 0 < t i ∧ t i ≤ 1) ∧ (y : F) = ∑ i, (t i : F) * (w i : F)}

theorem coneBox_finite (𝔣 𝔟 : Ideal (𝓞 F)) {r : ℕ} (w : Fin r → 𝓞 F) : (coneBox 𝔣 𝔟 w).Finite := by
  have hB := Embeddings.finite_of_norm_le F ℂ (∑ φ : F →+* ℂ, ∑ i, ‖φ (w i : F)‖)
  refine Set.Finite.of_finite_image (f := fun y : 𝓞 F => (y : F)) (hB.subset ?_) RingOfIntegers.coe_injective.injOn
  rintro _ ⟨y, ⟨-, t, ht, e⟩, rfl⟩
  refine ⟨y.isIntegral_coe, fun φ => ?_⟩
  have h1 : ‖φ (y : F)‖ ≤ ∑ i, ‖φ (w i : F)‖ := by
    rw [e, map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_mul, map_ratCast, norm_mul, Complex.norm_ratCast]
    have : |((t i : ℚ) : ℝ)| ≤ 1 := by
      rw [abs_of_pos (by exact_mod_cast (ht i).1)]
      exact_mod_cast (ht i).2
    exact mul_le_of_le_one_left (norm_nonneg _) this
  exact h1.trans (Finset.single_le_sum (f := fun φ : F →+* ℂ => ∑ i, ‖φ (w i : F)‖)
    (fun φ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ φ))

theorem coe_add_sum {r : ℕ} (w : Fin r → 𝓞 F) {a : 𝓞 F} {t : Fin r → ℚ} (e : (a : F) = ∑ i, (t i : F) * (w i : F)) (m : Fin r → ℕ) :
    ((a + ∑ i, (m i : 𝓞 F) * w i : 𝓞 F) : F) = ∑ i, ((t i + m i : ℚ) : F) * (w i : F) := by
  have h1 : ((a + ∑ i, (m i : 𝓞 F) * w i : 𝓞 F) : F) = (a : F) + ∑ i, ((m i : ℚ) : F) * (w i : F) := by
    simp [RingOfIntegers.coe_eq_algebraMap]
  rw [h1, e, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by push_cast; ring

theorem classParam_of_scaled [IsTotallyReal F] {𝔣 𝔞 𝔟 : Ideal (𝓞 F)} {x₀ : 𝓞 F} (h𝔟 : 𝔟 ≠ ⊥) (hx0 : x₀ ≠ 0) (hx1 : x₀ - 1 ∈ 𝔣)
    (hxp : TotPos F (x₀ : F)) (hab : 𝔞 * 𝔟 = Ideal.span {x₀}) {ι : Type} [Fintype ι] {r : ι → ℕ} {w : ∀ c, Fin (r c) → 𝓞 F}
    (hdom : IsConeDomain 𝔣 r (fun c i => (w c i : F))) (hwb : ∀ c i, w c i ∈ 𝔟) (hwf : ∀ c i, w c i ∈ 𝔣) :
    ∃ (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r' y v' := by
  classical
  obtain ⟨hr, hli, hpos, hun⟩ := hdom
  haveI : ∀ c, Fintype (coneBox 𝔣 𝔟 (w c)) := fun c => (coneBox_finite 𝔣 𝔟 (w c)).fintype
  let J : Type := Σ c, coneBox 𝔣 𝔟 (w c)
  let r' : J → ℕ := fun j => r j.1
  let y : J → 𝓞 F := fun j => j.2.1
  let v' : ∀ j : J, Fin (r' j) → 𝓞 F := fun j => w j.1
  let ξ : (Σ j : J, (Fin (r' j) → ℕ)) → 𝓞 F := fun p => y p.1 + ∑ i, (p.2 i : 𝓞 F) * v' p.1 i
  have hcoef : ∀ p : (Σ j : J, (Fin (r' j) → ℕ)), ∃ t : Fin (r p.1.1) → ℚ, (∀ i, 0 < t i ∧ t i ≤ 1) ∧
      ((ξ p : 𝓞 F) : F) = ∑ i, ((t i + p.2 i : ℚ) : F) * (w p.1.1 i : F) := fun p => by
    obtain ⟨t, ht, e⟩ := p.1.2.2.2
    exact ⟨t, ht, coe_add_sum (w p.1.1) e p.2⟩
  have hcone : ∀ p : (Σ j : J, (Fin (r' j) → ℕ)), ((ξ p : 𝓞 F) : F) ∈ openCone (fun i => (w p.1.1 i : F)) := fun p => by
    obtain ⟨t, ht, e⟩ := hcoef p
    exact ⟨fun i => t i + p.2 i, fun i => add_pos_of_pos_of_nonneg (ht i).1 (Nat.cast_nonneg _), e⟩
  have hpoint : ∀ p, RayPoint 𝔣 𝔟 (ξ p) := fun p => by
    have ha := p.1.2.2.1
    refine ⟨𝔟.add_mem ha.1 (𝔟.sum_mem fun i _ => 𝔟.mul_mem_left _ (hwb _ i)), ?_, ?_⟩
    · have : ξ p - 1 = (y p.1 - 1) + ∑ i, (p.2 i : 𝓞 F) * v' p.1 i := by
        change y p.1 + ∑ i, (p.2 i : 𝓞 F) * v' p.1 i - 1 = _
        ring
      rw [this]
      exact 𝔣.add_mem ha.2.1 (𝔣.sum_mem fun i _ => 𝔣.mul_mem_left _ (hwf _ i))
    · obtain ⟨t, ht, e⟩ := hcoef p
      rw [e]
      exact totPos_sum (hr _) (hpos _) fun i => add_pos_of_pos_of_nonneg (ht i).1 (Nat.cast_nonneg _)
  have hI := fun p => (hpoint p).exists_ideal hx0 hx1 hxp hab
  choose f hf hfe using hI
  let f' : (Σ j : J, (Fin (r' j) → ℕ)) → {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} := fun p => ⟨f p, hf p⟩
  have hinj : Function.Injective f' := by
    intro p p' hpp
    have hs : Ideal.span {ξ p} = Ideal.span {ξ p'} := by
      rw [← hfe p, ← hfe p']
      exact congrArg (· * 𝔟) (congrArg Subtype.val hpp)
    obtain ⟨u, hu, hue⟩ := (hpoint p).exists_unit (hpoint p') hs
    obtain ⟨q, -, hq⟩ := hun _ (hpoint p).2.2
    have h1u : (1 : (𝓞 F)ˣ) ∈ congUnits 𝔣 := ⟨by simp, fun σ => by simp⟩
    have e1 := hq (⟨1, h1u⟩, p.1.1) (by simpa using hcone p)
    have e2 := hq (⟨u, hu⟩, p'.1.1) (by
      have := hcone p'
      rw [hue] at this
      exact this)
    have e3 := e1.trans e2.symm
    have hc : p.1.1 = p'.1.1 := congrArg Prod.snd e3
    have hu1 : u = 1 := (congrArg (fun z : congUnits 𝔣 × ι => (z.1 : (𝓞 F)ˣ)) e3).symm
    have hξ : ξ p' = ξ p := by rw [hue, hu1]; simp
    obtain ⟨t, ht, e⟩ := hcoef p
    obtain ⟨t', ht', e'⟩ := hcoef p'
    obtain ⟨⟨c, a, ha⟩, m⟩ := p
    obtain ⟨⟨c', a', ha'⟩, m'⟩ := p'
    obtain rfl : c = c' := hc
    rw [hξ] at e'
    have ht2 := sum_coef_unique (hli c) (e.symm.trans e')
    have hm : m = m' := funext fun i => frac_unique (ht i).1 (ht i).2 (ht' i).1 (ht' i).2 (congrFun ht2 i)
    subst hm
    have ha2 : a' = a := add_right_cancel hξ
    subst ha2
    rfl
  have hsurj : Function.Surjective f' := by
    rintro ⟨I, hI1, hI2⟩
    obtain ⟨ξ₀, hξ₀, hIe⟩ := RayPoint.of_ideal hx0 hx1 hxp hab hI2
    obtain ⟨⟨⟨u, hu⟩, c⟩, hmem, -⟩ := hun _ hξ₀.2.2
    obtain ⟨t, ht, e⟩ := hmem
    have h₁ := hξ₀.unit_mul hu
    have hspan : Ideal.span {(u : 𝓞 F) * ξ₀} = Ideal.span {ξ₀} :=
      Ideal.span_singleton_eq_span_singleton.2 (Associated.symm ⟨u, mul_comm _ _⟩)
    choose m s hs0 hs1 hts using fun i => exists_frac (ht i)
    set S : 𝓞 F := ∑ i, (m i : 𝓞 F) * w c i with hS
    have hSc : (S : F) = ∑ i, ((m i : ℚ) : F) * (w c i : F) := by simp [hS, RingOfIntegers.coe_eq_algebraMap]
    have hSf : S ∈ 𝔣 := 𝔣.sum_mem fun i _ => 𝔣.mul_mem_left _ (hwf c i)
    have hSb : S ∈ 𝔟 := 𝔟.sum_mem fun i _ => 𝔟.mul_mem_left _ (hwb c i)
    have ha_coe : ((((u : 𝓞 F) * ξ₀ - S : 𝓞 F)) : F) = ∑ i, (s i : F) * (w c i : F) := by
      have h3 : ((((u : 𝓞 F) * ξ₀ - S : 𝓞 F)) : F) = ((u : 𝓞 F) : F) * (ξ₀ : F) - (S : F) := by
        simp [RingOfIntegers.coe_eq_algebraMap]
      rw [h3, e, hSc, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hts i]; push_cast; ring
    have ha : RayPoint 𝔣 𝔟 ((u : 𝓞 F) * ξ₀ - S) := by
      refine ⟨𝔟.sub_mem h₁.1 hSb, ?_, ?_⟩
      · have : (u : 𝓞 F) * ξ₀ - S - 1 = ((u : 𝓞 F) * ξ₀ - 1) - S := by ring
        rw [this]
        exact 𝔣.sub_mem h₁.2.1 hSf
      · rw [ha_coe]
        exact totPos_sum (hr c) (hpos c) hs0
    let p : (Σ j : J, (Fin (r' j) → ℕ)) := ⟨⟨c, _, ha, s, fun i => ⟨hs0 i, hs1 i⟩, ha_coe⟩, m⟩
    have hp : ξ p = (u : 𝓞 F) * ξ₀ := sub_add_cancel _ _
    refine ⟨p, Subtype.ext (mul_right_cancel₀ h𝔟 ?_)⟩
    change f p * 𝔟 = I * 𝔟
    rw [hfe, hp, hspan, hIe]
  refine ⟨J, inferInstance, r', y, v', h𝔟, fun j => ⟨j.2.2.1.1, j.2.2.1.2.2⟩, fun j i => ⟨hwb _ _, hpos _ _⟩, fun j => ?_,
    Equiv.ofBijective f' ⟨hinj, hsurj⟩, fun p => hfe p⟩
  simpa using (hli j.1).fintype_card_le_finrank

theorem exists_classParam : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∀ (ι : Type) [Fintype ι] (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), IsConeDomain 𝔣 r v →
      ∀ 𝔞 : Ideal (𝓞 F), CoprimeTo F 𝔣 𝔞 →
        ∃ (𝔟 : Ideal (𝓞 F)) (J : Type) (_ : Fintype J) (r' : J → ℕ) (y : J → 𝓞 F) (v' : ∀ j, Fin (r' j) → 𝓞 F),
          ClassParam 𝔣 𝔞 𝔟 r' y v' := by
  intro F _ _ _ 𝔣 h𝔣 ι _ r v hdom 𝔞 h𝔞
  obtain ⟨𝔟, x₀, hb, hx0, hx1, hxp, hab⟩ := exists_complement h𝔣 h𝔞
  obtain ⟨N, w, hN, hw⟩ := exists_scaled (𝔪 := 𝔟 * 𝔣) (mul_ne_zero hb.1 h𝔣) r v
  have hd := hdom.scale hN (u := fun c i => (w c i : F)) (fun c i => (hw c i).2)
  obtain ⟨J, a, b, c, d, e⟩ := classParam_of_scaled hb.1 hx0 hx1 hxp hab hd
    (fun c i => (Ideal.mul_le_left : 𝔟 * 𝔣 ≤ 𝔟) (hw c i).1)
    (fun c i => (Ideal.mul_le_right : 𝔟 * 𝔣 ≤ 𝔣) (hw c i).1)
  exact ⟨𝔟, J, a, b, c, d, e⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
