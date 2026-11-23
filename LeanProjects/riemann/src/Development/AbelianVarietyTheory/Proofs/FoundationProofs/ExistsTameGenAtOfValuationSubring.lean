import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace GlobalTheory.TameInertiaGen

theorem exists_topGen {H M : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [Group M] (θ : ℕ → H →* M) (hcl : ∀ n (s : Set M), IsClosed (θ n ⁻¹' s))
    (hcyc : ∀ n, IsCyclic (θ n).range) (hker : ∀ n σ, θ (n + 1) σ = 1 → θ n σ = 1) :
    ∃ γ : H, ∀ σ : H, ∃ h ∈ closure (Subgroup.zpowers γ : Set H), ∀ n, θ n (h⁻¹ * σ) = 1 := by
  have key : ∀ n a b, θ n (a⁻¹ * b) = 1 ↔ θ n b = θ n a := by
    intro n a b
    rw [map_mul, map_inv, inv_mul_eq_one, eq_comm]
  have hker' : ∀ n a b, θ (n + 1) b = θ (n + 1) a → θ n b = θ n a := fun n a b h =>
    (key n a b).1 (hker n _ ((key _ a b).2 h))
  let S : ℕ → Set H := fun n => θ n ⁻¹' {m | ∀ σ, ∃ k : ℤ, θ n σ = m ^ k}
  obtain ⟨γ, hγ⟩ : (⋂ n, S n).Nonempty := by
    refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S ?_ ?_
      (hcl _ _).isCompact (fun n => hcl _ _)
    · intro n γ h σ
      obtain ⟨k, hk⟩ := h σ
      refine ⟨k, ?_⟩
      rw [← map_zpow] at hk ⊢
      exact hker' n _ _ hk
    · intro n
      obtain ⟨⟨_, γ, rfl⟩, hg⟩ := (hcyc n).exists_generator
      refine ⟨γ, fun σ => ?_⟩
      obtain ⟨k, hk⟩ := hg ⟨θ n σ, σ, rfl⟩
      exact ⟨k, (congrArg Subtype.val hk).symm⟩
  refine ⟨γ, fun σ => ?_⟩
  let T : ℕ → Set H := fun n => closure (Subgroup.zpowers γ : Set H) ∩ θ n ⁻¹' {θ n σ}
  obtain ⟨h, hh⟩ : (⋂ n, T n).Nonempty := by
    refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed T ?_ ?_
      (isClosed_closure.inter (hcl _ _)).isCompact (fun n => isClosed_closure.inter (hcl _ _))
    · intro n h hh
      exact ⟨hh.1, hker' n _ _ hh.2⟩
    · intro n
      obtain ⟨k, hk⟩ := Set.mem_iInter.1 hγ n σ
      exact ⟨γ ^ k, subset_closure ⟨k, rfl⟩, by simp [hk]⟩
  rw [Set.mem_iInter] at hh
  exact ⟨h, (hh 0).1, fun n => (key n _ _).2 (hh n).2.symm⟩

theorem exists_nat_gen {Ω : Type*} [Field Ω] [CharZero Ω] (A : ValuationSubring Ω) :
    ∃ p : ℕ, p ≠ 0 ∧ ∀ a : ℕ, a ≠ 0 → ∃ k : ℕ, A.valuation (a : Ω) = A.valuation (p : Ω) ^ k := by
  have hle : ∀ z : ℤ, A.valuation (z : Ω) ≤ 1 := fun z =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A z)
  obtain ⟨p, hp0, hp⟩ : ∃ p : ℕ, p ≠ 0 ∧ ∀ q : ℕ, q.Prime → q = p ∨ A.valuation (q : Ω) = 1 := by
    by_cases h : ∃ p : ℕ, p.Prime ∧ A.valuation (p : Ω) < 1
    · obtain ⟨p, hp, hv⟩ := h
      refine ⟨p, hp.ne_zero, fun q hq => ?_⟩
      by_contra hc
      rw [not_or] at hc
      have hq1 : A.valuation (q : Ω) < 1 := lt_of_le_of_ne (by simpa using hle q) hc.2
      obtain ⟨x, y, hxy⟩ : IsCoprime (q : ℤ) (p : ℤ) :=
        Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 hc.1)
      have e : (x : Ω) * q + (y : Ω) * p = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hxy
      have : A.valuation ((x : Ω) * q + (y : Ω) * p) < 1 := by
        refine Valuation.map_add_lt _ ?_ ?_
        · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (hle x) zero_le hq1
        · rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right (hle y) zero_le hv
      rw [e, map_one] at this
      exact lt_irrefl _ this
    · refine ⟨1, one_ne_zero, fun q hq => Or.inr ?_⟩
      exact le_antisymm (by simpa using hle q) (not_lt.1 fun h' => h ⟨q, hq, h'⟩)
  refine ⟨p, hp0, fun a => ?_⟩
  induction a using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _; exact ⟨0, by simp⟩
  | prime q hq =>
    intro _
    rcases hp q hq with rfl | h
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp [h]⟩
  | mul a b ha hb =>
    intro h
    obtain ⟨k, hk⟩ := ha (left_ne_zero_of_mul h)
    obtain ⟨l, hl⟩ := hb (right_ne_zero_of_mul h)
    exact ⟨k + l, by rw [Nat.cast_mul, map_mul, hk, hl, pow_add]⟩

theorem exists_pow_eq {Ω : Type*} [Field Ω] [CharZero Ω] (A : ValuationSubring Ω) {p : ℕ} (hp0 : p ≠ 0)
    (hp : ∀ a : ℕ, a ≠ 0 → ∃ k : ℕ, A.valuation (a : Ω) = A.valuation (p : Ω) ^ k)
    {y : Ω} (hy0 : y ≠ 0) (hy : IsAlgebraic ℤ y) :
    ∃ (m : ℕ) (k : ℤ), m ≠ 0 ∧ A.valuation y ^ m = A.valuation (p : Ω) ^ k := by
  obtain ⟨f, hf0, hf⟩ := hy
  have hz : ∀ a : ℤ, a ≠ 0 → ∃ k : ℕ, A.valuation (a : Ω) = A.valuation (p : Ω) ^ k := by
    intro a ha
    obtain ⟨k, hk⟩ := hp a.natAbs (Int.natAbs_ne_zero.2 ha)
    refine ⟨k, ?_⟩
    rw [← hk]
    rcases Int.natAbs_eq a with h | h
    · conv_lhs => rw [h]
      simp
    · conv_lhs => rw [h]
      simp
  have hvy : A.valuation y ≠ 0 := by simpa using hy0
  have hvp : A.valuation (p : Ω) ≠ 0 := by simpa using hp0
  let t : ℕ → Ω := fun i => (f.coeff i : Ω) * y ^ i
  have hsum : ∑ i ∈ f.support, t i = 0 := by
    rw [← hf, Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    simp [t]
  obtain ⟨i, hi, hmax⟩ := f.support.exists_max_image (fun i => A.valuation (t i))
    (Polynomial.support_nonempty.2 hf0)
  have hti : ∀ i ∈ f.support, A.valuation (t i) ≠ 0 := by
    intro i hi
    have := Polynomial.mem_support_iff.1 hi
    simp [t, this, hy0]
  obtain ⟨j, hj, hji, he⟩ : ∃ j ∈ f.support, j ≠ i ∧ A.valuation (t j) = A.valuation (t i) := by
    by_contra hc
    push Not at hc
    have h1 : A.valuation (∑ j ∈ f.support.erase i, t j) < A.valuation (t i) :=
      Valuation.map_sum_lt _ (hti i hi) fun j hj =>
        lt_of_le_of_ne (hmax j (Finset.mem_of_mem_erase hj))
          (hc j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj))
    rw [← Finset.add_sum_erase _ _ hi, add_eq_zero_iff_eq_neg] at hsum
    rw [hsum, Valuation.map_neg] at h1
    exact lt_irrefl _ h1
  have main : ∀ i ∈ f.support, ∀ j ∈ f.support, i < j → A.valuation (t j) = A.valuation (t i) →
      ∃ (m : ℕ) (k : ℤ), m ≠ 0 ∧ A.valuation y ^ m = A.valuation (p : Ω) ^ k := by
    intro i hi j hj hij he
    obtain ⟨a, ha⟩ := hz _ (Polynomial.mem_support_iff.1 hi)
    obtain ⟨b, hb⟩ := hz _ (Polynomial.mem_support_iff.1 hj)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hij
    refine ⟨m + 1, (a : ℤ) - b, by omega, ?_⟩
    simp only [t, map_mul, map_pow, ha, hb] at he
    rw [zpow_sub₀ hvp, zpow_natCast, zpow_natCast, eq_div_iff (pow_ne_zero _ hvp)]
    apply mul_right_cancel₀ (pow_ne_zero i hvy)
    rw [← he, add_assoc, pow_add (A.valuation y) i]
    ac_rfl
  rcases lt_or_gt_of_ne hji with h | h
  · exact main j hj i hi h he.symm
  · exact main i hi j hj h he

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

noncomputable def cob (σ : G E Ω) : Ωˣ →* Ωˣ :=
  Units.map (σ : Ω →* Ω) / MonoidHom.id Ωˣ

omit [NumberField E] in
theorem coe_cob (σ : G E Ω) (y : Ωˣ) : (cob σ y : Ω) = σ y / y := by
  simp [cob]

omit [NumberField E] in
theorem cob_mul (σ τ : G E Ω) (y : Ωˣ) : cob (σ * τ) y = cob σ (cob τ y) * cob σ y * cob τ y := by
  ext
  have h1 : (y : Ω) ≠ 0 := y.ne_zero
  have h2 : σ (y : Ω) ≠ 0 := by simpa using h1
  have h3 : τ (y : Ω) ≠ 0 := by simpa using h1
  simp only [Units.val_mul, coe_cob, AlgEquiv.mul_apply, map_div₀]
  field_simp

theorem cob_mem_of_unit {A : ValuationSubring Ω} {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) {u : Ωˣ}
    (hu : A.valuation (u : Ω) = 1) : cob σ u ∈ A.principalUnitGroup := by
  rw [ValuationSubring.mem_principalUnitGroup_iff, coe_cob, div_sub_one u.ne_zero, map_div₀, hu, div_one]
  exact hσ.2 _ hu.le

theorem cob_mem_of_zpow {A : ValuationSubring Ω} {σ : G E Ω} (hσ : σ ∈ Ine (F := E) A) {r y : Ωˣ} {k : ℤ}
    (hr : cob σ r ∈ A.principalUnitGroup) (hy : A.valuation (y : Ω) = A.valuation (r : Ω) ^ k) :
    cob σ y ∈ A.principalUnitGroup := by
  have e : y = (y / r ^ k) * r ^ k := by simp
  rw [e, map_mul, map_zpow]
  refine mul_mem (cob_mem_of_unit hσ ?_) (zpow_mem hr k)
  have h : A.valuation (r : Ω) ^ k ≠ 0 := zpow_ne_zero _ (by simp)
  simp [hy, h]

omit [NumberField E] in
theorem cob_pow_eq_one (σ : G E Ω) {r : Ωˣ} {N p : ℕ} (hr : (r : Ω) ^ N = p) : cob σ r ^ N = 1 := by
  rw [← map_pow]
  ext
  rw [coe_cob, Units.val_pow_eq_pow_val, hr, map_natCast, div_self (hr ▸ pow_ne_zero _ r.ne_zero), Units.val_one]

noncomputable def tameChar (A : ValuationSubring Ω) {r : Ωˣ} {N p : ℕ} (hN : N ≠ 0) (hr : (r : Ω) ^ N = p) :
    Ine (F := E) A →* Ωˣ ⧸ A.principalUnitGroup :=
  MonoidHom.mk' (fun σ => QuotientGroup.mk (cob σ.1 r)) fun σ τ => by
    have h : cob σ.1 (cob τ.1 r) ∈ A.principalUnitGroup :=
      cob_mem_of_unit σ.2 (valuation_eq_one_of_pow_eq_one A hN (by
        rw [← Units.val_pow_eq_pow_val, cob_pow_eq_one τ.1 hr, Units.val_one]))
    rw [Subgroup.coe_mul, cob_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).2 h, one_mul]

theorem tameChar_eq_one {A : ValuationSubring Ω} {r : Ωˣ} {N p : ℕ} (hN : N ≠ 0) (hr : (r : Ω) ^ N = p)
    (σ : Ine (F := E) A) : tameChar A hN hr σ = 1 ↔ cob σ.1 r ∈ A.principalUnitGroup :=
  QuotientGroup.eq_one_iff _

theorem isCyclic_range (A : ValuationSubring Ω) {r : Ωˣ} {N p : ℕ} (hN : N ≠ 0) (hr : (r : Ω) ^ N = p) :
    IsCyclic (tameChar (E := E) A hN hr).range := by
  have : NeZero N := ⟨hN⟩
  have : IsCyclic ((rootsOfUnity N Ω).map (QuotientGroup.mk' A.principalUnitGroup)) :=
    isCyclic_of_surjective _ ((QuotientGroup.mk' A.principalUnitGroup).subgroupMap_surjective _)
  refine Subgroup.isCyclic_of_le (H' := (rootsOfUnity N Ω).map (QuotientGroup.mk' A.principalUnitGroup)) ?_
  rintro _ ⟨σ, rfl⟩
  exact ⟨cob σ.1 r, cob_pow_eq_one σ.1 hr, rfl⟩

theorem isClosed_preimage [IsAlgClosure E Ω] (A : ValuationSubring Ω) {r : Ωˣ} {N p : ℕ} (hN : N ≠ 0)
    (hr : (r : Ω) ^ N = p) (s : Set (Ωˣ ⧸ A.principalUnitGroup)) :
    IsClosed (tameChar (E := E) A hN hr ⁻¹' s) := by
  have h := (isClosed_setOf_apply (F := E) (r : Ω)
    (fun t => ∃ u : Ωˣ, (u : Ω) = t / r ∧ QuotientGroup.mk u ∈ s)).preimage
      (continuous_subtype_val (p := fun σ : G E Ω => σ ∈ Ine (F := E) A))
  convert h using 1
  ext σ
  constructor
  · intro h
    exact ⟨cob σ.1 r, coe_cob _ _, h⟩
  · rintro ⟨u, hu, h⟩
    have : u = cob σ.1 r := Units.ext (hu.trans (coe_cob _ _).symm)
    subst this
    exact h

theorem exists_tameGenAt_of_valuationSubring [IsAlgClosure E Ω] (A : ValuationSubring Ω) :
    ∃ γ : G E Ω, TameGenAt A γ := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : IsGalois E Ω := {}
  have : CompactSpace (Ine (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  obtain ⟨p, hp0, hp⟩ := exists_nat_gen A
  have hroot : ∀ n : ℕ, ∃ r : Ωˣ, (r : Ω) ^ n.factorial = p := by
    intro n
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (p : Ω) n.factorial_pos
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow n.factorial_ne_zero] at hz
      exact hp0 (by exact_mod_cast hz.symm)
    exact ⟨Units.mk0 z hz0, hz⟩
  choose r hr using hroot
  have hvr : ∀ n, A.valuation (p : Ω) = A.valuation (r n : Ω) ^ (n.factorial : ℤ) := fun n => by
    rw [← hr n, map_pow, zpow_natCast]
  obtain ⟨γ, hγ⟩ := exists_topGen (fun n => tameChar (E := E) A n.factorial_ne_zero (hr n))
    (fun n s => isClosed_preimage A _ _ s) (fun n => isCyclic_range A _ _) (fun n σ h => by
      rw [tameChar_eq_one] at h ⊢
      refine cob_mem_of_zpow σ.2 (k := (n + 1 : ℕ)) h ?_
      rw [zpow_natCast, ← pow_left_inj₀ zero_le zero_le n.factorial_ne_zero, ← pow_mul, ← Nat.factorial_succ,
        ← map_pow, ← map_pow, hr, hr])
  refine ⟨γ.1, γ.2, fun σ hσ => ?_⟩
  obtain ⟨h, hh, hw⟩ := hγ ⟨σ, hσ⟩
  set C : Subgroup (G E Ω) :=
    Subgroup.closure (insert γ.1 {σ : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}) with hC
  have h1 : h.1 ∈ C.topologicalClosure := by
    refine closure_mono ?_ (image_closure_subset_closure_image continuous_subtype_val ⟨h, hh, rfl⟩)
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact zpow_mem (Subgroup.subset_closure (Set.mem_insert _ _) : γ.1 ∈ C) k
  have h2 : h.1⁻¹ * σ ∈ C := by
    refine Subgroup.subset_closure (Set.mem_insert_of_mem _ fun y hy => ?_)
    have halg : IsAlgebraic ℤ y := by
      have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
      exact (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic y)
    obtain ⟨m, k, hm, hk⟩ := exists_pow_eq A hp0 hp hy halg
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    have := cob_mem_of_zpow (y := Units.mk0 y hy) (k := (m.factorial : ℤ) * k) (h⁻¹ * ⟨σ, hσ⟩).2
      ((tameChar_eq_one _ _ _).1 (hw (m + 1))) (by
        rw [Units.val_mk0, ← pow_left_inj₀ zero_le zero_le hm, hk, hvr (m + 1), ← zpow_natCast, ← zpow_mul,
          ← zpow_mul, Nat.factorial_succ]
        congr 1
        push_cast
        ring)
    rw [ValuationSubring.mem_principalUnitGroup_iff, coe_cob] at this
    exact this
  have h3 := C.topologicalClosure.mul_mem h1 (C.le_topologicalClosure h2)
  rw [mul_inv_cancel_left] at h3
  exact h3

end

theorem exists_tameGenAt : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v → ∃ γ : G E Ω, TameGenAt A γ :=
  fun _ _ _ _ _ _ _ _ A _ => exists_tameGenAt_of_valuationSubring A

end GlobalTheory.TameInertiaGen
