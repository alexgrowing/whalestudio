import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem withZero_eq_of_le_exp_iff {a b : ℤᵐ⁰} (ha : a ≤ 1) (hb : b ≤ 1)
    (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) : a = b := by
  have key : ∀ a b : ℤᵐ⁰, b ≠ 0 → b ≤ 1 →
      (∀ n : ℕ, b ≤ WithZero.exp (-(n : ℤ)) → a ≤ WithZero.exp (-(n : ℤ))) → a ≤ b := by
    intro a b hb0 hb h
    have e : b = WithZero.exp (WithZero.log b) := (WithZero.exp_log hb0).symm
    have hl : WithZero.log b ≤ 0 := by
      rw [e, ← WithZero.exp_zero, WithZero.exp_le_exp] at hb; exact hb
    have e2 : WithZero.log b = -(((-WithZero.log b).toNat : ℕ) : ℤ) := by omega
    rw [e2] at e
    rw [e]
    exact h _ e.le
  have key0 : ∀ a : ℤᵐ⁰, (∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ))) → a = 0 := by
    intro a h
    by_contra ha0
    have e : a = WithZero.exp (WithZero.log a) := (WithZero.exp_log ha0).symm
    have := h ((-WithZero.log a).toNat + 1)
    rw [e, WithZero.exp_le_exp, WithZero.log_exp] at this
    omega
  by_cases hb0 : b = 0
  · subst hb0
    exact key0 a fun n => (h n).2 (by simp)
  by_cases ha0 : a = 0
  · subst ha0
    exact (key0 b fun n => (h n).1 (by simp)).symm
  exact le_antisymm (key a b hb0 hb fun n => (h n).2) (key b a ha0 ha fun n => (h n).1)

open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.intValuation_of_eq_comap {R : Type} [CommRing R] [IsDedekindDomain R]
    (e : R ≃+* R) (w w' : HeightOneSpectrum R) (h : w'.asIdeal = w.asIdeal.comap e) (x : R) :
    w'.intValuation x = w.intValuation (e x) := by
  have hmem : ∀ n : ℕ, x ∈ w'.asIdeal ^ n ↔ e x ∈ w.asIdeal ^ n := by
    intro n
    rw [h, ← Ideal.map_symm, ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap]
  have hle : ∀ n : ℕ, w'.intValuation x ≤ WithZero.exp (-(n : ℤ)) ↔
      w.intValuation (e x) ≤ WithZero.exp (-(n : ℤ)) := fun n => by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem,
      HeightOneSpectrum.intValuation_le_pow_iff_mem, hmem]
  by_cases hx : x = 0
  · subst hx
    simp
  · have hex : e x ≠ 0 := fun h0 => hx (e.injective (h0.trans (map_zero e).symm))
    rw [HeightOneSpectrum.intValuation_if_neg _ hx, HeightOneSpectrum.intValuation_if_neg _ hex]
      at hle ⊢
    set a := (Associates.mk w'.asIdeal).count (Associates.mk (Ideal.span {x})).factors
    set b := (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {e x})).factors
    have h1 := (hle a).1 le_rfl
    have h2 := (hle b).2 le_rfl
    simp only [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le] at h1 h2
    rw [le_antisymm h1 h2]

open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.valuation_of_eq_comap {E : Type} [Field E] [NumberField E] (σ : E ≃+* E)
    (w w' : HeightOneSpectrum (𝓞 E))
    (h : w'.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ)) (y : E) :
    w'.valuation E y = w.valuation E (σ y) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
  have hσ : ∀ r : 𝓞 E, σ (algebraMap (𝓞 E) E r) =
      algebraMap (𝓞 E) E (RingOfIntegers.mapRingEquiv σ r) := fun r => rfl
  rw [map_div₀ σ, hσ, hσ, map_div₀, map_div₀]
  simp only [HeightOneSpectrum.valuation_of_algebraMap]
  rw [_root_.GlobalTheory.QNorm.intValuation_of_eq_comap _ w w' h a,
    _root_.GlobalTheory.QNorm.intValuation_of_eq_comap _ w w' h b]

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma ringOfIntegers_mapRingEquiv_algebraMap {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : 𝓞 F) :
    RingOfIntegers.mapRingEquiv (σ : E ≃+* E) (algebraMap (𝓞 F) (𝓞 E) n) =
      algebraMap (𝓞 F) (𝓞 E) n := by
  ext
  rw [show ((algebraMap (𝓞 F) (𝓞 E) n : 𝓞 E) : E) = algebraMap F E (n : F) from rfl]
  exact σ.commutes _

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma exists_algebraMap_eq_mul_conj_of_isQuad {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E}
    (hq : _root_.GlobalTheory.QNorm.IsQuad δ θ σ) (x : 𝓞 E) :
    ∃ n : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) n = x * RingOfIntegers.mapRingEquiv (σ : E ≃+* E) x := by
  obtain ⟨a, b, hab⟩ := hq.span (x : E)
  have hprod : (x : E) * σ (x : E) = algebraMap F E (a ^ 2 - b ^ 2 * δ) := by
    rw [hab]
    simp only [map_add, map_mul, AlgEquiv.commutes, hq.conj]
    rw [map_sub, map_mul, map_pow, map_pow, ← hq.sq]
    ring
  have hint : IsIntegral ℤ (algebraMap F E (a ^ 2 - b ^ 2 * δ)) := by
    rw [← hprod]
    exact (RingOfIntegers.isIntegral_coe x).mul
      (RingOfIntegers.isIntegral_coe (RingOfIntegers.mapRingEquiv (σ : E ≃+* E) x))
  refine ⟨⟨a ^ 2 - b ^ 2 * δ,
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F E) (algebraMap F E).injective).mp hint⟩, ?_⟩
  ext
  exact hprod.symm

open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.conj_places_transitive : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), _root_.GlobalTheory.QNorm.IsQuad δ θ σ →
    (∀ w : HeightOneSpectrum (𝓞 E), ∃ w' : HeightOneSpectrum (𝓞 E),
      w'.under (𝓞 F) = w.under (𝓞 F) ∧ ∀ y : E, w'.valuation E y = w.valuation E (σ y)) ∧
    ∀ w w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) →
      w' = w ∨ ∀ y : E, w'.valuation E y = w.valuation E (σ y) := by
  intro F E _ _ _ _ _ δ θ σ hq
  set e := RingOfIntegers.mapRingEquiv (σ : E ≃+* E) with he
  refine ⟨fun w => ?_, fun w w' hunder => ?_⟩
  · refine ⟨HeightOneSpectrum.comap (e : 𝓞 E →+* 𝓞 E) e.surjective w, ?_, fun y =>
      _root_.GlobalTheory.QNorm.valuation_of_eq_comap (σ : E ≃+* E) w _ rfl y⟩
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal]
    ext n
    change e (algebraMap (𝓞 F) (𝓞 E) n) ∈ w.asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) n ∈ w.asIdeal
    rw [he, ringOfIntegers_mapRingEquiv_algebraMap]
  · by_cases hw : w' = w
    · exact Or.inl hw
    right
    refine _root_.GlobalTheory.QNorm.valuation_of_eq_comap (σ : E ≃+* E) w w' ?_
    by_contra hne
    have h1 : ¬ w'.asIdeal ≤ w.asIdeal := fun hle =>
      hw (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top hle))
    have h2 : ¬ w'.asIdeal ≤ w.asIdeal.comap e := fun hle =>
      hne (w'.isMaximal.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) hle)
    have hns : ¬ ((w'.asIdeal : Set (𝓞 E)) ⊆ (w.asIdeal : Set (𝓞 E)) ∪ (w.asIdeal.comap e)) :=
      fun hs => (Ideal.subset_union.mp hs).elim h1 h2
    rw [Set.not_subset] at hns
    obtain ⟨x, hx, hxn⟩ := hns
    simp only [Set.mem_union, SetLike.mem_coe, Ideal.mem_comap, not_or] at hxn
    obtain ⟨n, hn⟩ := exists_algebraMap_eq_mul_conj_of_isQuad hq x
    have hnw' : n ∈ (w'.under (𝓞 F)).asIdeal := by
      rw [HeightOneSpectrum.under_asIdeal]
      change algebraMap (𝓞 F) (𝓞 E) n ∈ w'.asIdeal
      rw [hn]
      exact Ideal.mul_mem_right _ _ hx
    rw [hunder, HeightOneSpectrum.under_asIdeal] at hnw'
    change algebraMap (𝓞 F) (𝓞 E) n ∈ w.asIdeal at hnw'
    rw [hn] at hnw'
    rcases w.isPrime.mem_or_mem hnw' with h | h
    · exact hxn.1 h
    · exact hxn.2 h

end GlobalTheory.QNorm
