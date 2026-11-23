import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayHomCompAlgebraMap
open GlobalTheory.AffineCurveNbhd

noncomputable section

namespace GlobalTheory.LocDivEtale

open IsLocalRing

theorem span_singleton_eq_maximalIdeal_pow {L : Type} [CommRing L] [IsLocalRing L] [IsNoetherianRing L] (π : L)
    (hπ : maximalIdeal L = Ideal.span {π}) (x : L) (hx : x ≠ 0) :
    ∃ n : ℕ, Ideal.span {x} = maximalIdeal L ^ n := by
  classical
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal L) (maximalIdeal.isMaximal L).ne_top
  have hex : ∃ n, x ∉ maximalIdeal L ^ (n + 1) := by
    by_contra h
    push_neg at h
    apply hx
    have : x ∈ ⨅ i, maximalIdeal L ^ i := by
      rw [Ideal.mem_iInf]; intro i
      cases i with
      | zero => simp
      | succ k => exact h k
    rw [hK] at this; exact this
  obtain ⟨n, hn, hn'⟩ : ∃ n, x ∉ maximalIdeal L ^ (n + 1) ∧ x ∈ maximalIdeal L ^ n := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; simp
    · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      push_neg at this
      rwa [Nat.sub_add_cancel hpos] at this
  clear hex
  refine ⟨n, ?_⟩
  rw [hπ, Ideal.span_singleton_pow] at hn' hn ⊢
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hn'
  have hyu : IsUnit y := by
    by_contra hy'
    apply hn
    have : y ∈ maximalIdeal L := (mem_maximalIdeal _).2 hy'
    rw [hπ] at this
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 this
    rw [Ideal.mem_span_singleton']
    exact ⟨z, by rw [← hy, ← hz]; ring⟩
  rw [← hy]
  exact Ideal.span_singleton_mul_left_unit hyu _

theorem exists_local_uniformizer (B : Type) [CommRing B] [IsDedekindDomain B] (m : Ideal B) [m.IsPrime]
    (hm0 : m ≠ ⊥) : ∃ π ∈ m, ∀ b ∈ m, ∃ t ∉ m, ∃ c : B, t * b = π * c := by
  haveI : IsDiscreteValuationRing (Localization.AtPrime m) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hm0 _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime m)
  obtain ⟨⟨π, t⟩, hπt⟩ := IsLocalization.surj m.primeCompl ϖ
  simp only at hπt
  have hmax := hϖ.maximalIdeal_eq
  refine ⟨π, ?_, ?_⟩
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m, ← hπt]
    exact Ideal.mul_mem_right _ _ (hϖ.not_isUnit)
  · intro b hb
    have hb' : algebraMap B (Localization.AtPrime m) b ∈ maximalIdeal (Localization.AtPrime m) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime m) m b).2 hb
    rw [hmax] at hb'
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hb'
    obtain ⟨⟨c, u⟩, hcu⟩ := IsLocalization.surj m.primeCompl z
    simp only at hcu
    have heq : algebraMap B (Localization.AtPrime m) (b * (t * u)) =
        algebraMap B (Localization.AtPrime m) (π * c) := by
      rw [map_mul, map_mul, map_mul, ← hz, ← hπt, ← hcu]; ring
    obtain ⟨w, hw⟩ := (IsLocalization.eq_iff_exists m.primeCompl (Localization.AtPrime m)).1 heq
    refine ⟨w * (t * u), ?_, w * c, ?_⟩
    · exact (m.primeCompl).mul_mem w.2 ((m.primeCompl).mul_mem t.2 u.2)
    · rw [show (w : B) * (t * u) * b = w * (b * (t * u)) by ring, hw]; ring

theorem exists_dvd_mul_pow : ∀ (B A' : Type) [CommRing B] [IsDedekindDomain B] [CommRing A'] [Algebra B A']
    [Algebra.Etale B A'] (f : B), f ≠ 0 → IsNbhd B A' f → ∀ a ∈ nonZeroDivisors A', ∀ M : Ideal A', M.IsMaximal →
    algebraMap B A' f ∈ M → ∃ s ∉ M, ∃ N : ℕ, a ∣ s * algebraMap B A' f ^ N := by
  intro B A' _ _ _ _ _ f hf hN a ha M hM hfM
  classical
  set m : Ideal B := M.comap (algebraMap B A') with hm_def
  haveI : m.IsPrime := Ideal.comap_isPrime _ _
  have hfm : f ∈ m := hfM
  have hm0 : m ≠ ⊥ := by
    intro h; apply hf
    rw [h] at hfm; exact (Submodule.mem_bot _).1 hfm
  obtain ⟨π, hπm, hπ⟩ := exists_local_uniformizer B m hm0
  let L := Localization.AtPrime M
  haveI : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing B A'
  haveI : IsNoetherianRing L := IsLocalization.isNoetherianRing M.primeCompl L inferInstance
  let φ : B →+* L := (algebraMap A' L).comp (algebraMap B A')
  have hmem : ∀ b ∈ m, φ b ∈ Ideal.span {φ π} := by
    intro b hb
    obtain ⟨t, ht, c, htc⟩ := hπ b hb
    have hu : IsUnit (φ t) := IsLocalization.map_units L (⟨algebraMap B A' t, ht⟩ : M.primeCompl)
    refine (Ideal.unit_mul_mem_iff_mem _ hu).1 ?_
    rw [← map_mul, htc, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hmax : maximalIdeal L = Ideal.span {φ π} := by
    apply le_antisymm
    · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      intro x hx
      obtain ⟨b, hb⟩ := hN.1 x
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hb
      have hbm : b ∈ m := by
        show algebraMap B A' b ∈ M
        have : algebraMap B A' b = x - c * algebraMap B A' f := by rw [hc]; ring
        rw [this]; exact M.sub_mem hx (M.mul_mem_left _ hfM)
      have hx' : x = algebraMap B A' b + c * algebraMap B A' f := by rw [hc]; ring
      show algebraMap A' L x ∈ Ideal.span {φ π}
      rw [hx', map_add, map_mul]
      exact Ideal.add_mem _ (hmem b hbm) (Ideal.mul_mem_left _ _ (hmem f hfm))
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L M _).2 hπm
  have ha0 : algebraMap A' L a ≠ 0 := by
    intro h
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff M.primeCompl L a).1 h
    have : (s : A') = 0 := (mem_nonZeroDivisors_iff.1 ha).2 _ hs
    exact s.2 (this ▸ M.zero_mem)
  obtain ⟨n, hn⟩ := span_singleton_eq_maximalIdeal_pow (φ π) hmax _ ha0
  have hfL : φ f ^ n ∈ Ideal.span {algebraMap A' L a} := by
    rw [hn]; exact Ideal.pow_mem_pow ((IsLocalization.AtPrime.to_map_mem_maximal_iff L M _).2 hfM) n
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hfL
  obtain ⟨⟨y, s⟩, hys⟩ := IsLocalization.surj M.primeCompl z
  simp only at hys
  have heq : algebraMap A' L (algebraMap B A' f ^ n * s) = algebraMap A' L (y * a) := by
    rw [map_mul, map_mul, map_pow, ← hys]
    show φ f ^ n * _ = _
    rw [← hz]; ring
  obtain ⟨w, hw⟩ := (IsLocalization.eq_iff_exists M.primeCompl L).1 heq
  refine ⟨w * s, (M.primeCompl).mul_mem w.2 s.2, n, w * y, ?_⟩
  rw [show (w : A') * s * algebraMap B A' f ^ n = w * (algebraMap B A' f ^ n * s) by ring, hw]; ring

end GlobalTheory.LocDivEtale
