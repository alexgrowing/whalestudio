import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem finrank_quotient_eq_add_finrank_ker_factor (κ Λ : Type) [Field κ] [CommRing Λ] [Algebra κ Λ]
    [Module.Finite κ Λ] (I J : Ideal Λ) (h : I ≤ J) :
    Module.finrank κ (Λ ⧸ I) = Module.finrank κ (Λ ⧸ J) +
      Module.finrank κ (LinearMap.ker (Ideal.Quotient.factorₐ κ h).toLinearMap) := by
  haveI : Module.Finite κ (Λ ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ κ I).toLinearMap Ideal.Quotient.mk_surjective
  have hs : Function.Surjective (Ideal.Quotient.factorₐ κ h).toLinearMap :=
    Ideal.Quotient.factor_surjective h
  rw [← LinearMap.finrank_range_add_finrank_ker (Ideal.Quotient.factorₐ κ h).toLinearMap,
    LinearMap.range_eq_top.mpr hs, finrank_top]

set_option maxHeartbeats 400000 in
private theorem ideal_eq_span_pow_of_finrank (κ Λ : Type) [Field κ] [CommRing Λ] [IsLocalRing Λ] [Algebra κ Λ]
    [Module.Finite κ Λ] (ε : Λ →ₐ[κ] κ) (t : Λ)
    (ht : IsLocalRing.maximalIdeal Λ = Ideal.span {t}) (q : ℕ) :
    ∀ J : Ideal Λ, Module.finrank κ (Λ ⧸ J) = q → J = Ideal.span {t ^ q} := by
  classical
  intro J hJ
  haveI : IsArtinianRing Λ := IsArtinianRing.of_finite κ Λ
  haveI hfin : ∀ I : Ideal Λ, Module.Finite κ (Λ ⧸ I) := fun I ↦
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ κ I).toLinearMap Ideal.Quotient.mk_surjective
  have tm : t ∈ IsLocalRing.maximalIdeal Λ := by
    rw [ht]
    exact Ideal.subset_span rfl
  have mem_m : ∀ a, a ∈ IsLocalRing.maximalIdeal Λ ↔ ∃ b, b * t = a := fun a ↦ by
    rw [ht, Ideal.mem_span_singleton']
  have mem_pow : ∀ k x, x ∈ Ideal.span {t ^ k} ↔ ∃ a, a * t ^ k = x := fun k x ↦
    Ideal.mem_span_singleton'
  have unit_of : ∀ a : Λ, a ∉ IsLocalRing.maximalIdeal Λ → IsUnit a := fun a ha ↦ by
    by_contra hu
    exact ha ((IsLocalRing.mem_maximalIdeal a).2 hu)
  have hker : ∀ a : Λ, a - algebraMap κ Λ (ε a) ∈ IsLocalRing.maximalIdeal Λ := by
    intro a
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map ε
    simp at this
  have dec : ∀ a : Λ, ∃ b, a = algebraMap κ Λ (ε a) + b * t := by
    intro a
    obtain ⟨b, hb⟩ := (mem_m _).1 (hker a)
    exact ⟨b, by rw [hb]; ring⟩
  have drop : ∀ k, t ^ k ∈ Ideal.span {t ^ (k + 1)} → t ^ k = 0 := by
    intro k hk
    obtain ⟨a, ha⟩ := (mem_pow _ _).1 hk
    have hu : IsUnit (1 - a * t) := unit_of _ (fun h ↦ by
      have h1 : (1 : Λ) ∈ IsLocalRing.maximalIdeal Λ := by
        have := (IsLocalRing.maximalIdeal Λ).add_mem h
          ((IsLocalRing.maximalIdeal Λ).mul_mem_left a tm)
        simpa using this
      exact (IsLocalRing.mem_maximalIdeal _).1 h1 isUnit_one)
    have e : t ^ k * (1 - a * t) = 0 := by
      calc t ^ k * (1 - a * t) = t ^ k - a * t ^ (k + 1) := by ring
        _ = 0 := by rw [ha, sub_self]
    exact hu.mul_left_eq_zero.1 e
  have hNex : ∃ N, t ^ N = 0 := by
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := Λ)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, ht] at hN
    refine ⟨N, ?_⟩
    have h := Ideal.pow_mem_pow (Ideal.subset_span rfl : t ∈ Ideal.span {t}) N
    rw [hN] at h
    simpa using h
  obtain ⟨n, hn, hlt⟩ : ∃ n, t ^ n = 0 ∧ ∀ k < n, t ^ k ≠ 0 :=
    ⟨Nat.find hNex, Nat.find_spec hNex, fun k hk ↦ Nat.find_min hNex hk⟩
  have dimB : ∀ k ≤ n, Module.finrank κ (Λ ⧸ Ideal.span {t ^ k}) = k := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [pow_zero, Ideal.span_singleton_one]
      haveI : Subsingleton (Λ ⧸ (⊤ : Ideal Λ)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      exact Module.finrank_zero_of_subsingleton
    | succ k ih =>
      intro hk
      have hle : Ideal.span {t ^ (k + 1)} ≤ Ideal.span {t ^ k} :=
        Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow t (Nat.le_succ k))
      rw [finrank_quotient_eq_add_finrank_ker_factor κ Λ _ _ hle, ih (by omega)]
      congr 1
      set v := Ideal.Quotient.mk (Ideal.span {t ^ (k + 1)}) (t ^ k) with hv
      apply le_antisymm
      · have hsub : LinearMap.ker (Ideal.Quotient.factorₐ κ hle).toLinearMap ≤ κ ∙ v := by
          intro z hz
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
          rw [LinearMap.mem_ker] at hz
          have hx : x ∈ Ideal.span {t ^ k} := by
            rw [← Ideal.Quotient.eq_zero_iff_mem]
            simpa using hz
          obtain ⟨a, rfl⟩ := (mem_pow _ _).1 hx
          obtain ⟨b, hb⟩ := dec a
          rw [Submodule.mem_span_singleton]
          refine ⟨ε a, ?_⟩
          have e : a * t ^ k = algebraMap κ Λ (ε a) * t ^ k + b * t ^ (k + 1) := by
            linear_combination (t ^ k) * hb
          have hb0 : Ideal.Quotient.mk (Ideal.span {t ^ (k + 1)}) (b * t ^ (k + 1)) = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ b (Ideal.subset_span rfl))
          rw [e, map_add, hb0, add_zero, map_mul, Algebra.smul_def, Ideal.Quotient.mk_algebraMap]
        exact (Submodule.finrank_mono hsub).trans
          (by simpa using finrank_span_le_card ({v} : Set (Λ ⧸ Ideal.span {t ^ (k + 1)})))
      · have hvk : v ∈ LinearMap.ker (Ideal.Quotient.factorₐ κ hle).toLinearMap := by
          rw [LinearMap.mem_ker]
          simp only [v, AlgHom.toLinearMap_apply, Ideal.Quotient.factorₐ_apply_mk]
          exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
        have hv0 : v ≠ 0 := by
          intro h0
          exact hlt k (by omega) (drop k (Ideal.Quotient.eq_zero_iff_mem.1 h0))
        have hne : LinearMap.ker (Ideal.Quotient.factorₐ κ hle).toLinearMap ≠ ⊥ := fun hb ↦
          hv0 ((Submodule.mem_bot κ).1 (hb ▸ hvk))
        exact Nat.one_le_iff_ne_zero.2 (fun h ↦ hne (Submodule.finrank_eq_zero.1 h))
  have factA : ∃ k ≤ n, J = Ideal.span {t ^ k} := by
    by_cases h0 : J ≤ Ideal.span {t ^ n}
    · refine ⟨n, le_rfl, le_antisymm h0 ?_⟩
      rw [hn, Ideal.span_singleton_eq_bot.2 rfl]
      exact bot_le
    · have hex : ∃ k, ¬ J ≤ Ideal.span {t ^ k} := ⟨n, h0⟩
      obtain ⟨k0, hk0, hk0n, hmin⟩ : ∃ k0, ¬ J ≤ Ideal.span {t ^ k0} ∧ k0 ≤ n ∧
          ∀ j < k0, J ≤ Ideal.span {t ^ j} :=
        ⟨Nat.find hex, Nat.find_spec hex, Nat.find_min' hex h0,
          fun j hj ↦ not_not.1 (Nat.find_min hex hj)⟩
      have hk0pos : k0 ≠ 0 := by
        intro hz
        apply hk0
        rw [hz, pow_zero, Ideal.span_singleton_one]
        exact le_top
      obtain ⟨k, rfl⟩ : ∃ k, k0 = k + 1 := Nat.exists_eq_succ_of_ne_zero hk0pos
      have hJk : J ≤ Ideal.span {t ^ k} := hmin k (by omega)
      obtain ⟨x, hxJ, hx⟩ := SetLike.not_le_iff_exists.1 hk0
      obtain ⟨a, rfl⟩ := (mem_pow _ _).1 (hJk hxJ)
      have ha : a ∉ IsLocalRing.maximalIdeal Λ := by
        intro ham
        obtain ⟨b, rfl⟩ := (mem_m _).1 ham
        apply hx
        rw [mem_pow]
        exact ⟨b, by ring⟩
      obtain ⟨u, hu⟩ := unit_of a ha
      refine ⟨k, by omega, le_antisymm hJk ?_⟩
      rw [Ideal.span_le, Set.singleton_subset_iff]
      have e : t ^ k = ↑u⁻¹ * (a * t ^ k) := by
        rw [← hu, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
      rw [e]
      exact J.mul_mem_left _ hxJ
  obtain ⟨k, hkn, rfl⟩ := factA
  rw [dimB k hkn] at hJ
  rw [hJ]

theorem UpperTheory.Gal.crystallineComparison.Mod.chainLoc_of :
    ChainLoc := by
  intro κ Λ _ _ _ _ _ ε t ht J q hq
  exact ideal_eq_span_pow_of_finrank κ Λ ε t ht q J hq
