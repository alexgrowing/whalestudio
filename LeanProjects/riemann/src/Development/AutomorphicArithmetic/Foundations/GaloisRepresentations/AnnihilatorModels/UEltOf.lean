import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.uElt_of :
    UElt := by
  intro p _ D r w hw huw e
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)
  have hbb : ∀ x : 𝓞 D.F, D.bar (D.bar x) = x := by
    intro x
    apply NumberField.RingOfIntegers.ext
    rw [D.bar_eq, D.bar_eq]
    exact IsCMField.complexConj_apply_apply _ _
  have hp : (p : 𝓞 D.F) ∈ uIdeal D r := p_mem_uIdeal D r
  have hs : D.ω - (r : 𝓞 D.F) ∈ uIdeal D r := sub_mem_uIdeal D r
  set ub : Ideal (𝓞 D.F) := Ideal.span {(p : 𝓞 D.F), D.bar D.ω - (r : 𝓞 D.F)} with hub
  have hmap : Ideal.map D.bar (uIdeal D r) = ub := by
    simp [uIdeal, Ideal.map_span, Set.image_pair, hub]
  have hc : (D.ω - (r : 𝓞 D.F)) * (D.bar D.ω - r) = (r : 𝓞 D.F) ^ 2 - (D.tr : 𝓞 D.F) * r + D.nm := by
    linear_combination D.nm_eq - (r : 𝓞 D.F) * D.tr_eq
  have hdvd : (p : ℤ) ∣ r ^ 2 - D.tr * r + D.nm := by
    by_contra hnd
    obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hpr.irreducible).2 hnd
    have h2 := congrArg (Int.cast : ℤ → 𝓞 D.F) hab
    push_cast at h2
    apply hw
    rw [Ideal.eq_top_iff_one]
    apply huw
    have key : (1 : 𝓞 D.F) = (a : 𝓞 D.F) * p + (b : 𝓞 D.F) * ((D.ω - r) * (D.bar D.ω - r)) := by
      linear_combination -h2 - (b : 𝓞 D.F) * hc
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp) (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hs))
  have hprod : uIdeal D r * ub ≤ Ideal.span {(p : 𝓞 D.F)} := by
    obtain ⟨k, hk⟩ := hdvd
    show Ideal.span {(p : 𝓞 D.F), D.ω - (r : 𝓞 D.F)} * ub ≤ _
    rw [hub, Ideal.span_pair_mul_span_pair, Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
    · rw [SetLike.mem_coe, hc, Ideal.mem_span_singleton]
      exact ⟨(k : 𝓞 D.F), by exact_mod_cast hk⟩
  have hsup : uIdeal D r ⊔ ub = ⊤ := by
    obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hpr.irreducible).2 D.disc_p
    have h2 := congrArg (Int.cast : ℤ → 𝓞 D.F) hab
    push_cast at h2
    rw [Ideal.eq_top_iff_one]
    have hdiff : D.ω - D.bar D.ω ∈ uIdeal D r ⊔ ub := by
      have : D.ω - D.bar D.ω = (D.ω - r) - (D.bar D.ω - r) := by ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left hs) (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
    have hpm : (p : 𝓞 D.F) ∈ uIdeal D r ⊔ ub := Ideal.mem_sup_left hp
    have key : (1 : 𝓞 D.F) = (a : 𝓞 D.F) * p + (b : 𝓞 D.F) * ((D.ω - D.bar D.ω) * (D.ω - D.bar D.ω)) := by
      linear_combination -h2 - (b : 𝓞 D.F) * (D.ω + D.bar D.ω + D.tr) * D.tr_eq + 4 * (b : 𝓞 D.F) * D.nm_eq
    rw [key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hdiff))
  have hcopE : uIdeal D r ^ e ⊔ ub ^ e = ⊤ :=
    Ideal.isCoprime_iff_sup_eq.mp ((Ideal.isCoprime_iff_sup_eq.mpr hsup).pow)
  have hle : uIdeal D r ^ e * ub ^ e ≤ Ideal.span {(p : 𝓞 D.F) ^ e} := by
    rw [← mul_pow, ← Ideal.span_singleton_pow]
    exact Ideal.pow_right_mono hprod e
  have hinf : uIdeal D r ^ e ⊓ ub ^ e ≤ Ideal.span {(p : 𝓞 D.F) ^ e} := by
    rw [← Ideal.mul_eq_inf_of_coprime hcopE]
    exact hle
  have h1 : (1 : 𝓞 D.F) ∈ uIdeal D r ^ e ⊔ ub ^ e := by
    rw [hcopE]
    trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
  have hbz : D.bar z ∈ uIdeal D r ^ e := by
    rw [← hmap, ← Ideal.map_pow] at hz
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_of_equiv D.bar z).mp hz
    rwa [hbb]
  have hup : ∀ x ∈ uIdeal D r ^ e, D.bar x ∈ ub ^ e := by
    intro x hx
    rw [← hmap, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  have hx0u : z + D.bar z - 1 ∈ uIdeal D r ^ e := by
    have : z + D.bar z - 1 = D.bar z - y := by
      rw [← hyz]
      ring
    rw [this]
    exact Ideal.sub_mem _ hbz hy
  have hx0b : z + D.bar z - 1 ∈ ub ^ e := by
    have h := hup _ hx0u
    have : D.bar (z + D.bar z - 1) = z + D.bar z - 1 := by
      rw [map_sub, map_add, map_one, hbb]
      ring
    rwa [this] at h
  exact ⟨z, fun a ha => hle (Ideal.mul_mem_mul ha hz), hinf (Ideal.mem_inf.mpr ⟨hx0u, hx0b⟩), hbz⟩
