import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultiplicityDifferentEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootsOfUnityAndPValuation
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
open IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.DiffGenNorm

theorem norm_natCast_self (p : ℕ) [Fact p.Prime] : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]) p, norm_algebraMap', Padic.norm_p]

variable {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] (φ : 𝓞 E →+* ↥(intO ℂ_[p]))

theorem norm_le_one (x : 𝓞 E) : ‖((φ x : ↥(intO ℂ_[p])) : ℂ_[p])‖ ≤ 1 := (φ x).2

def smallIdeal : Ideal (𝓞 E) where
  carrier := {x | ‖((φ x : ↥(intO ℂ_[p])) : ℂ_[p])‖ < 1}
  add_mem' := by
    intro a b ha hb
    change ‖((φ (a + b) : ↥(intO ℂ_[p])) : ℂ_[p])‖ < 1
    rw [map_add, Subring.coe_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  zero_mem' := by
    change ‖((φ 0 : ↥(intO ℂ_[p])) : ℂ_[p])‖ < 1
    simp
  smul_mem' := by
    intro c x hx
    change ‖((φ (c * x) : ↥(intO ℂ_[p])) : ℂ_[p])‖ < 1
    rw [map_mul, Subring.coe_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_le_one φ c)).trans_lt hx

theorem mem_smallIdeal (x : 𝓞 E) : x ∈ smallIdeal φ ↔ ‖((φ x : ↥(intO ℂ_[p])) : ℂ_[p])‖ < 1 := Iff.rfl

theorem norm_eq_one_of_not_mem {x : 𝓞 E} (hx : x ∉ smallIdeal φ) : ‖((φ x : ↥(intO ℂ_[p])) : ℂ_[p])‖ = 1 :=
  le_antisymm (norm_le_one φ x) (not_lt.1 hx)

theorem natCast_mem_smallIdeal : (p : 𝓞 E) ∈ smallIdeal φ := by
  rw [mem_smallIdeal, map_natCast, Subring.coe_natCast, norm_natCast_self]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

theorem smallIdeal_isPrime : (smallIdeal φ).IsPrime where
  ne_top' := fun h => by
    have h1 : (1 : 𝓞 E) ∈ smallIdeal φ := h ▸ Submodule.mem_top
    rw [mem_smallIdeal, map_one, OneMemClass.coe_one, norm_one] at h1
    exact lt_irrefl _ h1
  mem_or_mem' := by
    intro x y hxy
    by_contra hc
    push_neg at hc
    rw [mem_smallIdeal, map_mul, Subring.coe_mul, norm_mul, norm_eq_one_of_not_mem φ hc.1,
      norm_eq_one_of_not_mem φ hc.2, mul_one] at hxy
    exact lt_irrefl _ hxy

def primeOf : HeightOneSpectrum (𝓞 E) :=
  ⟨smallIdeal φ, smallIdeal_isPrime φ, fun h => by
    have h1 := natCast_mem_smallIdeal φ (E := E)
    rw [h, Ideal.mem_bot] at h1
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h1⟩

theorem norm_eq_pow {π : 𝓞 E} (hπ : (primeOf φ).intValuation π = WithZero.exp (-1)) {x : 𝓞 E} (hx : x ≠ 0) {n : ℕ}
    (hn : (primeOf φ).intValuation x = WithZero.exp (-(n : ℤ))) :
    ‖((φ x : ↥(intO ℂ_[p])) : ℂ_[p])‖ = ‖((φ π : ↥(intO ℂ_[p])) : ℂ_[p])‖ ^ n := by
  have hs : (primeOf φ).intValuation x = (primeOf φ).intValuation (π ^ n) := by
    rw [hn, map_pow, hπ, ← WithZero.exp_nsmul]
    simp
  obtain ⟨u, v, hu, hv, huv⟩ := GlobalTheory.HTConst.exists_mul_eq_mul (primeOf φ) hx hs
  have h1 := congrArg (fun t => ‖((φ t : ↥(intO ℂ_[p])) : ℂ_[p])‖) huv
  simp only [map_mul, map_pow, Subring.coe_mul, Subring.coe_pow, norm_mul, norm_pow] at h1
  rw [norm_eq_one_of_not_mem φ hu, norm_eq_one_of_not_mem φ hv, one_mul, one_mul] at h1
  exact h1.symm

end GlobalTheory.DiffGenNorm

namespace GlobalTheory.DiffGenNorm

variable {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] (φ : 𝓞 E →+* ↥(intO ℂ_[p]))

theorem intValuation_natCast :
    (primeOf φ).intValuation (p : 𝓞 E) = WithZero.exp (-((Formalism.BasicNotions.eWL E (primeOf φ) : ℕ) : ℤ)) := by
  classical
  have hp : p.Prime := Fact.out
  set w := primeOf φ
  have hpw : (p : 𝓞 E) ∈ w.asIdeal := natCast_mem_smallIdeal φ
  have hp0 : (p : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨n, hn⟩ := GlobalTheory.HTConst.exists_intValuation_eq w hp0
  haveI := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.liesOver_span E p hp w.isPrime hpw
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have he : Formalism.BasicNotions.eWL E w = (normalizedFactors (Ideal.span {(p : 𝓞 E)})).count w.asIdeal := by
    rw [Formalism.BasicNotions.eWL, Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      (Ideal.span {(p : ℤ)}) w.asIdeal (by rw [hmap]; exact ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.span_nat_ne_bot p), hmap]
  have h1 : (p : 𝓞 E) ∈ w.asIdeal ^ n := (w.intValuation_le_pow_iff_mem _ n).1 hn.le
  have h2 : (p : 𝓞 E) ∉ w.asIdeal ^ (n + 1) := fun hc => by
    have := (w.intValuation_le_pow_iff_mem _ (n + 1)).2 hc
    rw [hn, WithZero.exp_le_exp] at this
    push_cast at this
    omega
  have h3 := Ideal.count_normalizedFactors_eq (p := w.asIdeal) (x := Ideal.span {(p : 𝓞 E)}) (n := n)
    ((Ideal.span_singleton_le_iff_mem _).2 h1) (fun hc => h2 ((Ideal.span_singleton_le_iff_mem _).1 hc))
  rw [hn, he, h3]

theorem norm_diffGens [IsGalois ℚ E] {m : ℕ} (d : Fin m → 𝓞 E)
    (hd : Ideal.span (Set.range d) = differentIdeal ℤ (𝓞 E)) :
    ‖fun k => ((φ (d k) : ↥(intO ℂ_[p])) : ℂ_[p])‖ = (p : ℝ) ^ (-vDiff E p) := by
  classical
  have hp : p.Prime := Fact.out
  set w := primeOf φ with hwdef
  have hpw : (p : 𝓞 E) ∈ w.asIdeal := natCast_mem_smallIdeal φ
  have hM := GlobalTheory.ShFam.Pad.multiplicity_different_eq E hp w hpw
  set M := multiplicity w.asIdeal (differentIdeal ℤ (𝓞 E)) with hMdef
  set e := Formalism.BasicNotions.eWL E w with hedef
  have hval := intValuation_natCast φ
  rw [← hwdef, ← hedef] at hval
  have he0 : e ≠ 0 := fun h0 => by
    have := (w.intValuation_lt_one_iff_mem _).2 hpw
    rw [hval, h0] at this
    simp at this
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  set t := ‖((φ π : ↥(intO ℂ_[p])) : ℂ_[p])‖ with htdef
  have ht0 : 0 ≤ t := norm_nonneg _
  have ht1 : t ≤ 1 := norm_le_one φ π

  have hte : t ^ e = (p : ℝ)⁻¹ := by
    have h1 := norm_eq_pow φ hπ (Nat.cast_ne_zero.mpr hp.ne_zero) hval
    rw [map_natCast, Subring.coe_natCast, norm_natCast_self] at h1
    exact h1.symm

  have hD0 : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hfin : FiniteMultiplicity w.asIdeal (differentIdeal ℤ (𝓞 E)) :=
    FiniteMultiplicity.of_not_isUnit (by rw [Ideal.isUnit_iff]; exact w.isPrime.ne_top) hD0
  have hle : differentIdeal ℤ (𝓞 E) ≤ w.asIdeal ^ M := Ideal.le_of_dvd (pow_multiplicity_dvd _ _)
  have hnle : ¬ differentIdeal ℤ (𝓞 E) ≤ w.asIdeal ^ (M + 1) := fun h =>
    hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self M) (Ideal.dvd_iff_le.2 h)
  have hmem : ∀ k, d k ∈ w.asIdeal ^ M := fun k => hle (hd ▸ Ideal.subset_span ⟨k, rfl⟩)
  obtain ⟨k0, hk0⟩ : ∃ k, d k ∉ w.asIdeal ^ (M + 1) := by
    by_contra hc
    push_neg at hc
    refine hnle (hd ▸ (Ideal.span_le.2 ?_))
    rintro _ ⟨k, rfl⟩
    exact hc k

  have hbound : ∀ k, ‖((φ (d k) : ↥(intO ℂ_[p])) : ℂ_[p])‖ ≤ t ^ M := by
    intro k
    by_cases h0 : d k = 0
    · rw [h0, map_zero, ZeroMemClass.coe_zero, norm_zero]
      exact pow_nonneg ht0 _
    obtain ⟨n, hn⟩ := GlobalTheory.HTConst.exists_intValuation_eq w h0
    have hMn : M ≤ n := by
      have := (w.intValuation_le_pow_iff_mem _ M).2 (hmem k)
      rw [hn, WithZero.exp_le_exp] at this
      omega
    rw [norm_eq_pow φ hπ h0 hn]
    exact pow_le_pow_of_le_one ht0 ht1 hMn
  have hexact : ‖((φ (d k0) : ↥(intO ℂ_[p])) : ℂ_[p])‖ = t ^ M := by
    have h0 : d k0 ≠ 0 := fun h => hk0 (h ▸ Submodule.zero_mem _)
    obtain ⟨n, hn⟩ := GlobalTheory.HTConst.exists_intValuation_eq w h0
    have hMn : M ≤ n := by
      have := (w.intValuation_le_pow_iff_mem _ M).2 (hmem k0)
      rw [hn, WithZero.exp_le_exp] at this
      omega
    have hnM : n < M + 1 := by
      by_contra hc
      push_neg at hc
      apply hk0
      refine (w.intValuation_le_pow_iff_mem _ (M + 1)).1 ?_
      rw [hn, WithZero.exp_le_exp]
      push_cast
      omega
    rw [norm_eq_pow φ hπ h0 hn, show n = M by omega]
  have hsup : ‖fun k => ((φ (d k) : ↥(intO ℂ_[p])) : ℂ_[p])‖ = t ^ M :=
    le_antisymm ((pi_norm_le_iff_of_nonneg (pow_nonneg ht0 _)).2 hbound)
      (hexact ▸ norm_le_pi_norm (fun k => ((φ (d k) : ↥(intO ℂ_[p])) : ℂ_[p])) k0)
  rw [hsup]

  have hp' : (p : ℝ) = (t ^ e)⁻¹ := by rw [hte, inv_inv]
  have hte0 : 0 ≤ t ^ e := pow_nonneg ht0 _
  rw [hp', Real.inv_rpow hte0, Real.rpow_neg hte0, inv_inv, ← Real.rpow_natCast t e, ← Real.rpow_mul ht0,
    ← hM, Real.rpow_natCast]

end GlobalTheory.DiffGenNorm

namespace GlobalTheory.DiffGenNorm

theorem exists_diffGens_norm : ∀ (E : Type) [Field E] [NumberField E], IsGalois ℚ E → ∃ (m : ℕ) (d : Fin m → 𝓞 E), (∃ n : ℕ, n ≠ 0 ∧ (n : 𝓞 E) ∈ Ideal.span (Set.range d)) ∧ ∀ (p : ℕ) [Fact p.Prime] (φ : 𝓞 E →+* ↥(intO ℂ_[p])), ‖fun k => ((φ (d k) : ↥(intO ℂ_[p])) : ℂ_[p])‖ = (p : ℝ) ^ (-vDiff E p) := by
  intro E _ _ hG
  obtain ⟨m, d, hd⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (IsNoetherian.noetherian (differentIdeal ℤ (𝓞 E)))
  have hd' : Ideal.span (Set.range d) = differentIdeal ℤ (𝓞 E) := hd
  refine ⟨m, d, ⟨Ideal.absNorm (differentIdeal ℤ (𝓞 E)), ?_, hd' ▸ Ideal.absNorm_mem _⟩, fun p _ φ =>
    norm_diffGens φ d hd'⟩
  exact (Ideal.absNorm_eq_zero_iff.not).2 differentIdeal_ne_bot

end GlobalTheory.DiffGenNorm
