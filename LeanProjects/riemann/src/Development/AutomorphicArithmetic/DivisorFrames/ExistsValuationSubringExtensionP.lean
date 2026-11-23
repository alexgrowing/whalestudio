import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ChiLenPicPushforwardOfIsClosedImmersion
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

private theorem UpperTheory.integral_mem_valuationSubring {S κ : Type} [CommRing S] [Field κ] [Algebra S κ]
    (B : ValuationSubring κ) (h : ∀ s, algebraMap S κ s ∈ B) {x : κ}
    (hx : _root_.IsIntegral S x) : x ∈ B := by
  have h1 : _root_.IsIntegral B (RingHom.id κ x) :=
    IsIntegral.map_of_comp_eq ((algebraMap S κ).codRestrict B.toSubring h) (RingHom.id κ)
      (by ext s; rfl) hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h1
  have : (y : κ) = x := hy
  exact this ▸ y.2

private theorem UpperTheory.exists_prime_power_mul_mem (p : ℕ) (K : Type) [Field K] [NumberField K]
    (V : ValuationSubring K) (hp : p.Prime) (hV : (p : K) ∈ V.nonunits) (x : K) :
    ∃ m : ℕ, (p : K) ^ m * x ∈ V := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hy⟩ := halg.exists_integral_multiple
  have h1 : y • x ∈ V := UpperTheory.integral_mem_valuationSubring V (fun s => by simp) hy
  have h2 : (y.natAbs : K) * x ∈ V := by
    rcases Int.natAbs_eq y with h | h
    · rw [h] at h1; simpa using h1
    · rw [h] at h1
      have := V.neg_mem _ h1
      simpa using this
  obtain ⟨e, n, hn, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hy0) p hp.ne_one
  refine ⟨e, ?_⟩
  have hcop : IsCoprime (p : V) (n : V) := by
    have := (Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hn)).map (Int.castRingHom V)
    simpa using this
  have hpm : (p : V) ∈ maximalIdeal V := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; simpa using hV
  have hu : IsUnit (n : V) := by
    by_contra hnu
    obtain ⟨a, b, hab⟩ := hcop
    have : (1 : V) ∈ maximalIdeal V := by
      rw [← hab]
      exact add_mem (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ hnu)
    exact (maximalIdeal.isMaximal V).ne_top ((Ideal.eq_top_iff_one _).2 this)
  obtain ⟨w, hw⟩ := hu.exists_left_inv
  have hw' : (w : K) * (n : K) = 1 := by
    have := congrArg (fun t : V => (t : K)) hw
    simpa using this
  have h3 := V.mul_mem _ _ w.2 h2
  rw [he] at h3
  push_cast at h3
  convert h3 using 1
  linear_combination (-((p : K) ^ e * x)) * hw'

private theorem UpperTheory.mvPolynomial_primitive_decomposition {K σ : Type} [Field K] (V : ValuationSubring K)
    (f : MvPolynomial σ K) (hf : f ≠ 0) :
    ∃ (c : K) (g : MvPolynomial σ V), c ≠ 0 ∧ MvPolynomial.map (residue V) g ≠ 0 ∧
      f = MvPolynomial.C c * MvPolynomial.map V.subtype g := by
  obtain ⟨n, hn, hmax⟩ := Finset.exists_max_image f.support
    (fun n => V.valuation (f.coeff n)) (MvPolynomial.support_nonempty.2 hf)
  have hc : f.coeff n ≠ 0 := MvPolynomial.mem_support_iff.1 hn
  have hr : MvPolynomial.C (f.coeff n)⁻¹ * f ∈ Set.range (MvPolynomial.map V.subtype) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨k, hk, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 ha
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hk
    rw [MvPolynomial.coeff_C_mul]
    have hk' : k ∈ f.support := MvPolynomial.mem_support_iff.2 (right_ne_zero_of_mul hk)
    refine ⟨⟨(f.coeff n)⁻¹ * f.coeff k, ?_⟩, rfl⟩
    rw [← V.valuation_le_one_iff, map_mul, map_inv₀]
    have hpos : 0 < V.valuation (f.coeff n) := by
      rw [zero_lt_iff]; simpa using hc
    rw [inv_mul_le_iff₀ hpos, mul_one]
    exact hmax k hk'
  obtain ⟨g, hg⟩ := hr
  refine ⟨f.coeff n, g, hc, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (MvPolynomial.coeff n) hg
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc] at h1
    have h2 : g.coeff n = 1 := Subtype.ext h1
    have h3 := congrArg (MvPolynomial.coeff n) h0
    rw [MvPolynomial.coeff_map, h2] at h3
    simp at h3
  · rw [hg, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc]; simp

theorem UpperTheory.exists_valuationSubring_extension_p :
    ∀ (p : ℕ) (K κ : Type) [Field K] [NumberField K] [Field κ] [Countable κ] (φ : K →+* κ) (V : ValuationSubring K), p.Prime → (p : K) ∈ V.nonunits → ∃ A : ValuationSubring κ, (∀ v ∈ V, φ v ∈ A) ∧ (p : κ) ∈ A.nonunits ∧ ∀ x : κ, ∃ m : ℕ, (p : κ) ^ m * x ∈ A := by
  intro p K κ _ _ _ _ φ V hp hV
  letI : Algebra K κ := φ.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K κ
  let ev : MvPolynomial s K →ₐ[K] κ := MvPolynomial.aeval (Subtype.val : s → κ)
  have hev : Function.Injective ev := hs.1
  let ψ : MvPolynomial s V →+* κ := ev.toRingHom.comp (MvPolynomial.map V.subtype)
  have hψ : Function.Injective ψ :=
    hev.comp (MvPolynomial.map_injective V.subtype Subtype.val_injective)
  let I : Ideal (MvPolynomial s V) := RingHom.ker (MvPolynomial.map (residue V))
  haveI hI : I.IsPrime := RingHom.ker_isPrime _
  have hunit : ∀ y : I.primeCompl, IsUnit (ψ y) := by
    intro y
    rw [isUnit_iff_ne_zero, map_ne_zero_iff _ hψ]
    intro h0
    exact y.2 (h0 ▸ I.zero_mem)
  let F : Localization.AtPrime I →+* κ := IsLocalization.lift hunit
  have hF : ∀ g, F (algebraMap _ _ g) = ψ g := fun g => IsLocalization.lift_eq hunit g
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing F
  have hψA : ∀ g, ψ g ∈ A := fun g => hF g ▸ hA _
  have hψinv : ∀ g, g ∉ I → (ψ g)⁻¹ ∈ A := by
    intro g hg
    obtain ⟨w, hw⟩ := (IsLocalization.map_units (Localization.AtPrime I)
      (⟨g, hg⟩ : I.primeCompl)).exists_left_inv
    have h1 := congrArg F hw
    rw [map_mul, map_one, hF] at h1
    rw [← eq_inv_of_mul_eq_one_left h1]
    exact hA w
  have hφ : ∀ v ∈ V, φ v ∈ A := by
    intro v hv
    have := hψA (MvPolynomial.C ⟨v, hv⟩)
    show algebraMap K κ v ∈ A
    simpa [ψ, ev] using this
  have hpm : (p : V) ∈ maximalIdeal V := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; simpa using hV
  have hpA : (p : κ) ∈ A.nonunits := by
    have h1 : ((p : A) : κ) ∈ A.nonunits := by
      rw [ValuationSubring.coe_mem_nonunits_iff, mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hu' : IsUnit ((F.codRestrict A.toSubring hA) (p : Localization.AtPrime I)) := by
        rw [map_natCast]; exact hu
      have h2 := (hloc.map_nonunit _ hu')
      have h3 : (p : Localization.AtPrime I) = algebraMap (MvPolynomial s V) _ p := by simp
      rw [h3, IsLocalization.AtPrime.isUnit_to_map_iff _ I] at h2
      apply h2
      show MvPolynomial.map (residue V) (p : MvPolynomial s V) = 0
      have h4 : residue V (p : V) = 0 := (residue_eq_zero_iff _).2 hpm
      rw [← map_natCast (MvPolynomial.C : V →+* MvPolynomial s V), MvPolynomial.map_C, h4, map_zero]
    simpa using h1
  refine ⟨A, hφ, hpA, ?_⟩
  have hpmem : (p : κ) ∈ A := natCast_mem A p
  let B0 : Subring κ :=
    { carrier := {x | ∃ m : ℕ, (p : κ) ^ m * x ∈ A}
      mul_mem' := by
        rintro a b ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        convert A.mul_mem _ _ hm hn using 1
        ring
      one_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro a b ⟨m, hm⟩ ⟨n, hn⟩
        refine ⟨m + n, ?_⟩
        convert A.add_mem _ _ (A.mul_mem _ _ (pow_mem hpmem n) hm) (A.mul_mem _ _ (pow_mem hpmem m) hn) using 1
        ring
      zero_mem' := ⟨0, by simp⟩
      neg_mem' := by
        rintro a ⟨m, hm⟩
        refine ⟨m, ?_⟩
        convert A.neg_mem _ hm using 1
        ring }
  have hAB : A.toSubring ≤ B0 := fun x hx => ⟨0, by simpa using hx⟩
  let B : ValuationSubring κ := A.ofLE B0 hAB
  have hAB' : ∀ x ∈ A, x ∈ B := fun x hx => hAB hx
  have hK : ∀ c : K, φ c ∈ B := by
    intro c
    obtain ⟨m, hm⟩ := UpperTheory.exists_prime_power_mul_mem p K V hp hV c
    exact ⟨m, by simpa using hφ _ hm⟩
  have hboth : ∀ f, ev f ∈ B ∧ (ev f)⁻¹ ∈ B := by
    intro f
    by_cases hf : f = 0
    · subst hf; simp
    obtain ⟨c, g, hc, hg, rfl⟩ := UpperTheory.mvPolynomial_primitive_decomposition V f hf
    have h1 : ev (MvPolynomial.C c * MvPolynomial.map V.subtype g) = φ c * ψ g := by
      rw [map_mul]; congr 1; simp [ev]; rfl
    rw [h1, mul_inv, ← map_inv₀]
    exact ⟨B.mul_mem _ _ (hK _) (hAB' _ (hψA g)), B.mul_mem _ _ (hK _) (hAB' _ (hψinv g hg))⟩
  have hadj : ∀ y : Algebra.adjoin K (Set.range (Subtype.val : s → κ)),
      (y : κ) ∈ B ∧ (y : κ)⁻¹ ∈ B := by
    rintro ⟨y, hy⟩
    rw [Algebra.adjoin_range_eq_range_aeval] at hy
    obtain ⟨f, rfl⟩ := hy
    exact hboth f
  intro x
  show x ∈ B
  obtain ⟨y, hy0, hy⟩ := (hs.isAlgebraic.isAlgebraic x).exists_integral_multiple
  have h1 : y • x ∈ B := UpperTheory.integral_mem_valuationSubring B (fun t => (hadj t).1) hy
  have h2 := B.mul_mem _ _ (hadj y).2 h1
  have hy' : (y : κ) ≠ 0 := fun h => hy0 (Subtype.ext h)
  have h3 : y • x = (y : κ) * x := rfl
  rwa [h3, inv_mul_cancel_left₀ hy'] at h2
