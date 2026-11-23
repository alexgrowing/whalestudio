import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt

noncomputable section

namespace GlobalTheory.CdvrLiftCp

theorem mem_int_iff' {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : x ∈ PadicComplexInt p ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).symm

theorem norm_p_lt_one' {p : ℕ} [Fact p.Prime] : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

theorem mem_range_of_norm_le {p : ℕ} [Fact p.Prime] {W L : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (kL : L →+* ℂ_[p])
    (hW : ∀ w, ‖kL (algebraMap W L w)‖ ≤ 1) (x : L) (hx : ‖kL x‖ ≤ 1) : x ∈ Set.range (algebraMap W L) := by
  by_contra hxr
  have hx0 : x ≠ 0 := by rintro rfl; exact hxr ⟨0, map_zero _⟩
  have hunit : ∀ u : Wˣ, ‖kL (algebraMap W L u)‖ = 1 := by
    intro u
    have h1 : kL (algebraMap W L u) * kL (algebraMap W L ↑u⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    have a1 := hW u
    have a2 := hW ↑u⁻¹
    nlinarith [norm_nonneg (kL (algebraMap W L u)), norm_nonneg (kL (algebraMap W L ↑u⁻¹))]
  obtain ⟨y, hy⟩ : IsLocalization.IsInteger W x⁻¹ :=
    (ValuationRing.isInteger_or_isInteger W x).resolve_left (fun ⟨a, ha⟩ => hxr ⟨a, ha⟩)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact hx0 (inv_eq_zero.1 hy.symm)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, u, hyu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  have hn : n ≠ 0 := by
    rintro rfl
    apply hxr
    refine ⟨↑u⁻¹, ?_⟩
    rw [hyu, pow_zero, mul_one] at hy
    rw [map_units_inv, hy, inv_inv]
  have hy1 : ‖kL (algebraMap W L y)‖ = 1 := by
    have h1 : kL x * kL (algebraMap W L y) = 1 := by rw [← map_mul, hy, mul_inv_cancel₀ hx0, map_one]
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    have a2 := hW y
    nlinarith [norm_nonneg (kL x), norm_nonneg (kL (algebraMap W L y))]
  have hϖ1 : ‖kL (algebraMap W L ϖ)‖ = 1 := by
    rw [hyu, map_mul, map_mul, norm_mul, hunit, one_mul, map_pow, map_pow, norm_pow] at hy1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 hy1
  have hall : ∀ w : W, w ≠ 0 → ‖kL (algebraMap W L w)‖ = 1 := by
    intro w hw
    obtain ⟨m, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw hϖ
    rw [map_mul, map_mul, norm_mul, hunit, map_pow, map_pow, norm_pow, hϖ1, one_pow, one_mul]
  have hp : kL (algebraMap W L (p : W)) = (p : ℂ_[p]) := by simp
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpW : (p : W) ≠ 0 := by
    intro h
    rw [h, map_zero, map_zero] at hp
    exact hp0 hp.symm
  have := hall _ hpW
  rw [hp] at this
  exact absurd this (ne_of_lt norm_p_lt_one')

end GlobalTheory.CdvrLiftCp

namespace GlobalTheory.CdvrLiftCp

theorem exists_cdvr_lift : ∀ (p : ℕ) [Fact p.Prime] (T : CDVR), T.FinRes → ∀ (kO : T.V →+* 𝓞_ℂ_[p]) (k : T.Fr →+* ℂ_[p]), (∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a)) → ∀ (L : Type) [Field L] [Algebra T.Fr L] [FiniteDimensional T.Fr L] (kL : L →+* ℂ_[p]), (∀ a, kL (algebraMap T.Fr L a) = k a) → ∃ (T' : CDVR) (i : T.V →+* T'.V) (iF : T.Fr →+* T'.Fr) (ψ : L ≃+* T'.Fr) (kO' : T'.V →+* 𝓞_ℂ_[p]), T'.FinRes ∧ Function.Injective kO' ∧ (∀ a, algebraMap T'.V T'.Fr (i a) = iF (algebraMap T.V T.Fr a)) ∧ (∀ a, ψ (algebraMap T.Fr L a) = iF a) ∧ (∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' a) = kL (ψ.symm (algebraMap T'.V T'.Fr a))) ∧ ∀ (A : Type) [CommRing A] (f : A →+* L), (∀ a, ‖kL (f a)‖ ≤ 1) → ∃ fO : A →+* T'.V, ∀ a, algebraMap T'.V T'.Fr (fO a) = ψ (f a) := by
  intro p _ T hT kO k hk L _ _ _ kL hkL
  haveI : CharZero T.Fr := algebraRat.charZero _
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, hinj, hloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension T.V T.Fr L
  haveI : CharZero W := charZero_of_injective_algebraMap hinj
  let T' : CDVR := { V := W }
  let ψ : L ≃+* FractionRing W := (FractionRing.algEquiv W L).symm.toRingEquiv
  let iF : T.Fr →+* FractionRing W := ψ.toRingHom.comp (algebraMap T.Fr L)
  have hψ : ∀ w : W, ψ (algebraMap W L w) = algebraMap W (FractionRing W) w := by
    intro w
    change (FractionRing.algEquiv W L).symm (algebraMap W L w) = _
    exact AlgEquiv.commutes _ w
  have hψs : ∀ w : W, ψ.symm (algebraMap W (FractionRing W) w) = algebraMap W L w := by
    intro w
    rw [← hψ, RingEquiv.symm_apply_apply]
  have hφ : ∀ a, iF (algebraMap T.V T.Fr a) = algebraMap W (FractionRing W) (algebraMap T.V W a) := by
    intro a
    have h1 : algebraMap T.Fr L (algebraMap T.V T.Fr a) = algebraMap W L (algebraMap T.V W a) :=
      (RingHom.congr_fun hc a).symm
    change ψ (algebraMap T.Fr L (algebraMap T.V T.Fr a)) = _
    rw [h1, hψ]
  haveI : Algebra.IsIntegral T.V W := Algebra.IsIntegral.of_finite T.V W
  have hint : ∀ w : W, kL (algebraMap W L w) ∈ 𝓞_ℂ_[p] := by
    intro w
    have hw : IsIntegral T.V w := Algebra.IsIntegral.isIntegral w
    have hcomp : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO = (kL.comp (algebraMap W L)).comp (algebraMap T.V W) := by
      ext a
      change algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = kL (algebraMap W L (algebraMap T.V W a))
      rw [hk, ← hkL, ← RingHom.comp_apply (algebraMap W L), ← RingHom.comp_apply (algebraMap T.Fr L), hc]
    have h1 : IsIntegral 𝓞_ℂ_[p] (kL (algebraMap W L w)) := IsIntegral.map_of_comp_eq kO _ hcomp hw
    exact (PadicComplexInt.integers p).mem_of_integral h1
  have hW : ∀ w : W, ‖kL (algebraMap W L w)‖ ≤ 1 := fun w => (mem_int_iff' _).1 (hint w)
  let kO' : W →+* 𝓞_ℂ_[p] := (kL.comp (algebraMap W L)).codRestrict 𝓞_ℂ_[p] hint
  have hkO' : ∀ w, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' w) = kL (algebraMap W L w) := fun w => rfl
  refine ⟨T', algebraMap T.V W, iF, ψ, kO', ?_, ?_, fun a => (hφ a).symm, fun a => rfl, ?_, ?_⟩
  · haveI : Finite (IsLocalRing.ResidueField T.V) := hT
    exact Module.finite_of_finite (IsLocalRing.ResidueField T.V) (M := IsLocalRing.ResidueField W)
  · intro a b hab
    have h1 := congrArg (algebraMap 𝓞_ℂ_[p] ℂ_[p]) hab
    rw [hkO', hkO'] at h1
    exact IsFractionRing.injective W L (kL.injective h1)
  · intro a
    change algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' a) = kL (ψ.symm (algebraMap W (FractionRing W) a))
    rw [hkO', hψs]
  · intro A _ f hf
    have hmem : ∀ a, f a ∈ (algebraMap W L).range := fun a => mem_range_of_norm_le kL hW (f a) (hf a)
    let e : W ≃+* (algebraMap W L).range :=
      RingEquiv.ofBijective (algebraMap W L).rangeRestrict
        ⟨fun a b h => IsFractionRing.injective W L (congrArg Subtype.val h), (algebraMap W L).rangeRestrict_surjective⟩
    refine ⟨e.symm.toRingHom.comp (f.codRestrict _ hmem), fun a => ?_⟩
    change algebraMap W (FractionRing W) (e.symm (f.codRestrict _ hmem a)) = ψ (f a)
    have h2 : algebraMap W L (e.symm (f.codRestrict _ hmem a)) = f a := by
      have h3 : e (e.symm (f.codRestrict _ hmem a)) = f.codRestrict _ hmem a := e.apply_symm_apply _
      exact congrArg Subtype.val h3
    rw [← hψ, h2]

end GlobalTheory.CdvrLiftCp
