import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PlaceRingFacts

open IsDedekindDomain

variable {R : Subring ℂ} [IsDiscreteValuationRing R]

theorem valuation_unit_mul_pow {ϖ : R} (hϖ : Irreducible ϖ) (u : Rˣ) (n : ℕ) :
    (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)
      (algebraMap R (FractionRing R) ((u : R) * ϖ ^ n)) = WithZero.exp (-(n : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap, map_mul, map_pow,
    HeightOneSpectrum.intValuation_singleton _ hϖ.ne_zero hϖ.maximalIdeal_eq,
    HeightOneSpectrum.intValuation_eq_one_iff.2 ?_]
  · rw [_root_.one_mul, ← WithZero.exp_nsmul]
    congr 1
    simp
  · exact fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit

theorem ord_unit_mul_pow {ϖ : R} (hϖ : Irreducible ϖ) (u : Rˣ) (n : ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (algebraMap R (FractionRing R) ((u : R) * ϖ ^ n)) = n := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw, valuation_unit_mul_pow hϖ u n, WithZero.log_exp, neg_neg]

theorem ord_div {x y : FractionRing R} (hx : x ≠ 0) (hy : y ≠ 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (x / y) = GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R x - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R y := by
  set v := (IsDiscreteValuationRing.maximalIdeal R).valuation (FractionRing R)
  have hvx : v x ≠ 0 := by simpa [v] using hx
  have hvy : v y ≠ 0 := by simpa [v] using hy
  have ex : v x = WithZero.exp (-GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R x) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw, neg_neg, WithZero.exp_log hvx]
  have ey : v y = WithZero.exp (-GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R y) := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw, neg_neg, WithZero.exp_log hvy]
  have : v (x / y) = WithZero.exp (-(GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R x - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R y)) := by
    rw [map_div₀, ex, ey, ← WithZero.exp_sub]
    congr 1
    ring
  rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw, this, WithZero.log_exp, neg_neg]

end GlobalTheory.PlaceRingFacts

namespace GlobalTheory.PlaceRingFacts

theorem norm_natCast_self (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [← Padic.norm_p (p := l), ← PadicComplex.norm_extends' l (l : ℚ_[l])]
  congr 1
  simp

theorem place_ring_facts : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l])
    (R : Subring ℂ) [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∃ j : FractionRing R →+* ℂ, (∀ x : R, j (algebraMap R (FractionRing R) x) = x) ∧ CharZero R ∧
      (l : R) ∈ IsLocalRing.maximalIdeal R ∧ Nat.card (E →+* FractionRing R) = Module.finrank ℚ E ∧
      (∀ σ : E →+* ℂ, ∃ τ : E →+* FractionRing R, j.comp τ = σ) ∧
      ∀ (x : FractionRing R) (r : ℚ), ((-r : ℚ) : WithTop ℚ) ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l x → Sz l lam (r : ℝ) (j x) := by
  intro E _ _ l _ lam R _ hR
  obtain ⟨-, hSz, -, hfr⟩ := hR
  have hlp : (l : ℕ).Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hA : ∀ x : R, (x : ℂ) ∈ algebraicClosure ℚ ℂ := fun x => (hSz x x.2).1
  let i0 : R →+* algebraicClosure ℚ ℂ := R.subtype.codRestrict (algebraicClosure ℚ ℂ) hA
  have hi0 : Function.Injective i0 := fun a b h => Subtype.ext (show (a : ℂ) = b from congrArg (fun z : algebraicClosure ℚ ℂ => (z : ℂ)) h)
  let jA : FractionRing R →+* algebraicClosure ℚ ℂ := IsFractionRing.lift hi0
  have hjA : ∀ x : R, jA (algebraMap R (FractionRing R) x) = i0 x := fun x => IsFractionRing.lift_algebraMap hi0 x
  let j : FractionRing R →+* ℂ := (IntermediateField.val (algebraicClosure ℚ ℂ)).toRingHom.comp jA
  have hj : ∀ x : R, j (algebraMap R (FractionRing R) x) = x := fun x => by
    show ((jA (algebraMap R (FractionRing R) x) : algebraicClosure ℚ ℂ) : ℂ) = x
    rw [hjA]
    rfl
  let g : FractionRing R →+* ℂ_[l] := lam.comp jA
  have hN1 : ∀ a : R, ‖g (algebraMap R (FractionRing R) a)‖ ≤ 1 := fun a => by
    obtain ⟨h, hh⟩ := hSz a a.2
    have e : g (algebraMap R (FractionRing R) a) = lam ⟨(a : ℂ), h⟩ := by
      simp only [g, RingHom.comp_apply, hjA]
      rfl
    rw [e]
    simpa using hh
  have hunit : ∀ u : Rˣ, ‖g (algebraMap R (FractionRing R) u)‖ = 1 := fun u => by
    have hprod : ‖g (algebraMap R (FractionRing R) u)‖ * ‖g (algebraMap R (FractionRing R) (u⁻¹ : Rˣ))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    have h1 := hN1 u
    have h2 := hN1 (u⁻¹ : Rˣ)
    have h0 := norm_nonneg (g (algebraMap R (FractionRing R) u))
    refine le_antisymm h1 ?_
    calc (1 : ℝ) = _ := hprod.symm
      _ ≤ ‖g (algebraMap R (FractionRing R) u)‖ * 1 := mul_le_mul_of_nonneg_left h2 h0
      _ = _ := mul_one _
  have hgl : ‖g (algebraMap R (FractionRing R) (l : R))‖ = (l : ℝ)⁻¹ := by
    rw [map_natCast, map_natCast]
    exact norm_natCast_self l
  have hlinv : (l : ℝ)⁻¹ ≠ 1 := by
    intro h
    rw [inv_eq_one] at h
    linarith
  have hmax : (l : R) ∈ IsLocalRing.maximalIdeal R := by
    refine (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 fun hu => ?_)
    obtain ⟨u, hu⟩ := hu
    have := hunit u
    rw [hu, hgl] at this
    exact hlinv this
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  set c := ‖g (algebraMap R (FractionRing R) ϖ)‖ with hc
  have hpowR : ∀ a : R, a ≠ 0 → ∃ n : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R (algebraMap R (FractionRing R) a) = n ∧
      ‖g (algebraMap R (FractionRing R) a)‖ = c ^ n := fun a ha => by
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    refine ⟨n, ord_unit_mul_pow hϖ u n, ?_⟩
    rw [map_mul, map_mul, norm_mul, hunit, _root_.one_mul, map_pow, map_pow, norm_pow]
  have hlR : (l : R) ≠ 0 := Nat.cast_ne_zero.2 hlp.ne_zero
  obtain ⟨k, hk1, hk2⟩ := hpowR _ hlR
  rw [hgl] at hk2
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hlinv (by simpa using hk2)
  have hc0 : 0 ≤ c := norm_nonneg _
  have hcl : c = (l : ℝ) ^ (-(1 / (k : ℝ))) := by
    have hl0 : (0 : ℝ) ≤ l := by positivity
    refine (pow_left_inj₀ hc0 (Real.rpow_nonneg hl0 _) hk0).1 ?_
    rw [← hk2, ← Real.rpow_natCast, ← Real.rpow_mul hl0]
    have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk0
    rw [show -(1 / (k : ℝ)) * k = -1 by field_simp, Real.rpow_neg_one]
  have hcne : c ≠ 0 := by
    rw [hcl]
    exact (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hgen : ∀ x : FractionRing R, x ≠ 0 →
      ‖g x‖ = c ^ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R x) := fun x hx => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : algebraMap R (FractionRing R) b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hb0
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hx
    have haK : algebraMap R (FractionRing R) a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 ha0
    obtain ⟨na, hna1, hna2⟩ := hpowR a ha0
    obtain ⟨nb, hnb1, hnb2⟩ := hpowR b hb0
    rw [ord_div haK hbK, hna1, hnb1, map_div₀, norm_div, hna2, hnb2, zpow_sub₀ hcne, zpow_natCast, zpow_natCast]

  have hrange : ∀ σ : E →+* ℂ, ∀ x, σ x ∈ j.fieldRange := fun σ x => by
    obtain ⟨a, ha, b, hb, hb0, h⟩ := hfr σ x
    refine RingHom.mem_fieldRange.2 ⟨algebraMap R (FractionRing R) ⟨a, ha⟩ / algebraMap R (FractionRing R) ⟨b, hb⟩, ?_⟩
    rw [map_div₀, hj, hj]
    exact (div_eq_iff hb0).2 h.symm
  have hsurj : ∀ σ : E →+* ℂ, ∃ τ : E →+* FractionRing R, j.comp τ = σ := fun σ => by
    refine ⟨(j.rangeRestrictFieldEquiv.symm : j.fieldRange →+* FractionRing R).comp
      (σ.codRestrict j.fieldRange (hrange σ)), ?_⟩
    ext x
    simp
  refine ⟨j, hj, inferInstance, hmax, ?_, hsurj, ?_⟩
  · have hbij : Function.Bijective (fun τ : E →+* FractionRing R => j.comp τ) := by
      refine ⟨fun τ₁ τ₂ h => ?_, fun σ => hsurj σ⟩
      ext x
      exact j.injective (congrArg (fun f : E →+* ℂ => f x) h)
    rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, NumberField.Embeddings.card]
  · intro x r hle
    refine ⟨(jA x).2, ?_⟩
    show ‖g x‖ ≤ (l : ℝ) ^ (r : ℝ)
    by_cases hx : x = 0
    · rw [hx, map_zero, norm_zero]
      positivity
    rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp, if_neg hx, WithTop.coe_le_coe] at hle
    have hlK : ((l : ℕ) : FractionRing R) = algebraMap R (FractionRing R) (l : R) := (map_natCast _ _).symm
    rw [hlK, hk1] at hle
    have hle' : -(r : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R x : ℝ) / (k : ℝ) := by
      have := (Rat.cast_le (K := ℝ)).2 hle
      push_cast at this
      exact this
    rw [hgen x hx, hcl, ← Real.rpow_intCast, ← Real.rpow_mul (by positivity)]
    refine Real.rpow_le_rpow_of_exponent_le hl1.le ?_
    have : -(1 / (k : ℝ)) * (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R x : ℝ) = -((GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ord_vw R x : ℝ) / (k : ℝ)) := by ring
    rw [this]
    linarith

end GlobalTheory.PlaceRingFacts
