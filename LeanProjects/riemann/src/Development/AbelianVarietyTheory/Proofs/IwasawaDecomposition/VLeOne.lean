import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicEmbeddingsConjugate

namespace GlobalTheory.CommonReading

open scoped NNReal

section
variable {l : ℕ} [Fact l.Prime] {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]

theorem exists_extend [Module.Finite A B] (hi : Function.Injective (algebraMap A B)) (κ : A →+* ℂ_[l])
    (hκ : Function.Injective κ) :
    ∃ ι : FractionRing B →+* ℂ_[l], ∀ y, ι (algebraMap B (FractionRing B) (algebraMap A B y)) = κ y := by
  let _ : Algebra A ℂ_[l] := κ.toAlgebra
  have hAF : Function.Injective (algebraMap A (FractionRing B)) := by
    rw [IsScalarTower.algebraMap_eq A B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp hi
  have : Module.IsTorsionFree A ℂ_[l] := Module.isTorsionFree_iff_algebraMap_injective.mpr hκ
  have : Module.IsTorsionFree A (FractionRing B) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hAF
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hi
  have : Algebra.IsAlgebraic A B := Algebra.IsIntegral.isAlgebraic
  have : Algebra.IsAlgebraic A (FractionRing B) :=
    (IsFractionRing.isAlgebraic_iff' A B (FractionRing B)).1 inferInstance
  let φ : FractionRing B →ₐ[A] ℂ_[l] := IsAlgClosed.lift
  refine ⟨φ.toRingHom, fun y => ?_⟩
  rw [← IsScalarTower.algebraMap_apply A B (FractionRing B) y]
  exact φ.commutes y

theorem v_le_one [Module.Finite A B] (j : B →+* ℂ_[l]) (hκ : ∀ y, Valued.v (j (algebraMap A B y)) ≤ (1 : ℝ≥0)) (b : B) :
    Valued.v (j b) ≤ (1 : ℝ≥0) := by
  obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := A) b
  have hroot : p.eval₂ (j.comp (algebraMap A B)) (j b) = 0 := by
    rw [← Polynomial.hom_eval₂, hp, map_zero]
  by_contra hle
  have hlt := not_le.mp hle
  rw [hpm.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at hroot
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hroot
  have hxn := eq_neg_of_add_eq_zero_left hroot
  have hn : p.natDegree ≠ 0 := by
    intro h0
    rw [h0] at hxn
    simp at hxn
  have h1 : Valued.v (j b ^ p.natDegree) ≤ Valued.v (j b) ^ (p.natDegree - 1) := by
    rw [hxn, Valuation.map_neg]
    apply Valuation.map_sum_le
    intro i hi
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow]
    calc Valued.v ((j.comp (algebraMap A B)) (p.coeff i)) * Valued.v (j b) ^ i
        ≤ 1 * Valued.v (j b) ^ (p.natDegree - 1) :=
          mul_le_mul' (hκ _) (pow_le_pow_right₀ hlt.le (by omega))
      _ = _ := one_mul _
  rw [map_pow] at h1
  have h2 : Valued.v (j b) ^ (p.natDegree - 1) < Valued.v (j b) ^ p.natDegree :=
    pow_lt_pow_right₀ hlt (by omega)
  exact absurd h1 (not_le.mpr h2)

theorem mem_range_iff [IsDiscreteValuationRing B] (ι : FractionRing B →+* ℂ_[l])
    (h : ∀ b, Valued.v (ι (algebraMap B (FractionRing B) b)) ≤ (1 : ℝ≥0)) (x : FractionRing B) :
    x ∈ (algebraMap B (FractionRing B)).range ↔ Valued.v (ι x) ≤ (1 : ℝ≥0) := by
  constructor
  · rintro ⟨b, rfl⟩
    exact h b
  · intro hx
    by_contra hxn
    set φ : B →+* ℂ_[l] := ι.comp (algebraMap B (FractionRing B)) with hφ
    have hφ1 : ∀ b, Valued.v (φ b) ≤ (1 : ℝ≥0) := fun b => h b
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hxn (RingHom.mem_range.mpr ⟨0, map_zero _⟩)
    obtain ⟨b, hb⟩ : ∃ b, algebraMap B (FractionRing B) b = x⁻¹ := by
      rcases ValuationRing.isInteger_or_isInteger B x with h1 | h1
      · exact absurd (RingHom.mem_range.mpr (RingHom.mem_rangeS.mp h1)) hxn
      · exact RingHom.mem_rangeS.mp h1
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [map_zero] at hb
      exact hx0 (inv_eq_zero.mp hb.symm)
    have hbu : ¬ IsUnit b := by
      rintro ⟨u, rfl⟩
      apply hxn
      refine RingHom.mem_range.mpr ⟨(↑u⁻¹ : B), ?_⟩
      rw [map_units_inv, hb, inv_inv]
    have hl1 : Valued.v ((l : ℕ) : ℂ_[l]) < 1 := by
      rw [PadicComplex.valuation_p, one_div]
      have : (1 : ℝ≥0) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      exact inv_lt_one_of_one_lt₀ this
    have hl0 : ((l : ℕ) : B) ≠ 0 := by
      intro h0
      have h2 : φ ((l : ℕ) : B) = 0 := by rw [h0, map_zero]
      rw [map_natCast] at h2
      exact (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) h2
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
    obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hϖ
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hϖ
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hbu (hk.symm.isUnit (by simp))
    have hdvd : ((l : ℕ) : B) ∣ b ^ n := by
      have h2 : ϖ ^ n ∣ ϖ ^ (k * n) :=
        pow_dvd_pow ϖ (by have := Nat.pos_of_ne_zero hk0; nlinarith)
      have h3 : ϖ ^ (k * n) ∣ b ^ n := by
        rw [pow_mul]
        exact (hk.pow_pow (n := n)).symm.dvd
      exact hn.dvd.trans (h2.trans h3)
    obtain ⟨c, hc⟩ := hdvd
    have hvb : Valued.v (φ b) < 1 := by
      by_contra hlt'
      have hge := not_lt.mp hlt'
      have h1 : 1 ≤ Valued.v (φ b) ^ n := one_le_pow₀ hge
      rw [← map_pow Valued.v, ← map_pow φ, hc, map_mul, map_mul, map_natCast] at h1
      exact absurd h1 (not_le.mpr (mul_lt_one_of_nonneg_of_lt_one_left (by positivity) hl1 (hφ1 c)))
    have h1 : Valued.v (ι x) * Valued.v (φ b) = 1 := by
      rw [← map_mul]
      have h3 : ι x * φ b = 1 := by
        show ι x * ι (algebraMap B (FractionRing B) b) = 1
        rw [← map_mul, hb, mul_inv_cancel₀ hx0, map_one]
      rw [h3, map_one]
    exact absurd h1 (ne_of_lt (mul_lt_one_of_nonneg_of_lt_one_right hx (by positivity) hvb))

end

theorem exists_factor {l : ℕ} [Fact l.Prime] {L : Type} [Field L] [NumberField L] (g : L →+* ℂ_[l]) :
    ∃ e : L →+* PadicAlgCl l, ∀ x, algebraMap (PadicAlgCl l) ℂ_[l] (e x) = g x := by
  have hmem : ∀ x : L, g x ∈ (algebraMap (PadicAlgCl l) ℂ_[l]).range := by
    intro x
    obtain ⟨f, hf0, hf⟩ := Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x
    have hg : (f.map (algebraMap ℚ ℂ_[l])).eval (g x) = 0 := by
      have h1 : g (Polynomial.eval₂ (algebraMap ℚ L) x f) = 0 := by
        rw [← Polynomial.aeval_def, hf, map_zero]
      rw [Polynomial.hom_eval₂] at h1
      rw [Polynomial.eval_map]
      have e : g.comp (algebraMap ℚ L) = algebraMap ℚ ℂ_[l] := RingHom.ext_rat _ _
      rwa [e] at h1
    have hsplit : (f.map (algebraMap ℚ (PadicAlgCl l))).Splits := IsAlgClosed.splits _
    have hP0 : f.map (algebraMap ℚ (PadicAlgCl l)) ≠ 0 :=
      (Polynomial.map_ne_zero_iff (algebraMap ℚ (PadicAlgCl l)).injective).mpr hf0
    have hmap : f.map (algebraMap ℚ ℂ_[l]) =
        (f.map (algebraMap ℚ (PadicAlgCl l))).map (algebraMap (PadicAlgCl l) ℂ_[l]) := by
      rw [Polynomial.map_map]
      congr 1
      exact RingHom.ext_rat _ _
    have hroot : g x ∈ ((f.map (algebraMap ℚ (PadicAlgCl l))).map (algebraMap (PadicAlgCl l) ℂ_[l])).roots := by
      rw [Polynomial.mem_roots ((Polynomial.map_ne_zero_iff (algebraMap (PadicAlgCl l) ℂ_[l]).injective).mpr hP0)]
      show Polynomial.eval _ _ = 0
      rw [← hmap]
      exact hg
    rw [hsplit.roots_map_of_injective (algebraMap (PadicAlgCl l) ℂ_[l]).injective, Multiset.mem_map] at hroot
    obtain ⟨β, -, hβ⟩ := hroot
    exact RingHom.mem_range.mpr ⟨β, hβ⟩
  have hr : Function.Bijective (algebraMap (PadicAlgCl l) ℂ_[l]).rangeRestrict :=
    ⟨fun a b hab => (algebraMap (PadicAlgCl l) ℂ_[l]).injective (congrArg Subtype.val hab),
      RingHom.rangeRestrict_surjective _⟩
  let E := RingEquiv.ofBijective _ hr
  refine ⟨E.symm.toRingHom.comp (g.codRestrict _ hmem), fun x => ?_⟩
  exact congrArg Subtype.val (E.apply_symm_apply (g.codRestrict _ hmem x))

theorem exists_common {l : ℕ} [Fact l.Prime] {A B L : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B] (hi : Function.Injective (algebraMap A B))
    (κ : A →+* ℂ_[l]) (hκ : Function.Injective κ) (hv : ∀ y, Valued.v (κ y) ≤ (1 : ℝ≥0))
    [Field L] [NumberField L] (eB : L →+* FractionRing B) (e : L →+* PadicAlgCl l)
    (he : ∀ x, eB x ∈ (algebraMap B (FractionRing B)).range ↔ ‖e x‖ ≤ 1) :
    ∃ (σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (ι : FractionRing B →+* ℂ_[l]),
      (∀ y, ι (algebraMap B (FractionRing B) (algebraMap A B y)) = κ y) ∧
      ∀ x, ι (eB x) = algebraMap (PadicAlgCl l) ℂ_[l] (σ (e x)) := by
  obtain ⟨ι, hι⟩ := exists_extend hi κ hκ
  have hB : ∀ b, Valued.v (ι (algebraMap B (FractionRing B) b)) ≤ (1 : ℝ≥0) := by
    intro b
    refine v_le_one (A := A) (ι.comp (algebraMap B (FractionRing B))) (fun y => ?_) b
    rw [RingHom.comp_apply, hι]
    exact hv y
  obtain ⟨e', he'⟩ := exists_factor (ι.comp eB)
  have hcond : ∀ x, ‖e x‖ ≤ 1 ↔ ‖e' x‖ ≤ 1 := by
    intro x
    rw [← he x, mem_range_iff ι hB, ← RingHom.comp_apply ι eB, ← he' x, ← PadicComplex.coe_eq,
      PadicComplex.valuation_extends, PadicAlgCl.valuation_def, ← NNReal.coe_le_coe, coe_nnnorm,
      NNReal.coe_one]
  obtain ⟨σ, hσ⟩ := GlobalTheory.EmbUnitBallConj.exists_conj l L e e' hcond
  refine ⟨σ, ι, hι, fun x => ?_⟩
  rw [hσ, he']
  rfl

end GlobalTheory.CommonReading
