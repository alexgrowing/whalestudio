import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.IntegralJetsPairing
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.DualBasesOfSeries
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormSubEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes

open NumberField Filter Topology

noncomputable section

namespace GlobalTheory.Proof.IdempotentLatticeSequence

theorem mem_int_iff {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : x ∈ PadicComplexInt p ↔ ‖x‖ ≤ 1 := by
  show x ∈ (PadicComplex.valued p).v.valuationSubring ↔ _
  rw [Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm, Valuation.norm_def,
    ← map_one (PadicComplex.valued p).v, ← Valuation.restrict_le_iff]
  simpa only [map_one, NNReal.coe_le_one] using
    ((Valuation.RankOne.strictMono (PadicComplex.valued p).v).le_iff_le (b := 1)).symm

theorem norm_int_le {p : ℕ} [Fact p.Prime] {M : Type} [Field M] (φ : M →+* ℂ_[p]) (a : 𝓞 M) : ‖φ (a : M)‖ ≤ 1 := by
  obtain ⟨P, hmon, hev⟩ := RingOfIntegers.isIntegral_coe a
  have key : ∀ f : ℤ →+* ℂ_[p], Polynomial.eval₂ f (φ (a : M)) P = 0 := fun f => by
    rw [RingHom.ext_int f (φ.comp (algebraMap ℤ M)), ← Polynomial.hom_eval₂, hev, map_zero]
  exact GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral ⟨P, hmon, key _⟩

theorem flat_system {A B : Type} [CommRing A] [AddCommGroup B] [Module A B] [Module.Flat A B] {κ J : Type}
    [Fintype κ] [Fintype J] (b : κ → J → A) (r : κ → B) (h : ∀ j, ∑ k, b k j • r k = 0) :
    ∃ (n : ℕ) (a : κ → Fin n → A) (y : Fin n → B), (∀ k, r k = ∑ l, a k l • y l) ∧ ∀ l j, ∑ k, b k j * a k l = 0 := by
  classical
  let f : (J → A) →ₗ[A] (κ → A) := Matrix.mulVecLin (Matrix.of fun k j => b k j)
  let x : (κ → A) →ₗ[A] B := Fintype.linearCombination A r
  have hxf : x ∘ₗ f = 0 := by
    refine LinearMap.ext fun c => ?_
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, x, f, Fintype.linearCombination_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp_rw [mul_comm (b _ j) (c j), mul_smul]
    rw [← Finset.smul_sum, h j, smul_zero]
  obtain ⟨n, a', y', hxa, haf⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxf
  refine ⟨n, fun k l => a' (Pi.single k 1) l, fun l => y' (Finsupp.single l 1), fun k => ?_, fun l j => ?_⟩
  · have hr : r k = x (Pi.single k 1) := by
      simp [x, Fintype.linearCombination_apply, Pi.single_apply]
    rw [hr, hxa, LinearMap.comp_apply]
    conv_lhs => rw [← Finsupp.univ_sum_single (a' (Pi.single k 1))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finsupp.smul_single_one, map_smul]
  · have h1 := congrArg (fun v => v l) (LinearMap.congr_fun haf (Pi.single j 1))
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
    have hf : f (Pi.single j 1) = ∑ k, b k j • Pi.single k 1 := by
      ext k'
      simp [f, Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
    rw [hf, map_sum] at h1
    simpa [Finsupp.finsetSum_apply, map_smul] using h1

def primeOf {p : ℕ} [Fact p.Prime] {E : Type} [Field E] (φ : E →+* ℂ_[p]) : Ideal (𝓞 E) where
  carrier := {a | ‖φ (a : E)‖ < 1}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    change ‖φ (algebraMap (𝓞 E) E (a + b))‖ < 1
    rw [map_add, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  smul_mem' := fun c a ha => by
    change ‖φ (algebraMap (𝓞 E) E (c * a))‖ < 1
    rw [map_mul, map_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le φ c)).trans_lt ha

theorem mem_primeOf {p : ℕ} [Fact p.Prime] {E : Type} [Field E] (φ : E →+* ℂ_[p]) (a : 𝓞 E) :
    a ∈ primeOf φ ↔ ‖φ (algebraMap (𝓞 E) E a)‖ < 1 := by
  exact Iff.rfl

theorem natCast_mem_primeOf {p : ℕ} [Fact p.Prime] {E : Type} [Field E] (φ : E →+* ℂ_[p]) :
    (p : 𝓞 E) ∈ primeOf φ := by
  rw [mem_primeOf]
  have h1 : ‖((p : ℚ_[p]) : ℂ_[p])‖ < 1 := by
    rw [PadicComplex.norm_extends', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  simpa using h1

theorem primeOf_isPrime {p : ℕ} [Fact p.Prime] {E : Type} [Field E] (φ : E →+* ℂ_[p]) : (primeOf φ).IsPrime := by
  refine ⟨?_, fun {a b} hab => ?_⟩
  · rw [Ne, Ideal.eq_top_iff_one, mem_primeOf]
    simp
  · rw [mem_primeOf, map_mul, map_mul, norm_mul] at hab
    rw [mem_primeOf, mem_primeOf]
    have ha : ‖φ (algebraMap (𝓞 E) E a)‖ ≤ 1 := norm_int_le φ a
    have hb : ‖φ (algebraMap (𝓞 E) E b)‖ ≤ 1 := norm_int_le φ b
    by_contra h
    rw [not_or, not_lt, not_lt] at h
    nlinarith [h.1, h.2, norm_nonneg (φ (algebraMap (𝓞 E) E a))]

theorem primeOf_isMaximal {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ_[p]) :
    (primeOf φ).IsMaximal := by
  refine (primeOf_isPrime φ).isMaximal ?_
  intro h
  have hp := natCast_mem_primeOf φ
  rw [h, Ideal.mem_bot] at hp
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp

end GlobalTheory.Proof.IdempotentLatticeSequence
