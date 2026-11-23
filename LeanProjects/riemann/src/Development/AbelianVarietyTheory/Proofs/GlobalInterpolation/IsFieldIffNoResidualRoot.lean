import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.QuadFieldCriterion
open Polynomial IsLocalRing

theorem exists_root_of_residual {O : Type*} [CommRing O] [IsLocalRing O]
    [HenselianRing O (maximalIdeal O)] (t n : O) (hd : IsUnit (t ^ 2 - 4 * n))
    (r : ResidueField O) (hr : r ^ 2 - residue O t * r + residue O n = 0) :
    ∃ s : O, s ^ 2 - t * s + n = 0 := by
  obtain ⟨r₀, rfl⟩ := residue_surjective r
  have hmon : (X ^ 2 - C t * X + C n : O[X]).Monic := by monicity!
  have h0 : r₀ ^ 2 - t * r₀ + n ∈ maximalIdeal O := by
    rw [← residue_eq_zero_iff]; simpa using hr
  obtain ⟨s, hs, -⟩ := HenselianRing.is_henselian (I := maximalIdeal O) _ hmon r₀
    (by simpa using h0) (by
      have h1 : IsUnit (residue O (t ^ 2 - 4 * n)) := hd.map _
      have h2 : residue O (t ^ 2 - 4 * n) = (residue O (2 * r₀ - t)) ^ 2 := by
        simp only [map_sub, map_pow, map_mul, map_ofNat]
        linear_combination (-4) * hr
      rw [h2, isUnit_pow_iff two_ne_zero] at h1
      have h3 : eval r₀ (derivative (X ^ 2 - C t * X + C n : O[X])) = 2 * r₀ - t := by
        simp; norm_num
      rw [h3]
      exact h1)
  exact ⟨s, by simpa using hs⟩

theorem exists_root_of_fraction {O K : Type*} [CommRing O] [IsDomain O] [IsIntegrallyClosed O]
    [Field K] [Algebra O K] [IsFractionRing O K] (t n : O) (x : K)
    (hx : x ^ 2 - algebraMap O K t * x + algebraMap O K n = 0) :
    ∃ s : O, s ^ 2 - t * s + n = 0 := by
  have hmon : (X ^ 2 - C t * X + C n : O[X]).Monic := by monicity!
  have hi : IsIntegral O x := ⟨_, hmon, by simpa using hx⟩
  obtain ⟨s, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  refine ⟨s, IsFractionRing.injective O K ?_⟩
  simpa using hx

theorem isField_iff_no_root {K A : Type*} [Field K] [CommRing A] [Algebra K A] (w : A) (t n : K)
    (hw : w ^ 2 - algebraMap K A t * w + algebraMap K A n = 0)
    (hspan : ∀ z : A, ∃ a b : K, z = algebraMap K A a + algebraMap K A b * w)
    (hind : ∀ a b : K, algebraMap K A a + algebraMap K A b * w = 0 → a = 0 ∧ b = 0) :
    IsField A ↔ ¬ ∃ x : K, x ^ 2 - t * x + n = 0 := by
  constructor
  · rintro hF ⟨x, hx⟩
    letI := hF.toField
    have hx' : algebraMap K A x ^ 2 - algebraMap K A t * algebraMap K A x + algebraMap K A n = 0 := by
      simpa using congrArg (algebraMap K A) hx
    have hprod : (algebraMap K A (-x) + algebraMap K A 1 * w) *
        (algebraMap K A (x - t) + algebraMap K A 1 * w) = 0 := by
      simp only [map_neg, map_sub, map_one]
      linear_combination hw - hx'
    rcases mul_eq_zero.mp hprod with h | h
    · exact one_ne_zero (hind _ _ h).2
    · exact one_ne_zero (hind _ _ h).2
  · intro hno
    refine ⟨⟨1, 0, fun h => one_ne_zero (hind 1 0 (by simpa using h)).1⟩, mul_comm, ?_⟩
    intro z hz
    obtain ⟨a, b, rfl⟩ := hspan z
    have hN : a ^ 2 + t * a * b + n * b ^ 2 ≠ 0 := by
      intro hN
      by_cases hb : b = 0
      · subst hb
        have : a = 0 := by simpa using hN
        subst this
        simp at hz
      · exact hno ⟨-a / b, by field_simp; linear_combination hN⟩
    refine ⟨algebraMap K A (a ^ 2 + t * a * b + n * b ^ 2)⁻¹ *
      (algebraMap K A a + algebraMap K A b * (algebraMap K A t - w)), ?_⟩
    have h1 : algebraMap K A (a ^ 2 + t * a * b + n * b ^ 2)⁻¹ *
        algebraMap K A (a ^ 2 + t * a * b + n * b ^ 2) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hN, map_one]
    rw [← h1]
    simp only [map_add, map_mul, map_pow]
    linear_combination (- algebraMap K A (a ^ 2 + t * a * b + n * b ^ 2)⁻¹ *
      algebraMap K A b ^ 2) * hw

theorem isField_iff_no_residual_root : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (A : Type) [CommRing A] [Algebra (Fv F v) A] (w : A) (t n : v.adicCompletionIntegers F), IsUnit (t ^ 2 - 4 * n) → w ^ 2 - algebraMap (Fv F v) A t * w + algebraMap (Fv F v) A n = 0 → (∀ z : A, ∃ a b : Fv F v, z = algebraMap (Fv F v) A a + algebraMap (Fv F v) A b * w) → (∀ a b : Fv F v, algebraMap (Fv F v) A a + algebraMap (Fv F v) A b * w = 0 → a = 0 ∧ b = 0) → (IsField A ↔ ¬ ∃ r : IsLocalRing.ResidueField (v.adicCompletionIntegers F), r ^ 2 - IsLocalRing.residue (v.adicCompletionIntegers F) t * r + IsLocalRing.residue (v.adicCompletionIntegers F) n = 0) := by
  intro F _ _ v A _ _ w t n hd hw hspan hind
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  rw [isField_iff_no_root w _ _ hw hspan hind]
  refine not_congr ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨s, hs⟩ := exists_root_of_fraction (K := Fv F v) t n x hx
    exact ⟨residue _ s, by simpa using congrArg (residue _) hs⟩
  · rintro ⟨r, hr⟩
    obtain ⟨s, hs⟩ := exists_root_of_residual t n hd r hr
    exact ⟨(s : Fv F v), by
      simpa using congrArg (algebraMap (v.adicCompletionIntegers F) (Fv F v)) hs⟩

end GlobalTheory.QuadFieldCriterion
