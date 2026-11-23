import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma exists_close {E : Type} [Field E] [NumberField E] (c : InfinitePlace E → E) :
    ∃ x : E, ∀ v : InfinitePlace E, v (x - c v) < 1 / 2 := by
  have hd := InfinitePlace.denseRange_algebraMap_pi E
  obtain ⟨x, hx⟩ := hd.exists_dist_lt (fun v : InfinitePlace E => WithAbs.toAbs v.1 (c v))
    (by norm_num : (0:ℝ) < 1/2)
  refine ⟨x, fun v => ?_⟩
  have h1 := (dist_le_pi_dist _ _ v).trans_lt hx
  rw [dist_comm, dist_eq_norm] at h1
  exact h1

theorem UpperTheory.Gal.W2.Seed.pCEx :
    CEx := by
  intro E _ _ _ τ₀ M hM
  classical
  obtain ⟨x, hx⟩ := exists_close (E := E) (fun v => if v = InfinitePlace.mk τ₀ then -1 else 1)
  have hbound : ∀ τ : E →+* ℂ,
      |(τ x).re - (if InfinitePlace.mk τ = InfinitePlace.mk τ₀ then -1 else 1)| < 1 / 2 := by
    intro τ
    have h : ‖τ (x - (if InfinitePlace.mk τ = InfinitePlace.mk τ₀ then -1 else 1))‖ < 1 / 2 :=
      hx (InfinitePlace.mk τ)
    refine lt_of_le_of_lt ?_ h
    split_ifs with hτ
    · have := Complex.abs_re_le_norm (τ x - -1)
      simpa using this
    · have := Complex.abs_re_le_norm (τ x - 1)
      simpa using this
  have hxalg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hyint⟩ := IsAlgebraic.exists_integral_multiple hxalg
  set z : E := y • (y • x) with hzdef
  have hz : IsIntegral ℤ z := hyint.smul y
  have hyR : (y : ℝ) ≠ 0 := by exact_mod_cast hy0
  have hy2 : 0 < (y : ℝ) ^ 2 := by positivity
  have hτz : ∀ τ : E →+* ℂ, (τ z).re = (y : ℝ) ^ 2 * (τ x).re := by
    intro τ
    simp [hzdef, zsmul_eq_mul]
    ring
  set w : E := z + IsCMField.complexConj E z with hwdef
  have hw : IsIntegral ℤ w := hz.add (map_isIntegral_int (IsCMField.complexConj E) hz)
  have hτw : ∀ τ : E →+* ℂ, (τ w).re = 2 * (τ z).re := by
    intro τ
    simp [hwdef, IsCMField.complexEmbedding_complexConj]
    ring
  have hneg : (τ₀ w).re < 0 := by
    have hb := hbound τ₀
    rw [if_pos rfl] at hb
    have := (abs_lt.mp hb).2
    rw [hτw, hτz]
    nlinarith
  have hpos : ∀ τ : E →+* ℂ, InfinitePlace.mk τ ≠ InfinitePlace.mk τ₀ → 0 < (τ w).re := by
    intro τ hτ
    have hb := hbound τ
    rw [if_neg hτ] at hb
    have := (abs_lt.mp hb).1
    rw [hτw, hτz]
    nlinarith
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / ((M : ℝ) * -(τ₀ w).re))
  have hKM : 1 < (M : ℝ) * K * -(τ₀ w).re := by
    have hd : 0 < (M : ℝ) * -(τ₀ w).re := by nlinarith
    rw [div_lt_iff₀ hd] at hK
    nlinarith
  let wO : 𝓞 E := ⟨w, (mem_integralClosure_iff ℤ E).mpr hw⟩
  have hcoe : (((1 : 𝓞 E) + (M : 𝓞 E) * ((K : 𝓞 E) * wO) : 𝓞 E) : E) = 1 + (M : E) * ((K : E) * w) := by
    push_cast
    rfl
  have hre : ∀ τ : E →+* ℂ, (τ (1 + (M : E) * ((K : E) * w))).re = 1 + (M : ℝ) * K * (τ w).re := by
    intro τ
    simp
    ring
  refine ⟨1 + (M : 𝓞 E) * ((K : 𝓞 E) * wO), ?_, ?_, ?_, (K : 𝓞 E) * wO, rfl⟩
  · rw [hcoe]
    simp [hwdef, add_comm]
  · rw [hcoe, hre]
    linarith
  · intro τ hτ
    rw [hcoe, hre]
    have := hpos τ hτ
    have : 0 ≤ (M : ℝ) * K * (τ w).re := by positivity
    linarith
