import Mathlib
import Formalism.LocalRingCardinality.DataParams

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory

theorem typePrime_real_bound {C F N k b : ℝ} (hF0 : 0 ≤ F) (hN0 : 0 ≤ N)
    (hC : C ≤ b) (hF : F ≤ 5 * b) (hN : N ≤ 3 * (k * b)) (hk : 5 ≤ k) (hb : 1 ≤ b) :
    C * (F * N ^ 2 + N ^ 3) < (k * b) ^ 8 := by
  set y := k * b with hy
  have hby : 5 * b ≤ y := by rw [hy]; nlinarith
  have hy5 : 5 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have h1 : F * N ^ 2 + N ^ 3 ≤ y * (3 * y) ^ 2 + (3 * y) ^ 3 := by
    have hFy : F ≤ y := by linarith
    gcongr
  have h0 : 0 ≤ F * N ^ 2 + N ^ 3 := by positivity
  have h2 : C * (F * N ^ 2 + N ^ 3) ≤ y * (y * (3 * y) ^ 2 + (3 * y) ^ 3) :=
    mul_le_mul (by linarith) h1 h0 hy0.le
  have h3 : y * (y * (3 * y) ^ 2 + (3 * y) ^ 3) = 36 * y ^ 4 := by ring
  have h4 : (5 : ℝ) ^ 4 ≤ y ^ 4 := by gcongr
  have h5 : 0 < y ^ 4 := by positivity
  have h6 : y ^ 8 = y ^ 4 * y ^ 4 := by ring
  rw [h6]
  nlinarith

theorem typePrime_exceeds_constant :
    ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L → L.etaSz + D.R.t + L.Sc ≤ L.sc.b → 1 ≤ L.sc.b → ∀ CT : ℕ, (CT : ℝ) ≤ L.sc.b → (⌊L.etaSz⌋₊ + D.R.t + 1 < ⌊3 * L.sc.b⌋₊ + 2) ∧ ((⌊L.etaSz⌋₊ : ℝ) ≤ 2 * L.etaSz) ∧ ∀ k : Fin 2, CT * ((⌊3 * L.sc.b⌋₊ + 2 + 0) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) < D.host.g k := by
  intro D L P hsum hb CT hCT
  have heta := L.etaSz_pos
  have hSc := L.Sc_pos
  have hfl : (⌊L.etaSz⌋₊ : ℝ) ≤ L.etaSz := Nat.floor_le heta.le
  have ht0 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  refine ⟨?_, by linarith, fun i => ?_⟩
  · have : ⌊L.etaSz⌋₊ + D.R.t ≤ ⌊3 * L.sc.b⌋₊ := by
      apply Nat.le_floor
      push_cast
      linarith
    omega
  · obtain ⟨Y, hY, -, -, hg⟩ := P.g_Y
    have hgi := (hg i).1
    have hm := D.R.m_add_three_le_k
    have hm2 := D.R.two_le_m
    have hk5 : (5 : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : 5 ≤ D.R.k)
    have hnV : D.R.nV + 1 ≤ 2 * D.R.k + D.R.t := by
      unfold Ranks.nV Ranks.r
      omega
    have hnVR : (D.R.nV : ℝ) + 1 ≤ 2 * D.R.k + D.R.t := by exact_mod_cast hnV
    have hfl3 : (⌊3 * L.sc.b⌋₊ : ℝ) ≤ 3 * L.sc.b := Nat.floor_le (by linarith)
    have hN : (D.R.nV : ℝ) + 1 ≤ 3 * ((D.R.k : ℝ) * L.sc.b) := by nlinarith
    have key := typePrime_real_bound (C := (CT : ℝ)) (F := (⌊3 * L.sc.b⌋₊ : ℝ) + 2)
      (N := (D.R.nV : ℝ) + 1) (by positivity) (by positivity) hCT (by linarith) hN hk5 hb
    have : ((CT * ((⌊3 * L.sc.b⌋₊ + 2 + 0) * (D.R.nV + 1) ^ 2 + (D.R.nV + 1) ^ 3) : ℕ) : ℝ) <
        (D.host.g i : ℝ) := by
      push_cast
      simp only [add_zero]
      linarith
    exact_mod_cast this

end GlobalTheory
