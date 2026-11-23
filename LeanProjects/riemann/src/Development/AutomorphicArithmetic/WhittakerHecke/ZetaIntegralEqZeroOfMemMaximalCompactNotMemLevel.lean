import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem loc_dv {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) {c d z n : K}
    (hc : w c ≤ 1) (hd : w d ≤ 1) (hn : w n ≤ 1) (h0 : w (z * c) ≤ w n) (h1 : w (z * d - 1) ≤ w n) : w c ≤ w n := by
  rcases lt_or_eq_of_le hn with hlt | heq
  · have h2 : w (z * d - 1) < w 1 := by rw [map_one]; exact h1.trans_lt hlt
    have h3 : w (z * d) = 1 := by
      have e : z * d = (z * d - 1) + 1 := by ring
      rw [e, Valuation.map_add_eq_of_lt_right w h2, map_one]
    have h4 : 1 ≤ w z := by
      rw [map_mul] at h3
      calc (1 : Γ) = w z * w d := h3.symm
        _ ≤ w z * 1 := mul_le_mul' le_rfl hd
        _ = w z := mul_one _
    calc w c = 1 * w c := (one_mul _).symm
      _ ≤ w z * w c := mul_le_mul' h4 le_rfl
      _ = w (z * c) := (map_mul _ _ _).symm
      _ ≤ w n := h0
  · rw [heq]
    exact hc

private theorem nat_le_one (v : H.P ℚ) (N : ℕ) : Valued.v (N : H.Kv v) ≤ 1 := by
  have h : (N : H.Kv v) ∈ v.adicCompletionIntegers ℚ := natCast_mem _ N
  exact h

theorem UpperTheory.zeta_integral_eq_zero_of_mem_maximal_compact_not_mem_level :
    ∀ (N : ℕ), 0 < N → ∀ (p : MvPolynomial (Fin 2) ℂ) (s : ℂ), ∀ k ∈ KK ℚ, k ∉ SS N → Zr N p s k = 0 := by
  intro N _ p s k hk hkS
  have hz : ∀ z : IdeleGroup ℚ, (PhiN N p fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j) = 0 := by
    intro z
    unfold PhiN
    rw [if_neg]
    intro h
    apply hkS
    intro v
    obtain ⟨h0, h1⟩ := h v
    have hint : ∀ i j, Valued.v (H.cp v (k i j)) ≤ 1 := fun i j => hk.2 v i j
    have e0 : H.cp v (((z : (A ℚ)ˣ) : A ℚ) * row k 0) = H.cp v ((z : (A ℚ)ˣ) : A ℚ) * H.cp v (k 1 0) := map_mul _ _ _
    have e1 : H.cp v (((z : (A ℚ)ˣ) : A ℚ) * row k 1 - 1) = H.cp v ((z : (A ℚ)ˣ) : A ℚ) * H.cp v (k 1 1) - 1 := by
      rw [map_sub, map_one]
      exact congrArg (· - 1) (map_mul _ _ _)
    have h0' : Valued.v (H.cp v (((z : (A ℚ)ˣ) : A ℚ) * row k 0)) ≤ Valued.v (N : H.Kv v) := h0
    have h1' : Valued.v (H.cp v (((z : (A ℚ)ˣ) : A ℚ) * row k 1 - 1)) ≤ Valued.v (N : H.Kv v) := h1
    rw [e0] at h0'
    rw [e1] at h1'
    exact loc_dv Valued.v (hint 1 0) (hint 1 1) (nat_le_one v N) h0' h1'
  simp only [Zr, hz, zero_mul, MeasureTheory.integral_zero]
