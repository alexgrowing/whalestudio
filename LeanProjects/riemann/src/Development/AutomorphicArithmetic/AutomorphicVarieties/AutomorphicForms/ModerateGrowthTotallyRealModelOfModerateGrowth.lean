import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelHeights.SiegelHeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AdelicHeightGeArchOpNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelSetInterTranslateFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SiegelSetHeightBound
open NumberField Matrix GlobalTheory.CuspRep GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V UpperTheory.V.Fb

private theorem one_le_ht {E : Type} [Field E] [NumberField E] {a : ℕ} (y : GL (Fin a) (TR.Rinf E)) :
    1 ≤ TR.height y := by
  unfold TR.height
  have h1 := norm_nonneg (TR.toL y.val)
  have h2 := norm_nonneg (TR.toL (y⁻¹).val)
  linarith

private theorem unif {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ} (φ : TR.Sm E a)
    (hU : IsOpen {k | TR.finRep E a k φ = φ})
    (hg : ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * TR.infGL E a y)‖ ≤ C * TR.height y ^ N)
    {Ω : Set (AdelicGLn.FiniteAdelicGL E a)} (hΩ : IsCompact Ω) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ l ∈ Ω, ∀ y, ‖φ.1 (finGL E a l * TR.infGL E a y)‖ ≤ C * TR.height y ^ N := by
  refine hΩ.induction_on (p := fun S => ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ l ∈ S, ∀ y,
    ‖φ.1 (finGL E a l * TR.infGL E a y)‖ ≤ C * TR.height y ^ N) ⟨0, 0, le_rfl, fun _ h => h.elim⟩ ?_ ?_ ?_
  · rintro S T hST ⟨C, N, h0, h⟩
    exact ⟨C, N, h0, fun l hl => h l (hST hl)⟩
  · rintro S T ⟨C, N, h0, h⟩ ⟨D, M, h1, h'⟩
    refine ⟨max C D, max N M, le_max_of_le_left h0, fun l hl y => ?_⟩
    have hy := one_le_ht y
    rcases hl with hl | hl
    · exact (h l hl y).trans (mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ hy (le_max_left _ _))
        (pow_nonneg (zero_le_one.trans hy) _) (le_max_of_le_left h0))
    · exact (h' l hl y).trans (mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hy (le_max_right _ _))
        (pow_nonneg (zero_le_one.trans hy) _) (le_max_of_le_left h0))
  · intro k _
    obtain ⟨C, N, h⟩ := hg (finGL E a k)
    have ho : IsOpen ((fun l : AdelicGLn.FiniteAdelicGL E a => k⁻¹ * l) ⁻¹' {k | TR.finRep E a k φ = φ}) :=
      hU.preimage (continuous_const.mul continuous_id)
    refine ⟨_, mem_nhdsWithin_of_mem_nhds (ho.mem_nhds ?_), |C|, N, abs_nonneg C, fun l hl y => ?_⟩
    · change TR.finRep E a (k⁻¹ * k) φ = φ
      rw [inv_mul_cancel, map_one]
      rfl
    · have e : φ.1 (finGL E a k * TR.infGL E a y * finGL E a (k⁻¹ * l)) = φ.1 (finGL E a k * TR.infGL E a y) :=
        congrFun (congrArg Subtype.val hl) _
      rw [mul_assoc, TR.infGL_comm, ← mul_assoc, ← map_mul, mul_inv_cancel_left] at e
      rw [e]
      exact (h y).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (zero_le_one.trans (one_le_ht y)) _))

theorem UpperTheory.moderateGrowth_totallyRealModel_of_moderateGrowth :
    UpperTheory.V.Fb.GrowthTo := by
  intro E _ _ _ a φ hl hU hg
  obtain ⟨ω, hω, hB, t, ht, hred⟩ := Reduction.exists_siegelSet (K := E) a
  obtain ⟨Ω, hΩ, hfin⟩ := UpperTheory.siegelSet_inter_translate_finite E a ω hω t
  obtain ⟨D, M, hD⟩ := UpperTheory.siegelSet_height_bound E a ω hω hB t ht
  obtain ⟨C, N, h0, hC⟩ := unif φ hU hg hΩ
  refine ⟨C * (3 * D) ^ N, M * N, fun g => ?_⟩
  obtain ⟨γ, hγ⟩ := hred g
  have h1 := hC _ (hfin _ hγ) (GeneralLinearGroup.map (TR.pInf E) (AdelicGLn.diagonal E a γ * g))
  have h2 := UpperTheory.adelicHeight_ge_archOpNorm E a (AdelicGLn.diagonal E a γ * g)
  have h3 := hD g γ hγ
  have e : finGL E a (finPart (AdelicGLn.diagonal E a γ * g)) *
      TR.infGL E a (GeneralLinearGroup.map (TR.pInf E) (AdelicGLn.diagonal E a γ * g)) = ratGL E a γ * g :=
    (TR.infGL_comm _ _).symm.trans (TR.infGL_mul_finGL (AdelicGLn.diagonal E a γ * g))
  rw [e, hl] at h1
  refine h1.trans ?_
  rw [mul_assoc C, pow_mul, ← mul_pow]
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (one_le_ht _)) ?_ N) h0
  rw [mul_assoc]
  linarith
