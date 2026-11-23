import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeOperatorsCommuteOnAutomorphicForms
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FixedSubgroup
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsOpenStabilizerAddSmul
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteSpanAddSmul
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ModerateGrowthAddSmul
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MirabolicRowCongruence

open UpperTheory.V.Sd UpperTheory.V.TR in
private theorem UpperTheory.Reformulated.B.Gr32.aut_zero {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F] :
    IsAutForm (0 : Sm F 2) := by
  refine ⟨fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · simp only [map_zero, Set.setOf_true, isOpen_univ]
  · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) ?_
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    simp
  · refine Submodule.finiteDimensional_of_le (S₂ := ⊥) ?_
    rw [Submodule.span_le]
    rintro _ ⟨k, _, rfl⟩
    simp
  · intro g
    exact ⟨0, 0, fun y => by simp⟩

open UpperTheory.V.Sd UpperTheory.V.TR in
private theorem UpperTheory.Reformulated.B.Gr32.aut_lin {F : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    {φ ψ : Sm F 2} (z : ℂ) (hφ : IsAutForm φ) (hψ : IsAutForm ψ) : IsAutForm (φ + z • ψ) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := hφ
  obtain ⟨b1, b2, b3, b4, b5⟩ := hψ
  refine ⟨fun γ g => ?_, UpperTheory.isOpen_stabilizer_add_smul _ φ ψ z a2 b2, ?_, UpperTheory.finite_span_add_smul (fun x => x) _ φ ψ z a4 b4, fun g => ?_⟩
  · change φ.1 _ + z * ψ.1 _ = φ.1 _ + z * ψ.1 _
    rw [a1, b1]
  · rw [← Set.image_univ] at a3 b3 ⊢
    exact UpperTheory.finite_span_add_smul (fun k => cptRep F 2 k) _ φ ψ z a3 b3
  · refine UpperTheory.moderate_growth_add_smul (fun y : GL (Fin 2) (Rinf F) => height y) (fun y => φ.1 (g * infGL F 2 y))
      (fun y => ψ.1 (g * infGL F 2 y)) z (fun y => ?_) (a5 g) (b5 g)
    unfold height
    have h1 := norm_nonneg (toL (y : Matrix (Fin 2) (Fin 2) (Rinf F)))
    have h2 := norm_nonneg (toL ((y⁻¹ : GL (Fin 2) (Rinf F)) : Matrix (Fin 2) (Fin 2) (Rinf F)))
    linarith

open UpperTheory.V.Sd in
private theorem UpperTheory.Reformulated.B.Gr32.principal_congruence_antitone {F : Type} [Field F] [NumberField F]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {m n : ℕ} (h : m ≤ n) :
    K1 w n ≤ K1 w m := by
  unfold K1
  refine Subgroup.map_mono fun g hg => ?_
  exact UpperTheory.mirabolic_row_congruence _ _ g (Ideal.pow_le_pow_right h) hg

open UpperTheory.V.Sd in
private theorem UpperTheory.Reformulated.B.Gr32.coefAt_lin {F : Type} [Field F] [NumberField F]
    (a b : Ideal (NumberField.RingOfIntegers F) → ℂ) (z : ℂ) (y : GlobalTheory.CuspRep.Af F) :
    coefAt (a + z • b) y = coefAt a y + z * coefAt b y := by
  unfold coefAt
  split_ifs <;> simp

open UpperTheory.V.Sd in
private theorem UpperTheory.Reformulated.B.Gr32.coefAt_zero {F : Type} [Field F] [NumberField F]
    (y : GlobalTheory.CuspRep.Af F) : coefAt (0 : Ideal (NumberField.RingOfIntegers F) → ℂ) y = 0 := by
  unfold coefAt
  split_ifs <;> simp

theorem UpperTheory.Reformulated.B.Gr32.holLin :
    UpperTheory.V.Sd.HolLin := by
  intro F _ _ _ k c ω
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨UpperTheory.Reformulated.B.Gr32.aut_zero, fun w => Submodule.zero_mem _, fun z g => ?_, fun v => ?_, fun v => ?_⟩
    · simp
    · simp
    · simp
  · intro x y _ yf
    simp only [UpperTheory.Reformulated.B.Gr32.coefAt_zero, zero_mul, Pi.zero_apply, zero_div, sub_zero]
    exact hasSum_zero
  · rintro φ ψ z ⟨a1, a2, a3, a4, a5⟩ ⟨b1, b2, b3, b4, b5⟩
    refine ⟨UpperTheory.Reformulated.B.Gr32.aut_lin z a1 b1,
      fun w => Submodule.add_mem _ (a2 w) (Submodule.smul_mem _ z (b2 w)), fun u g => ?_, fun v => ?_, fun v => ?_⟩
    · change φ.1 _ + z * ψ.1 _ = _ * (φ.1 _ + z * ψ.1 _)
      rw [a3, b3]
      ring
    · simp only [map_add, map_smul]
      linear_combination (norm := module) a4 v + z • b4 v
    · simp only [map_add, map_smul]
      linear_combination (norm := module) a5 v + z • b5 v
  · intro φ ψ z c₀ a d₀ b h1 h2 x y hy yf
    have h := (h1 x y hy yf).add ((h2 x y hy yf).mul_left z)
    convert h using 1
    · funext ξ
      rw [UpperTheory.Reformulated.B.Gr32.coefAt_lin]
      ring
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  · rintro φ c' hc ⟨a1, a2, a3, a4, a5⟩
    refine ⟨a1, fun w => ?_, a3, a4, a5⟩
    have h : φ ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd (UpperTheory.V.Sd.locSm F w) (UpperTheory.V.Sd.K1 w (c w)) := a2 w
    show φ ∈ UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd (UpperTheory.V.Sd.locSm F w) (UpperTheory.V.Sd.K1 w (c' w))
    exact fun g hg => h g (UpperTheory.Reformulated.B.Gr32.principal_congruence_antitone w (hc w) hg)
