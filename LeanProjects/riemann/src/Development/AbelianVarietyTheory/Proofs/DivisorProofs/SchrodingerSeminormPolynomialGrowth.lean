import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairRApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTranslationSeminormBound
open scoped SchwartzMap

noncomputable section

namespace GlobalTheory.SchrPairingGrowth

open GlobalTheory.SchrPairing

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

def pairCLM {P : V → V → ℝ} (hP : GlobalTheory.ArchUniq.IsPairing P) : V →L[ℝ] (V →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := pairR hP
      map_add' := fun b b' => by ext y; simp [pairR_apply, hP.addR]
      map_smul' := fun c b => by ext y; simp [pairR_apply, hP.smulR] }

theorem seminorm_schrSch_sub_le {P : V → V → ℝ} (hP : GlobalTheory.ArchUniq.IsPairing P)
    (p : Seminorm ℂ 𝓢(V, ℂ)) (hp : Continuous p) :
    ∃ (q₁ q₂ q₃ : Seminorm ℂ 𝓢(V, ℂ)) (M₁ M₂ M₃ : ℕ), ∀ (w : V × V) (g : 𝓢(V, ℂ)),
      p (schrSch hP w g - g) ≤ (‖pairR hP w.2‖ + |P w.1 w.2 / 2|) * (1 + ‖pairR hP w.2‖) ^ M₁ *
          (‖w.1‖ * (1 + ‖w.1‖) ^ M₃ * q₃ g + q₁ g) + ‖w.1‖ * (1 + ‖w.1‖) ^ M₂ * q₂ g := by
  obtain ⟨q₁, M₁, hq₁, hb₁⟩ := GlobalTheory.PhaseLipschitz.seminorm_smulLeft_eChar_sub_le V p hp
  obtain ⟨q₂, M₂, -, hb₂⟩ := GlobalTheory.SchwartzTranslateLip.translate_sub_le V p hp
  obtain ⟨q₃, M₃, -, hb₃⟩ := GlobalTheory.SchwartzTranslateLip.translate_sub_le V q₁ hq₁
  refine ⟨q₁, q₂, q₃, M₁, M₂, M₃, fun w g => ?_⟩
  set T := SchwartzMap.compSubConstCLM ℂ (-w.1) g with hT
  have h1 := map_add_le_add p (SchwartzMap.smulLeftCLM ℂ
    (fun y => GlobalTheory.Published.Metaplectic.eChar ((-pairR hP w.2) y + -(P w.1 w.2 / 2))) T - T) (T - g)
  rw [sub_add_sub_cancel] at h1
  have e : schrSch hP w g = SchwartzMap.smulLeftCLM ℂ
    (fun y => GlobalTheory.Published.Metaplectic.eChar ((-pairR hP w.2) y + -(P w.1 w.2 / 2))) T := rfl
  rw [e]
  refine le_trans h1 (add_le_add ((hb₁ _ _ T).trans ?_) (hb₂ _ g))
  rw [norm_neg, abs_neg]
  have h2 := map_add_le_add q₁ (T - g) g
  rw [sub_add_cancel] at h2
  have h3 := hb₃ w.1 g
  gcongr
  linarith

theorem seminorm_schrSch_le : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {P : V → V → ℝ} (hP : GlobalTheory.ArchUniq.IsPairing P) (f : 𝓢(V, ℂ)), ∀ k m : ℕ, ∃ (C : ℝ) (N : ℕ), ∀ w : V × V,
    SchwartzMap.seminorm ℂ k m (GlobalTheory.SchrPairing.schrSch hP w f) ≤ C * (1 + ‖w‖) ^ N := by
  intro V _ _ _ P hP g k m
  obtain ⟨q₁, q₂, q₃, M₁, M₂, M₃, hb⟩ := seminorm_schrSch_sub_le hP (SchwartzMap.seminorm ℂ k m)
    ((schwartz_withSeminorms ℂ V ℂ).continuous_seminorm (k, m))
  set p := SchwartzMap.seminorm ℂ k m (E := V) (F := ℂ) with hpdef
  set c := ‖pairCLM hP‖ with hcdef
  set N := 3 + M₁ + M₂ + M₃ with hN
  have hq1 : 0 ≤ q₁ g := apply_nonneg _ _
  have hq2 : 0 ≤ q₂ g := apply_nonneg _ _
  have hq3 : 0 ≤ q₃ g := apply_nonneg _ _
  have hp : 0 ≤ p g := apply_nonneg _ _
  refine ⟨(1 + c) ^ N * (2 * q₃ g + 2 * q₁ g + q₂ g + p g), N, fun w => ?_⟩
  have hc : 0 ≤ c := norm_nonneg _
  have hw := norm_nonneg w
  set X := (1 + c) * (1 + ‖w‖) with hX
  have hX1 : 1 ≤ X := by rw [hX]; nlinarith
  have hw1 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
  have hw2 : ‖w.2‖ ≤ ‖w‖ := norm_snd_le w
  have hLb : ‖pairR hP w.2‖ ≤ c * ‖w.2‖ := (pairCLM hP).le_opNorm w.2
  have hL : ‖pairR hP w.2‖ ≤ c * ‖w‖ := hLb.trans (mul_le_mul_of_nonneg_left hw2 hc)
  have hP1 : |P w.1 w.2| ≤ ‖pairR hP w.2‖ * ‖w.1‖ := by
    have := (pairR hP w.2).le_opNorm w.1
    rwa [pairR_apply, Real.norm_eq_abs] at this
  have ha : 1 + ‖w.1‖ ≤ X := by rw [hX]; nlinarith
  have hb' : 1 + ‖pairR hP w.2‖ ≤ X := by rw [hX]; nlinarith
  have ha' : ‖w.1‖ ≤ X := by linarith
  have hb'' : ‖pairR hP w.2‖ ≤ X := by linarith
  have hk : ‖pairR hP w.2‖ + |P w.1 w.2 / 2| ≤ 2 * X ^ 2 := by
    have h2 : ‖pairR hP w.2‖ * ‖w.1‖ ≤ X * X := mul_le_mul hb'' ha' (norm_nonneg _) (by linarith)
    rw [abs_div, abs_two]
    nlinarith
  have hsub : p (schrSch hP w g) ≤ p (schrSch hP w g - g) + p g := by
    simpa using map_add_le_add p (schrSch hP w g - g) g
  calc p (schrSch hP w g) ≤ p (schrSch hP w g - g) + p g := hsub
    _ ≤ (2 * X ^ 2) * X ^ M₁ * (X * X ^ M₃ * q₃ g + q₁ g) + X * X ^ M₂ * q₂ g + p g := by
        refine add_le_add ((hb w g).trans ?_) le_rfl
        gcongr
    _ = 2 * X ^ (3 + M₁ + M₃) * q₃ g + 2 * X ^ (2 + M₁) * q₁ g + X ^ (1 + M₂) * q₂ g + 1 * p g := by ring
    _ ≤ 2 * X ^ N * q₃ g + 2 * X ^ N * q₁ g + X ^ N * q₂ g + X ^ N * p g := by
        have e1 : X ^ (3 + M₁ + M₃) ≤ X ^ N := pow_le_pow_right₀ hX1 (by omega)
        have e2 : X ^ (2 + M₁) ≤ X ^ N := pow_le_pow_right₀ hX1 (by omega)
        have e3 : X ^ (1 + M₂) ≤ X ^ N := pow_le_pow_right₀ hX1 (by omega)
        have e4 : (1 : ℝ) ≤ X ^ N := one_le_pow₀ hX1
        have f1 := mul_le_mul_of_nonneg_right e1 hq3
        have f2 := mul_le_mul_of_nonneg_right e2 hq1
        have f3 := mul_le_mul_of_nonneg_right e3 hq2
        have f4 := mul_le_mul_of_nonneg_right e4 hp
        nlinarith
    _ = (1 + c) ^ N * (2 * q₃ g + 2 * q₁ g + q₂ g + p g) * (1 + ‖w‖) ^ N := by
        rw [hX, mul_pow]; ring

end GlobalTheory.SchrPairingGrowth
