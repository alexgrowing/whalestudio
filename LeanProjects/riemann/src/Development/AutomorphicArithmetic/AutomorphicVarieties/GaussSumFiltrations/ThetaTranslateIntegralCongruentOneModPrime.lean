import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashUnnormalizedConstMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashRationalMatrixProperties
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IntMatrixIsometryPrimeOrderLatticeStability
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.GenByTranslationsInversions
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IntegralTestFunctionMulTraceCharacterQuadFormOfD
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaSeriesCongrOneModPOfIsometry
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IntegralTestFunctionFiniteFourierTransformOfOddP
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HasQExpansionAffineTranslateCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaSeriesTranslationTwistsCoefficients
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsFiniteRepsScaledLatticeCardNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertThetaSeriesPeriodicInversionFormula
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem theta_translates_integral_one : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ γ : GL (Fin 2) F, InG p δ γ → Small ι (p : ℝ)⁻¹ (sl0 (p - 1) (toInf γ) (th G oneL) - 1) := by
  intro F _ _ _ p _ ι hp2 δ hδ κ _ _ G S t hL γ hγ

  have hPos : ∀ g : GL (Fin 2) F, TP g.val.det → Pos (toInf g) := fun g hg =>
    ((GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash F (p - 1) (th G oneL)).2.1 g).1.2 hg
  have hTP1 : TP (1 : F) := fun v => by simp [reAt]
  have hdetw : ∀ c : Fˣ, (wm c).val.det = 1 := fun c => by
    simp [wm, Matrix.det_fin_two]
  have hdeta : ∀ (e : Fˣ) (b : F), (aff e b).val.det = e := fun e b => by
    simp [aff, Matrix.det_fin_two]
  have hPw : ∀ c : Fˣ, Pos (toInf (wm c)) := fun c => hPos _ (by rw [hdetw]; exact hTP1)
  have hPa : ∀ b : F, Pos (toInf (aff 1 b)) := fun b => hPos _ (by rw [hdeta]; simpa using hTP1)

  have haL1 : ∀ x : κ → F, x ∈ aL κ (1 : F) ↔ x ∈ LL F κ := fun x => by
    simp [aL, AddSubgroup.mem_map]
  have hone : ∀ x y : κ → F, (x ∈ LL F κ ↔ y ∈ LL F κ) → oneL x = oneL y := fun x y h => by
    by_cases hy : y ∈ LL F κ
    · rw [oneL, oneL, if_pos hy, if_pos (h.2 hy)]
    · rw [oneL, oneL, if_neg hy, if_neg fun hx => hy (h.1 hx)]

  have hgood1 : Good ι S (oneL (F := F) (κ := κ)) := by
    have hS := (GlobalTheory.HilbertThetaSeries.IsoP.isometry_order_p F p Fact.out κ G S t hL).2.1
    refine ⟨⟨1, one_pos, Nat.coprime_one_left p, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro x hx
      have hx' : x ∈ LL F κ := by
        by_contra h; exact hx (by simp [oneL, h])
      simpa [haL1] using hx'
    · intro x l hl
      have hl' : l ∈ LL F κ := by simpa [haL1] using hl
      exact hone _ _ ((LL F κ).add_mem_cancel_right hl')
    · intro x
      have h1 := ((hS x).2.2.2 1)
      rw [haL1, haL1] at h1
      exact hone _ _ h1
    · intro x
      unfold oneL; split_ifs <;> simp
    · have h0 : (0 : κ → F) ∈ LL F κ := (LL F κ).zero_mem
      simp only [oneL, h0, if_true, map_one, sub_self, norm_zero]
      positivity

  have hW : ∀ (c : Fˣ) (Φ : (κ → F) → ℂ), Good ι S Φ → PUnit p ((c : F) / δ) →
      ∃ Ψ, Good ι S Ψ ∧ sl0 (p - 1) (toInf (wm c)) (th G Φ) = th G Ψ := by
    intro c Φ hΦ hc
    obtain ⟨N, hN, hNp, hSB⟩ := hΦ.1
    have hNF : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
    have hint : IsIntegral ℤ ((N : F) / (N : F)⁻¹) := by
      rw [div_inv_eq_mul, ← Nat.cast_mul]
      simpa using isIntegral_algebraMap (R := ℤ) (A := F) (x := ((N * N : ℕ) : ℤ))
    obtain ⟨T, hT, h0T, hle, -⟩ := GlobalTheory.HilbertThetaSeries.exists_isReps_aL F κ (N : F) (N : F)⁻¹ hNF (inv_ne_zero hNF) hint
    refine ⟨_, GlobalTheory.T.integral_test_function_finite_fourier_transform_of_odd_prime F p ι hp2 δ hδ κ G S t hL Φ N T c hΦ hN hNp hSB hT h0T hc, ?_⟩
    exact GlobalTheory.T.hilbertThetaSeries_periodic_inversion_formula F κ G hL.pos t hL.det (p - 1) hL.card (N : F) (N : F)⁻¹ c T Φ hNF (inv_ne_zero hNF) hle hT hSB.1 hSB.2

  have hA : ∀ (b : F) (Φ : (κ → F) → ℂ), Good ι S Φ → PInt p (δ * b) →
      ∃ Ψ, Good ι S Ψ ∧ sl0 (p - 1) (toInf (aff 1 b)) (th G Φ) = th G Ψ := fun b Φ hΦ hb =>
    ⟨_, GlobalTheory.T.integral_test_function_mul_trace_character_quad_form_of_delta_integral F p ι δ hδ κ G S t hL Φ hΦ b hb, GlobalTheory.HilbertThetaSeries.th_translate F κ G (p - 1) b Φ⟩

  let P : GL (Fin 2) F → Prop := fun g => Pos (toInf g) ∧
    ∃ Ψ, Good ι S Ψ ∧ sl0 (p - 1) (toInf g) (th G oneL) = th G Ψ
  have step : ∀ g g' : GL (Fin 2) F, P g → Pos (toInf g') →
      (∀ Ψ, Good ι S Ψ → ∃ Ψ', Good ι S Ψ' ∧ sl0 (p - 1) (toInf g') (th G Ψ) = th G Ψ') → P (g * g') := by
    intro g g' ⟨hg, Ψ, hΨ, he⟩ hg' hstep
    have hc := SlashCocycle.slash_cocycle F (p - 1) (toInf g) (toInf g') (th G oneL) hg hg'
    obtain ⟨Ψ', hΨ', he'⟩ := hstep Ψ hΨ
    refine ⟨by rw [map_mul]; exact hc.1, Ψ', hΨ', ?_⟩
    rw [map_mul, hc.2.2.1, he, he']
  obtain ⟨b₁, b₂, b₃, c₁, c₂, c₃, ε, hb₁, hb₂, hb₃, hc₁, hc₂, hc₃, hε, hγe⟩ := GlobalTheory.HilbertThetaSeries.gen_by_translations_inversions F p Fact.out δ hδ γ hγ
  have P1 : P (wm c₁) := by
    refine ⟨hPw c₁, ?_⟩
    exact hW c₁ oneL hgood1 hc₁
  have P6 := step _ _ (step _ _ (step _ _ (step _ _ (step _ _ P1 (hPa b₁) (fun Ψ h => hA b₁ Ψ h hb₁))
    (hPw c₂) (fun Ψ h => hW c₂ Ψ h hc₂)) (hPa b₂) (fun Ψ h => hA b₂ Ψ h hb₂))
    (hPw c₃) (fun Ψ h => hW c₃ Ψ h hc₃)) (hPa b₃) (fun Ψ h => hA b₃ Ψ h hb₃)
  obtain ⟨hX, Ψ, hΨ, hXe⟩ := P6
  have hE : Pos (toInf (aff ε 0)) := hPos _ (by rw [hdeta]; exact hε)
  have hc := SlashCocycle.slash_cocycle F (p - 1) (toInf (wm c₁ * aff 1 b₁ * wm c₂ * aff 1 b₂ * wm c₃ * aff 1 b₃)) (toInf (aff ε 0)) (th G oneL) hX hE
  rw [hγe, map_mul, hc.2.2.1, hXe]

  have hden : ∀ z : Hn F, (∏ v, UpperHalfPlane.denom (cmp v (toInf (aff ε 0))) (z v)) = 1 := by
    intro z
    refine Finset.prod_eq_one fun v _ => ?_
    simp [UpperHalfPlane.denom, cmp, toInf, aff, Matrix.GeneralLinearGroup.map]
  have hsub : sl0 (p - 1) (toInf (aff ε 0)) (th G Ψ - 1) = sl0 (p - 1) (toInf (aff ε 0)) (th G Ψ) - 1 := by
    funext z
    simp [sl0, hden]
  rw [← hsub]
  obtain ⟨a, hQ, hbd⟩ := GlobalTheory.T.thetaSeries_congr_one_mod_p_of_isometry F p ι κ G S t hL Ψ hΨ
  refine ⟨_, GlobalTheory.T.hasQExpansion_affineTranslate_coeff F (p - 1) (th G Ψ - 1) a ε 0 hε hQ, fun ξ => ?_⟩
  simpa [et] using hbd (ξ / ε)

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_translate_integral_congruent_one_mod_prime : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ γ : GL (Fin 2) F, InG p δ γ → Small ι (p : ℝ)⁻¹ (sl0 (p - 1) (toInf γ) (th G oneL) - 1) := by
  first | exact @GlobalTheory.HilbertThetaSeries.theta_translates_integral_one | exact GlobalTheory.HilbertThetaSeries.theta_translates_integral_one | (intros; apply GlobalTheory.HilbertThetaSeries.theta_translates_integral_one <;> assumption)
