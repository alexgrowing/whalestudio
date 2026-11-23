import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionZeroOnePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormCoeffWittDiscStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem le_one_of_mul_pow_le_one (c : ℝ) (n : ℕ) (h : ∀ t : ℝ≥0, t < 1 → c * (t : ℝ) ^ n ≤ 1) : c ≤ 1 := by
  have ht : Filter.Tendsto (fun t : ℝ≥0 => c * (t : ℝ) ^ n) (nhdsWithin (1 : ℝ≥0) (Set.Iio 1)) (nhds (c * ((1 : ℝ≥0) : ℝ) ^ n)) :=
    ((continuous_const.mul ((NNReal.continuous_coe).pow n)).tendsto 1).mono_left nhdsWithin_le_nhds
  have : (nhdsWithin (1 : ℝ≥0) (Set.Iio 1)).NeBot := nhdsWithin_Iio_self_neBot' ⟨0, zero_lt_one⟩
  have h2 := le_of_tendsto ht (eventually_nhdsWithin_of_forall fun t (hti : t ∈ Set.Iio 1) => h t hti)
  simpa using h2

theorem disc_bdd_isSeries : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ y : bk.DS ρ, (∀ ρ₁ : ℝ≥0, ρ₁ < 1 → ∃ (ρ' : ℝ≥0) (R : bk.DS ρ' →+* bk.DS ρ) (y' : bk.DS ρ'), ρ₁ ≤ ρ' ∧ ρ ≤ ρ' ∧ ρ' < 1 ∧ IsDiscMap (RingHom.id bk.S) R ∧ R y' = y ∧ ‖y'‖ ≤ 1) → ∃ a, toDisc l (X : bk.S) ρ a = y := by
  intro l _ K bk ρ hρ hρ1 y hy
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  obtain ⟨a, ha1, ha2, ha3, -⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ hρ hρ1
  obtain ⟨-, hk2, -, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_zero_one_properties l K bk

  have hcont : ∀ (r : ℝ≥0), 0 < r → ∀ (b : ℕ → (bk.DS r →+ Disc l (0 : Wq l bk.a) 1)),
      (∀ n z, ‖b n z‖ * (r : ℝ) ^ n ≤ ‖z‖) → ∀ n, Continuous (b n) := by
    intro r hr b hb n
    refine AddMonoidHomClass.continuous_of_bound (b n) (((r : ℝ) ^ n)⁻¹) fun z => ?_
    have hp : (0 : ℝ) < (r : ℝ) ^ n := pow_pos (by exact_mod_cast hr) n
    rw [inv_mul_eq_div, le_div_iff₀ hp]
    exact hb n z

  have htor : ∀ z : Disc l (0 : Wq l bk.a) 1, l • z = 0 → z = 0 := by
    intro z hz
    have h := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Wq l bk.a) (0 : Wq l bk.a) 1).2.1 z
    rw [← nsmul_eq_mul, hz, norm_zero] at h
    exact norm_eq_zero.1 (by
      have := (div_eq_zero_iff.1 h.symm).resolve_right hl0.ne'
      exact this)

  have hle : ∀ n, ‖a n y‖ ≤ 1 := by
    intro n
    refine le_one_of_mul_pow_le_one _ n fun t ht => ?_
    obtain ⟨ρ', R, y', h1, h2, h3, hR, hRy, hy'⟩ := hy t ht
    have hρ' : 0 < ρ' := hρ.trans_le h2
    obtain ⟨a', ha1', ha2', -, -⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ' hρ' h3
    have hRc : Continuous R := AddMonoidHomClass.continuous_of_bound R 1 fun z => (hR.norm_le z).trans (one_mul _).ge
    have e : ((a n).comp (R : bk.DS ρ' →+ bk.DS ρ)) = a' n :=
      (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l bk.S (X : bk.S) ρ').2.2.1 _ htor _ _ ((hcont ρ hρ a ha2 n).comp hRc)
        (hcont ρ' hρ' a' ha2' n) fun x => by
          simp only [AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Function.comp_apply]
          rw [hR.ext x, RingHom.id_apply, ha1, ha1']
    have e2 : a n y = a' n y' := by rw [← hRy, ← e]; rfl
    rw [e2]
    calc ‖a' n y'‖ * (t : ℝ) ^ n ≤ ‖a' n y'‖ * (ρ' : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ t.2 (by exact_mod_cast h1) n) (norm_nonneg _)
      _ ≤ ‖y'‖ := ha2' n y'
      _ ≤ 1 := hy'
  choose w hw using fun n => hk2 (a n y) (hle n)
  refine ⟨PowerSeries.mk w, ?_⟩
  have h0 : ‖y - toDisc l (X : bk.S) ρ (PowerSeries.mk w)‖ ≤ 0 :=
    ha3 _ 0 le_rfl fun n => by
      rw [map_sub, ha1, coeff_mk, ← hw, sub_self, norm_zero, zero_mul]
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 h0)).symm

end GlobalTheory.BSP
