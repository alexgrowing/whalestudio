import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscCoefficientsTopologicallyFreeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBreuilKisinIdealPowOfNormLeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinClosedDiscRestrictInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdIffDvdCoeffBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopologicalBasisBasicFactsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem toDisc_injective_of_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, 0 < ρ → ρ < 1 →
    Function.Injective (toDisc l (s X) ρ) ∧
    (∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ x : A, ‖toDisc l (s X) ρ x‖ ≤ r → x ∈ (bk.J ^ n).map s) ∧
    ∀ ρ' : ℝ≥0, 0 < ρ' → ρ' ≤ ρ → ∀ R : Disc l (s X) ρ →+* Disc l (s X) ρ', IsDiscMap (RingHom.id A) R →
      Function.Injective R := by
  intro l _ K bk A _ s ι TB ρ hρ hρ1
  have hH : IsHausdorff bk.J bk.S := bk.complete.toIsHausdorff
  obtain ⟨-, -, -, -, h5⟩ := GlobalTheory.T.topologicalBasis_basic_facts bk.S A s bk.J ι TB hH
  have hlW : (l : Wq l bk.a) ≠ 0 := WittVector.p_nonzero l (Fq l bk.a)
  have hCl : (C (l : Wq l bk.a) : bk.S) = (l : bk.S) := map_natCast _ l
  have hlS0 : (l : bk.S) ≠ 0 := by
    rw [← hCl]; exact fun h => hlW (C_injective (h.trans (map_zero _).symm))
  have hlA : (l : A) ∈ nonZeroDivisors A := by
    simpa [map_natCast] using h5 _ (mem_nonZeroDivisors_of_ne_zero hlS0)
  have htor : ∀ x : A, (l : A) * x = 0 → x = 0 := fun x hx =>
    (mem_nonZeroDivisors_iff_right.1 hlA x) (by rw [mul_comm]; exact hx)
  have hdvd : ∀ (m : ℕ) (x y : A), (l : A) * x = s X ^ m * y → s X ^ m ∣ x := by
    intro m x y hxy
    rw [← map_pow, GlobalTheory.T.dvd_iff_dvd_coeff_breuilKisin l K bk A s ι TB]
    intro i
    have e := congrArg (TB.c i) hxy
    rw [← map_natCast s l, ← map_pow, TB.c_mul, TB.c_mul] at e
    have hd : X ^ m ∣ (l : bk.S) * TB.c i x := ⟨_, e⟩
    rw [PowerSeries.X_pow_dvd_iff] at hd ⊢
    intro k hk
    have := hd k hk
    rw [← hCl, coeff_C_mul] at this
    exact (mul_eq_zero.1 this).resolve_left hlW
  have small := GlobalTheory.T.mem_breuilKisinIdeal_pow_of_norm_le l K bk A s htor hdvd ρ hρ hρ1
  refine ⟨?_, small, ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    have hmem : ∀ n : ℕ, x ∈ (bk.J.map s) ^ n := fun n => by
      obtain ⟨r, hr, h⟩ := small n
      rw [← Ideal.map_pow]
      exact h x (by rw [hx, norm_zero]; exact hr.le)
    have hHA : IsHausdorff (bk.J.map s) A := TB.complete.toIsHausdorff
    refine hHA.haus x fun n => ?_
    rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
    exact hmem n
  · intro ρ' hρ' hρ'ρ R hR
    have hρ'1 : ρ' < 1 := lt_of_le_of_lt hρ'ρ hρ1
    have h1 : ‖toDisc l (s X) ρ (s X)‖ ≤ ρ := by
      simpa using norm_toDisc_pow_le (l := l) (u := s X) (ρ := ρ) 1 hρ
    have h1' : ‖toDisc l (s X) ρ' (s X)‖ ≤ ρ' := by
      simpa using norm_toDisc_pow_le (l := l) (u := s X) (ρ := ρ') 1 hρ'
    have h2 : ‖toDisc l (X : bk.S) ρ' (RingHom.id bk.S X)‖ ≤ ρ := by
      have := norm_toDisc_pow_le (l := l) (u := (X : bk.S)) (ρ := ρ') 1 hρ'
      simp only [pow_one] at this
      exact this.trans (by exact_mod_cast hρ'ρ)
    obtain ⟨cD, hc1, -, hcn, -, -, hsup, -, -⟩ :=
      GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ hρ hρ1 (Disc.map s h1) (isDiscMap_map s h1)
    obtain ⟨cD', hc1', -, hcn', -, -, -, -, -⟩ :=
      GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ' hρ' hρ'1 (Disc.map s h1') (isDiscMap_map s h1')
    set RS : bk.DS ρ →+* bk.DS ρ' := Disc.map (RingHom.id bk.S) h2 with hRS
    have hRSd : IsDiscMap (RingHom.id bk.S) RS := isDiscMap_map _ h2
    have injS : Function.Injective RS := GlobalTheory.T.breuilKisin_closedDisc_restrict_injective l K bk ρ ρ' hρ' hρ'ρ hρ1 RS hRSd
    obtain ⟨-, hlnorm, -, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l bk.S (X : bk.S) ρ'
    obtain ⟨-, -, hext, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ
    have hlpos : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
    have htorD : ∀ z : bk.DS ρ', l • z = 0 → z = 0 := by
      intro z hz
      rw [nsmul_eq_mul] at hz
      have := hlnorm z
      rw [hz, norm_zero] at this
      exact norm_eq_zero.1 ((div_eq_zero_iff.1 this.symm).resolve_right hlpos.ne')
    have hRc : Continuous R :=
      AddMonoidHomClass.continuous_of_bound R 1 fun x => (hR.norm_le x).trans (one_mul _).ge
    have hRSc : Continuous RS :=
      AddMonoidHomClass.continuous_of_bound RS 1 fun x => (hRSd.norm_le x).trans (one_mul _).ge
    have key : ∀ i y, cD' i (R y) = RS (cD i y) := by
      intro i y
      have hF : Continuous ((cD' i).comp R.toAddMonoidHom) :=
        (AddMonoidHomClass.continuous_of_bound (cD' i) 1 fun z => (hcn' i z).trans (one_mul _).ge).comp hRc
      have hG : Continuous (RS.toAddMonoidHom.comp (cD i)) :=
        hRSc.comp (AddMonoidHomClass.continuous_of_bound (cD i) 1 fun z => (hcn i z).trans (one_mul _).ge)
      have := hext (bk.DS ρ') htorD ((cD' i).comp R.toAddMonoidHom) (RS.toAddMonoidHom.comp (cD i)) hF hG
        (fun a => by
          change cD' i (R (toDisc l (s X) ρ a)) = RS (cD i (toDisc l (s X) ρ a))
          rw [hR.ext, hc1, hc1', hRSd.ext]; rfl)
      exact DFunLike.congr_fun this y
    refine (injective_iff_map_eq_zero R).2 fun y hy => ?_
    have hz : ∀ i, cD i y = 0 := fun i =>
      injS (by rw [← key, hy, map_zero, map_zero])
    exact norm_le_zero_iff.1 (hsup y 0 le_rfl fun i => by rw [hz, norm_zero])

end GlobalTheory.BSP
