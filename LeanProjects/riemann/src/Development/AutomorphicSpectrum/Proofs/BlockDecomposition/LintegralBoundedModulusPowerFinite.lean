import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.MHInt

theorem lintegral_indicator_modulus_rpow_lt_top :
    ForS fun F _ _ _ _ _ _ _ => ∀ B e : ℝ, 0 < e →
      ∫⁻ a : Fˣ, Set.indicator {a : Fˣ | (modulus (a : F) : ℝ) ≤ B}
        (fun a => ENNReal.ofReal ((modulus (a : F) : ℝ) ^ e)) a ∂multHaar F < ⊤ := by
  intro F _ _ _ _ _ _ _ _ B e he
  have hq1' : (1 : ℝ) < (residueCard F : ℝ) := by exact_mod_cast one_lt_residueCard (K := F)
  set q : ℝ := (residueCard F : ℝ) with hq
  have hq1 : 1 < q := hq1'
  have hq0 : 0 < q := by linarith
  set ρ : ℝ := q ^ (-e) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos hq0 _
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hq1
  let a : ℤ → ℝ := fun k => if -(n : ℤ) ≤ k then ρ ^ k else 0
  have ha0 : ∀ k, 0 ≤ a k := fun k => by
    simp only [a]
    split_ifs
    · exact zpow_nonneg hρ0.le _
    · exact le_rfl
  have hsum : HasSum a (ρ ^ (-(n : ℤ)) * (1 - ρ)⁻¹) := by
    refine hasSum_int_of_shift (-(n : ℤ)) (fun k hk => by simp [a, not_le.mpr hk]) ?_
    have e' : (fun m : ℕ => a (-(n : ℤ) + m)) = fun m : ℕ => ρ ^ (-(n : ℤ)) * ρ ^ m := by
      funext m
      simp only [a, le_add_iff_nonneg_right, Nat.cast_nonneg, if_true]
      rw [zpow_add₀ hρ0.ne', zpow_natCast]
    rw [e']
    exact (hasSum_geometric_of_lt_one hρ0.le hρ1).mul_left _
  have hbound : ∀ u : Fˣ, Set.indicator {a : Fˣ | (modulus (a : F) : ℝ) ≤ B}
      (fun a => ENNReal.ofReal ((modulus (a : F) : ℝ) ^ e)) u
        ≤ ENNReal.ofReal (a (ord (u : F))) := by
    intro u
    by_cases hu : u ∈ {a : Fˣ | (modulus (a : F) : ℝ) ≤ B}
    · have hmod : (modulus (u : F) : ℝ) = q ^ (-ord (u : F)) := by
        rw [modulus_of_ne_zero u.ne_zero]
        push_cast
        rfl
      have hk : -(n : ℤ) ≤ ord (u : F) := by
        have h1 : q ^ (-ord (u : F)) < q ^ (n : ℤ) := by
          rw [zpow_natCast, ← hmod]
          exact lt_of_le_of_lt hu hn
        have := (zpow_lt_zpow_iff_right₀ hq1).1 h1
        omega
      simp only [a, Set.indicator_of_mem hu, if_pos hk]
      apply ENNReal.ofReal_le_ofReal
      refine le_of_eq ?_
      rw [hmod, hρ, ← Real.rpow_intCast q, ← Real.rpow_mul hq0.le,
        ← Real.rpow_intCast (q ^ (-e)), ← Real.rpow_mul hq0.le]
      congr 1
      push_cast
      ring
    · simp [Set.indicator_of_notMem hu]
  refine (lintegral_multHaar_le_tsum _ (fun k => ENNReal.ofReal (a k)) hbound).trans_lt ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg ha0 hsum.summable]
  exact ENNReal.ofReal_lt_top

end GlobalTheory.CompanionTheory.MHInt
