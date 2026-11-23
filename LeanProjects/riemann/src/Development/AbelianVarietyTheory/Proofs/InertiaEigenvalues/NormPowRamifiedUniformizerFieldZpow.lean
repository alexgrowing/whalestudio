import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKur
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLocB

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.ValGroupKprime

theorem norm_Kunr (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] {c : Om l} (hc : c ∈ Kunr l a) (h0 : c ≠ 0) :
    ∃ m : ℤ, ‖c‖ = (l : ℝ) ^ m := by
  have hK : MaximalUnramifiedExtension l ≤ ReciprocityTheory.ChartRestriction.L1.kurAlg l := by
    refine IntermediateField.adjoin_le_iff.2 fun x ⟨m, hm, hlm, hx⟩ => ?_
    refine ReciprocityTheory.ChartRestriction.L1.mem_kurAlg.2
      (Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨m, hm, hlm, ?_⟩))
    rw [← map_pow, hx, map_one]
  have h1 := ReciprocityTheory.ChartRestriction.L1.mem_kurAlg.1 (hK (Kunr_le_Kur l a hc))
  obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.L1.kur_val l h1 ((map_ne_zero _).2 h0)
  exact ⟨m, by rw [← hm]; exact (PadicComplex.norm_extends l c).symm⟩

theorem norm_natCast_l (l : ℕ) [Fact l.Prime] : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  have := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [Padic.norm_p] at this
  simpa using this

theorem norm_pow_field (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e)
    (y : Om l) (hy : y ∈ (ϖ.field a).1) (h0 : y ≠ 0) : ∃ j : ℤ, ‖y‖ ^ e = (l : ℝ) ^ j := by
  set π := ϖ.seq 0 with hπdef
  set E := Kunr l a with hE
  have hπ0 : π ≠ 0 := ϖ.seq_ne_zero 0

  have hy' : y ∈ IntermediateField.adjoin E {π} := by
    have h1 : (ϖ.field a).1 = (IntermediateField.adjoin E {π}).restrictScalars ℚ_[l] := by
      rw [IntermediateField.restrictScalars_adjoin_eq_sup]; rfl
    rw [h1] at hy; exact hy
  have hint : IsAlgebraic E π :=
    (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) π).tower_top.isAlgebraic
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint] at hy'

  let M : Submodule E (Om l) := Submodule.span E (Set.range fun i : Fin e => π ^ (i : ℕ))
  have hlE : (-(l : Om l)) ∈ E := E.neg_mem (IntermediateField.natCast_mem E l)
  have hpow : ∀ n, π ^ n ∈ M := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < e
      · exact Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hn)
        have hk : k < e + k := by have := NeZero.pos e; omega
        have h2 : π ^ (e + k) = (⟨-(l : Om l), hlE⟩ : E) • π ^ k := by
          rw [pow_add, ϖ.seq_zero]; rfl
        rw [h2]; exact M.smul_mem _ (ih k hk)
  have hyM : y ∈ M := by
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
    obtain ⟨p, rfl⟩ := hy'
    show Polynomial.aeval π p ∈ M
    rw [Polynomial.aeval_eq_sum_range]
    exact Submodule.sum_mem _ fun i _ => M.smul_mem _ (hpow i)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hyM
  set t : Fin e → Om l := fun i => (c i : Om l) * π ^ (i : ℕ) with ht
  have hyt : y = ∑ i, t i := by rw [← hc]; rfl

  have hnπ : ‖π‖ ^ e = (l : ℝ)⁻¹ := by
    rw [← norm_pow, ϖ.seq_zero, norm_neg, norm_natCast_l]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith

  have hnt : ∀ i, t i ≠ 0 → ∃ m : ℤ, ‖t i‖ ^ e = (l : ℝ) ^ ((e : ℤ) * m - (i : ℕ)) := by
    intro i hi
    have hci : (c i : Om l) ≠ 0 := fun h => hi (by simp [ht, h])
    obtain ⟨m, hm⟩ := norm_Kunr l a (c i).2 hci
    refine ⟨m, ?_⟩
    rw [ht]; dsimp only
    rw [norm_mul, norm_pow, mul_pow, hm, ← pow_mul, mul_comm (i : ℕ) e, pow_mul, hnπ,
      zpow_sub₀ hl0.ne', inv_pow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm m, zpow_natCast, div_eq_mul_inv]

  have hdist : ∀ i j, t i ≠ 0 → t j ≠ 0 → ‖t i‖ = ‖t j‖ → i = j := by
    intro i j hi hj hij
    obtain ⟨m1, h1⟩ := hnt i hi
    obtain ⟨m2, h2⟩ := hnt j hj
    have h3 : (e : ℤ) * m1 - (i : ℕ) = (e : ℤ) * m2 - (j : ℕ) :=
      zpow_right_injective₀ hl0 hl1.ne' (show (l : ℝ) ^ _ = (l : ℝ) ^ _ by rw [← h1, ← h2, hij])
    have h4 : ((i : ℕ) : ℤ) - (j : ℕ) = 0 := by
      have hi' := i.2
      have hj' := j.2
      refine Int.eq_zero_of_abs_lt_dvd (m := (e : ℤ)) ⟨m1 - m2, by linear_combination -h3⟩ ?_
      rw [abs_lt]; constructor <;> omega
    exact Fin.ext (by omega)

  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => ‖t i‖)
    (Finset.univ_nonempty_iff.2 ⟨⟨0, NeZero.pos e⟩⟩)
  have ht0 : t i0 ≠ 0 := by
    intro h
    apply h0
    rw [hyt]
    refine Finset.sum_eq_zero fun i _ => norm_eq_zero.1 (le_antisymm ?_ (norm_nonneg _))
    simpa [h] using hi0 i (Finset.mem_univ _)
  have hpos : 0 < ‖t i0‖ := norm_pos_iff.2 ht0
  have hrest : ‖∑ i ∈ Finset.univ.erase i0, t i‖ < ‖t i0‖ := by
    obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finset_sum_le (Finset.univ.erase i0) t
    rcases (Finset.univ.erase i0).eq_empty_or_nonempty with hs | hs
    · rw [hs, Finset.sum_empty, norm_zero]; exact hpos
    have him := hi hs
    refine lt_of_le_of_lt hle ?_
    by_cases hti : t i = 0
    · rw [hti, norm_zero]; exact hpos
    refine lt_of_le_of_ne (hi0 i (Finset.mem_univ _)) fun h => ?_
    exact (Finset.mem_erase.1 him).1 (hdist i i0 hti ht0 h)
  have hy2 : ‖y‖ = ‖t i0‖ := by
    rw [hyt, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0),
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hrest.ne', max_eq_left hrest.le]
  obtain ⟨m, hm⟩ := hnt i0 ht0
  exact ⟨_, by rw [hy2, hm]⟩

end GlobalTheory.ValGroupKprime
