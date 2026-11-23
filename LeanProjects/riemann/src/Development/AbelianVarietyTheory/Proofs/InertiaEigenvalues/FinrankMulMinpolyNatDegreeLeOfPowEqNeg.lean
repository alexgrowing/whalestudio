import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

open IntermediateField in

theorem GlobalTheory.finrank_mul_minpoly_natDegree_le_of_pow_eq_neg : ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (Om l)) (N : ℕ) (x : Om l), 0 < N → x ^ N = -(l : Om l) → F ≤ IntermediateField.adjoin ℚ_[l] {x} → Module.finrank ℚ_[l] F * (minpoly F x).natDegree ≤ N := by
  intro l _ F N x hN hx hF
  have hp : (Polynomial.X ^ N + Polynomial.C (l : ℚ_[l])).Monic :=
    Polynomial.monic_X_pow_add_C _ hN.ne'
  have hroot : Polynomial.aeval x (Polynomial.X ^ N + Polynomial.C (l : ℚ_[l])) = 0 := by simp [hx]
  have hint : IsIntegral ℚ_[l] x := ⟨_, hp, hroot⟩
  have hdeg : (minpoly ℚ_[l] x).natDegree ≤ N := by
    have h1 := minpoly.min ℚ_[l] x hp hroot
    rw [Polynomial.degree_X_pow_add_C hN] at h1
    exact Polynomial.natDegree_le_of_degree_le h1
  have hintF : IsIntegral F x := hint.tower_top
  have key := Module.finrank_mul_finrank ℚ_[l] F (F⟮x⟯)
  have hE : (F⟮x⟯).restrictScalars ℚ_[l] = ℚ_[l]⟮x⟯ := by
    rw [restrictScalars_adjoin]
    apply le_antisymm
    · rw [adjoin_le_iff]
      rintro y (hy | hy)
      · exact hF hy
      · rw [Set.mem_singleton_iff.mp hy]; exact mem_adjoin_simple_self _ _
    · exact adjoin.mono _ _ _ (Set.subset_union_right)
  have h2 : Module.finrank ℚ_[l] (F⟮x⟯) = Module.finrank ℚ_[l] (ℚ_[l]⟮x⟯) := by
    rw [← hE]; rfl
  rw [← adjoin.finrank hintF, key, h2, adjoin.finrank hint]
  exact hdeg
