import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.WtMatFix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Polynomial

theorem UpperTheory.exists_crystalline_unit_frobenius_eigen :
    ∀ (l : ℕ) [Fact l.Prime] (a : ℤ), ∃ u : (Bcr l)ˣ, (PP l).ιB (u : Bcr l) ∈ ((PP l).PD (botExt l)).Fil a ∧ (PP l).φB (u : Bcr l) = algebraMap ℚ_[l] (Bcr l) ((l : ℚ_[l]) ^ a) * (u : Bcr l) := by
  intro l _ a
  obtain ⟨T⟩ := tiedP l
  obtain ⟨t, ht⟩ := ((PP l).PD (botExt l)).t_unit
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  refine ⟨t ^ a, ?_, ?_⟩
  · have h := GlobalTheory.DRFil.tdR_zpow_mem T (botExt l) a
    have e : GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR (PP l) (botExt l) =
        Units.map ((PP l).ιB : Bcr l →* (PP l).R.BdR) t := by
      ext
      change ((PP l).PD (botExt l)).ι ((PP l).PD (botExt l)).t = (PP l).ιB (t : Bcr l)
      rw [(PP l).PD_ι, ht]
    rw [e, ← map_zpow] at h
    exact h
  · have h1 : (PP l).φB (t : Bcr l) = algebraMap ℚ_[l] (Bcr l) (l : ℚ_[l]) * (t : Bcr l) := by
      have := ((PP l).PD (botExt l)).t_φ
      rw [(PP l).PD_φ, (PP l).PD_p, Algebra.smul_def, ← ht] at this
      exact this
    have e : Units.map ((PP l).φB : Bcr l →* Bcr l) t =
        Units.map (algebraMap ℚ_[l] (Bcr l) : ℚ_[l] →* Bcr l) (Units.mk0 _ hl) * t := Units.ext h1
    have e2 := congrArg (fun x : (Bcr l)ˣ => ((x ^ a : (Bcr l)ˣ) : Bcr l)) e
    simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map, Units.val_zpow_eq_zpow_val, Units.val_mk0] at e2
    exact e2
