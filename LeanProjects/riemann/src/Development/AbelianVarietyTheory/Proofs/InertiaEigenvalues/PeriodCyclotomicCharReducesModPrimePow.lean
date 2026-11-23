import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterCongrRootOfUnityPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CycLevel

theorem toZModPow_eq_of_norm_sub_le {l : ℕ} [Fact l.Prime] (u : ℤ_[l]) (a : ℕ) (r : ℕ)
    (h : ‖(u : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(r : ℤ))) :
    (PadicInt.toZModPow r u : ZMod (l ^ r)) = (a : ZMod (l ^ r)) := by
  have h1 : ‖u - (a : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by
    rw [PadicInt.norm_def]; push_cast; exact h
  have h2 := (PadicInt.norm_le_pow_iff_mem_span_pow (u - (a : ℤ_[l])) r).mp h1
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at h2
  exact h2

theorem chi_reduces (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (r : ℕ) (g : ↥(GK K)) :
    ∃ u : ℤ_[l], (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = (u : ℚ_[l]) ∧
      (PadicInt.toZModPow r u : ZMod (l ^ r)) =
        ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) := by
  obtain ⟨ζ, hζ1, hζ⟩ := GlobalTheory.LocDualInt.exists_root_pow_cyclotomicCharacter_congr K.1
    (IntermediateField.fixingSubgroupEquiv K.1 g) r
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc (g : GQ l) r ζ hζ1
  have key := hζ a hga
  have hr : (l : ℝ) ^ (-(r : ℤ)) ≤ 1 := by
    apply zpow_le_one_of_nonpos₀
    · exact_mod_cast (Fact.out : l.Prime).one_lt.le
    · simp
  have hnorm : ‖((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
    have e : ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) =
        (((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) + (a : ℚ_[l]) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha.trans hr) ?_)
    have := PadicInt.norm_le_one (a : ℤ_[l])
    rwa [PadicInt.norm_def, PadicInt.coe_natCast] at this
  let u : ℤ_[l] := ⟨_, hnorm⟩
  have hu : (u : ℚ_[l]) = ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) := rfl
  have ha' : ‖(u : ℚ_[l]) - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(r : ℤ)) := by rw [hu]; exact ha
  refine ⟨u, (P.PD_χ K g).trans hu.symm, ?_⟩
  rw [toZModPow_eq_of_norm_sub_le u a r ha', key]
  rfl

end GlobalTheory.CycLevel
