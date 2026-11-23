import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenLevel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGrowthUniform
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.CuspGrowth

open GlobalTheory.IdeleCovolume GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele in

theorem abs_le_of_conj_mem_compact : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ Q : Set (GA E a), IsCompact Q → ∃ n₀ : ℕ, ∀ (γ : GL (Fin a) E) (n : ℤ) (x : GA E a),
      x⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * x ∈ Q → |n| ≤ n₀ := by
  intro E _ _ _ a ha Q hQ
  have hf : Continuous fun g : GA E a => Real.log (ideleNorm (E := E) (GeneralLinearGroup.det g)) :=
    (continuous_ideleNorm.comp GeneralLinearGroup.continuous_det).log fun _ => ideleNorm_ne_zero _
  obtain ⟨B, hB⟩ := (hQ.image hf).isBounded.exists_norm_le
  have hL : 0 < Real.log (ideleNorm (E := E) (eIdele E)) := Real.log_pos (one_lt_ideleNorm_eIdele E)
  set L := Real.log (ideleNorm (E := E) (eIdele E)) with hLdef
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  refine ⟨⌈B / (a * L)⌉₊, fun γ n x hx => ?_⟩
  have hd : GeneralLinearGroup.det (ratGL E a γ) = diag E (GeneralLinearGroup.det γ) :=
    Units.ext (by rw [ratGL, GlobalTheory.CuspRep.det_map]; rfl)
  have hv : Real.log (ideleNorm (E := E) (GeneralLinearGroup.det
      (x⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * x))) = (n : ℝ) * (a * L) := by
    have h1 : GeneralLinearGroup.det (x⁻¹ * (ratGL E a γ * splitCentre E a 1 ^ n) * x) =
        diag E (GeneralLinearGroup.det γ) * (eIdele E ^ a) ^ n := by
      rw [map_mul, map_mul, map_mul, map_inv, map_zpow, hd, det_splitCentre_one, mul_comm, ← mul_assoc,
        mul_inv_cancel, one_mul]
    rw [h1, map_mul, show ideleNorm (E := E) (diag E _) = 1 from ideleNorm_principalIdele _, one_mul,
      map_zpow, map_pow, Real.log_zpow, Real.log_pow]
  have hb := hB _ ⟨_, hx, rfl⟩
  beta_reduce at hb
  rw [hv, Real.norm_eq_abs, abs_mul, abs_of_pos (mul_pos ha' hL)] at hb
  have h2 : ((|n| : ℤ) : ℝ) ≤ B / (a * L) := by
    rw [le_div_iff₀ (mul_pos ha' hL)]
    simpa using hb
  have h3 : ((|n| : ℤ) : ℝ) ≤ ((⌈B / (a * L)⌉₊ : ℤ) : ℝ) := by
    rw [Int.cast_natCast]
    exact h2.trans (Nat.le_ceil _)
  exact Int.cast_le.1 h3

end GlobalTheory.CompanionTheory.CuspGrowth
