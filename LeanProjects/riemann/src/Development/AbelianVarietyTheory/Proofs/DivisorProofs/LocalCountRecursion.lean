import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemGenLatSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexCongruenceSubgroupEqLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexLocalCongruenceEqAbsNormPowStatement
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published

theorem GlobalTheory.TamCnt.locCount_succ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 2 ≤ r → Unr E → SelfDualLat G Λ → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (k : ℕ), 1 ≤ k → locCount (IsCMField.complexConj E).toAlgHom Gᵀ Λ v (k + 1) = locCount (IsCMField.complexConj E).toAlgHom Gᵀ Λ v k * Ideal.absNorm v.asIdeal ^ (r ^ 2 - 1) := by
  intro E _ _ _ r G Λ hr hU hS v k hk
  have h := Subgroup.relIndex_mul_relIndex _ _ _
    (GlobalTheory.TamCnt.congG_anti (IsCMField.complexConj E).toAlgHom Gᵀ Λ v k)
    (GlobalTheory.TamCnt.congG_le_stabG (IsCMField.complexConj E).toAlgHom Gᵀ Λ v k)
  rw [GlobalTheory.TamCnt.locCount_eq_relIndex, GlobalTheory.TamCnt.locCount_eq_relIndex, ← h,
    GlobalTheory.T.relIndex_congruence_subgroup_eq_local _ _ _ _ _ _ v k, GlobalTheory.T.relIndex_local_congruence_eq_absNorm_pow E r G Λ hr hU hS v k hk, mul_comm]
