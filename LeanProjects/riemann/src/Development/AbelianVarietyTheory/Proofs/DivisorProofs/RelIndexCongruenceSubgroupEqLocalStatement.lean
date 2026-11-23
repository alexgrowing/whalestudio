import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexCongruenceSubgroupEqLocal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemGenLatSmul
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_congruence_subgroup_eq_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E)) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ), (GlobalTheory.TamCnt.congG σ J Λ v (k + 1)).relIndex (GlobalTheory.TamCnt.congG σ J Λ v k) = (GlobalTheory.TamCnt.locCong σ J Λ v (k + 1)).relIndex (GlobalTheory.TamCnt.locCong σ J Λ v k) := by
  first | exact @GlobalTheory.TamCnt.relIndex_congG_succ | exact GlobalTheory.TamCnt.relIndex_congG_succ | (intros; apply GlobalTheory.TamCnt.relIndex_congG_succ <;> assumption)
