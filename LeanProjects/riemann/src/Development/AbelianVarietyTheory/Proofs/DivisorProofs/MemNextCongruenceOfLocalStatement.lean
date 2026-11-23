import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNextCongruenceOfLocal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemGenLatSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocHomVal
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_next_congruence_of_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (Λ : Submodule (𝓞 E) (Fin M → E)) (v : HeightOneSpectrum (𝓞 F)) (k : ℕ), ∀ (h : GlobalTheory.Published.SUAdelic σ J), h ∈ GlobalTheory.TamCnt.congG σ J Λ v k → GlobalTheory.TamCnt.locHom σ J v h ∈ GlobalTheory.TamCnt.locCong σ J Λ v (k + 1) → h ∈ GlobalTheory.TamCnt.congG σ J Λ v (k + 1) := by
  first | exact @GlobalTheory.TamCnt.LevelUp.mem_congG_succ | exact GlobalTheory.TamCnt.LevelUp.mem_congG_succ | (intros; apply GlobalTheory.TamCnt.LevelUp.mem_congG_succ <;> assumption)
