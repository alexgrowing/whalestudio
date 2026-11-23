import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionUniformizerPower
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulVecMemGenLatSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.SUCong

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_completion_uniformizer_power : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (π : 𝓞 F), π ∈ v.asIdeal → π ∉ v.asIdeal ^ 2 → ∀ (k : ℕ) (y : Fin n → Fv F v ⊗[F] E), y ∈ GlobalTheory.TamCnt.compK Λ v k ↔ ∃ z ∈ GlobalTheory.TamCnt.compLat v (Λ : Set (Fin n → E)), y = ((1 : Fv F v) ⊗ₜ[F] algebraMap F E (π : F)) ^ k • z := by
  first | exact @GlobalTheory.TamCnt.mem_compK_iff | exact GlobalTheory.TamCnt.mem_compK_iff | (intros; apply GlobalTheory.TamCnt.mem_compK_iff <;> assumption)
