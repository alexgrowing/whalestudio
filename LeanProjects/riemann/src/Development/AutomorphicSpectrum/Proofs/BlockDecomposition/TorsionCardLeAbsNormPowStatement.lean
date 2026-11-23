import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPow
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_card_le_absNorm_pow : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ 𝔞 : Ideal (𝓞 K), 𝔞 ≠ ⊥ → Finite {x : (Fin m → K) ⧸ L // ∀ a ∈ 𝔞, a • x = 0} ∧ Nat.card {x : (Fin m → K) ⧸ L // ∀ a ∈ 𝔞, a • x = 0} ≤ Ideal.absNorm 𝔞 ^ m := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.TorCard.tor_card | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.TorCard.tor_card | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.TorCard.tor_card <;> assumption)
