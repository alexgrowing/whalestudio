import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UniformizerPowerTorusMemNormalUnitarySubgroup
import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeB
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
open Formalism.UG Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizerPowerTorus_mem_normal_unitarySubgroup : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ N : Subgroup (Formalism.UG.GU σ n), N.Normal → Formalism.UG.KU σ n ≤ N → (∀ u : Formalism.UG.GU σ n, Formalism.UG.IsUnipU u → u ∈ N) → ∀ (c : Fin n → ℤ), (∀ i : Fin n, c i.rev = -c i) → ∀ t : Formalism.UG.GU σ n, ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => ϖ ^ c i) → t ∈ N := by
  first | exact @GlobalTheory.torus_mem_normal | exact GlobalTheory.torus_mem_normal | (intros; apply GlobalTheory.torus_mem_normal <;> assumption)
