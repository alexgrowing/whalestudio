import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardKerSubspacesAndHeckePolyOfConvolution
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_ker_subspaces_and_heckePolyOf_convolution : (∀ (k U U' : Type) [Field k] [Fintype k] [AddCommGroup U] [Module k U] [FiniteDimensional k U] [AddCommGroup U'] [Module k U'] [FiniteDimensional k U'] (n t d : ℕ) (f : U →ₗ[k] U'), Module.finrank k U = n + t → Module.finrank k U' = n → Nat.card {W : Submodule k U // Module.finrank k W + d = n + t ∧ W ≤ LinearMap.ker f} = ∑ j ∈ Finset.range (d + 1), Fintype.card k ^ ((n - j) * (d - j)) * gaussBin (Fintype.card k) t (d - j) * Nat.card {W' : Submodule k U' // Module.finrank k W' = j ∧ LinearMap.range f ≤ W'}) ∧ ∀ (L : Type) [Field L] (q n t : ℕ) (a : ℕ → L) (ν s : L), (∀ j, n < j → a j = 0) → heckePolyOf (n + t) q (fun d => ∑ j ∈ Finset.range (d + 1), (q : L) ^ ((n - j) * (d - j)) * (gaussBin q t (d - j) : L) * ν ^ (d - j) * s ^ j * a j) = (heckePolyOf n q a).comp (C s * X) * blockPoly (ν * (q : L) ^ n) q t := by
  first | exact @GlobalTheory.KerRangeCount.card_ker_and_heckePolyOf_conv | exact GlobalTheory.KerRangeCount.card_ker_and_heckePolyOf_conv | (intros; apply GlobalTheory.KerRangeCount.card_ker_and_heckePolyOf_conv <;> assumption)
