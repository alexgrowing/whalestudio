import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalUnitAlmostAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeLevelFamilyIff
open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_twisted_orbital_unit_almost_all : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (P : E[X]), P ∈ Ell E n →
  ∀ᶠ w in (cofinite : Filter (Pl E)), stTw n w (atPl w P) ((GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1) = 1 := by
  first | exact @GlobalTheory.BCT.UnitStable.stTw_unit | exact GlobalTheory.BCT.UnitStable.stTw_unit | (intros; apply GlobalTheory.BCT.UnitStable.stTw_unit <;> assumption)
