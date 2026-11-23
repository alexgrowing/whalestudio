import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TeichmullerDecompositionDirichletTwistedPower
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChSumSubCMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubOnePowThreeLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_decomposition_dirichlet_twisted_power : ∀ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (e R j : ℕ), l ≠ 2 → ∃ (ε : Qbar l) (t : ℕ), (ε = 0 ∨ ε ^ (l - 1) = 1) ∧ Cg R (φ (j : ZMod l) * (j : Qbar l) ^ e) (ε * ((1 + (l : Qbar l)) ^ e) ^ t) ∧ ∀ m, 1 ≤ m → m ≤ R → ∀ ψ : DirichletCharacter (Qbar l) (l ^ m), InComp φ e ψ → ψ⁻¹ (j : ZMod (l ^ m)) = ε * (ψ⁻¹ (1 + (l : ZMod (l ^ m)))) ^ t := by
  first | exact @GlobalTheory.TeichDec.teich | exact GlobalTheory.TeichDec.teich | (intros; apply GlobalTheory.TeichDec.teich; all_goals assumption)
