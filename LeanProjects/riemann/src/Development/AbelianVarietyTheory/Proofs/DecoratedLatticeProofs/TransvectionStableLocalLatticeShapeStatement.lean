import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionStableLocalLatticeShape
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transvectionStable_localLattice_shape : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (L : Submodule 𝒪[k] (n → k)) (c : k), 3 ≤ Fintype.card n → c ≠ 0 → (∀ x ∈ L, ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → x + Pi.single b ((t : k) * x d) ∈ L) → (∀ x ∈ L, ∀ j, c⁻¹ * x j ∈ 𝒪[k]) → (∃ x ∈ L, ∃ j, x j = c) → (∀ x : n → k, x ∈ L ↔ ∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∨ (∀ x : n → k, x ∈ L ↔ (∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧ ∃ s : 𝒪[k], s ∈ IsLocalRing.maximalIdeal 𝒪[k] ∧ (s : k) = c⁻¹ * x i) := by
  first | exact @GlobalTheory.LatPairStab.stable_lattice_shape | exact GlobalTheory.LatPairStab.stable_lattice_shape | (intros; apply GlobalTheory.LatPairStab.stable_lattice_shape <;> assumption)
