import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLineHomLatticeCompletionIffScalar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_lineHomLatticeCompletion_iff_scalar : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n'' : Type) [Fintype n''] [DecidableEq n''] (σ : ℕ) (B' : BesLev D σ) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M' : Lat B'.V₀) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ (S : HSp D) (LS : Lat S), IsSelfDualC S LS → ∀ x : WO S B'.L, MxAt P x → ((B'.o.resT S).symm (0, x) ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P ↔ ∀ y ∈ latV S LS P, ∃ d : AE D, d ∈ idAt D P ∧ (x : Matrix _ _ (AE D)) *ᵥ y = d • ratV B'.ζ ∧ (∀ i, (p i).pr d ∈ 𝒪[k] ∧ (p i).pr (cA D d) * (p i).pr (incA D (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ)) ∈ 𝒪[k])) := by
  first | exact @GlobalTheory.Corev.mem_latO_line_iff | exact GlobalTheory.Corev.mem_latO_line_iff | (intros; apply GlobalTheory.Corev.mem_latO_line_iff <;> assumption)
