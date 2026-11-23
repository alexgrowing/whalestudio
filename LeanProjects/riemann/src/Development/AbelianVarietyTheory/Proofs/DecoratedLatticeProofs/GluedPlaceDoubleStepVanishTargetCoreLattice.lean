import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointFrameCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleUnfoldingStepAtGluedFinitePlaceStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.FinPl.vertexGlued_vanish_lastLat : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank), IsStdChar D ψ (-1) → UnrAt s₁ p.v → UnrAt s₂ p.v → ∀ (M₀ : Lat B.V₀) (M₁ : Lat J.W₀) (M : Lat B'.V₀) (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p J.W₀ n) (γ : Frame p B'.A n'') (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)) (P : Pair k n') (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsLattice k], IsSelfDualC B.V₀ M₀ → IsSelfDualC J.W₀ M₁ → IsSelfDualC B'.V₀ M → GluedCore B M₀ q α α₀ P → β.IsLat M₁ Q.lat → IsSumFrame B'.o B'.ζ γ γ₀ → (γ₀.IsLat M (lastKer Λ) ∨ γ₀.IsLat M (lastPair q Λ).lat) → ∀ Ξ₁ Ξ₂, Vac ψ B.V₀ J.W₀ M₀ M₁ (· = p.v) Ξ₁ → Vac ψ J.W₀ B'.V₀ M₁ M (· = p.v) Ξ₂ → ∀ φ, IsRam α φ → hand0 s₁ s₂ l vL (φ P) Ξ₁ Ξ₂ = 0 := by
  intro D k _ _ _ _ p n n' n'' _ _ _ _ _ _ q ψ σ B J B' s₁ s₂ l vL hψ hs₁ hs₂ M₀ M₁ M α α₀ β γ γ₀ P Q Λ _ hM₀ hM₁ hM hG hβ hγ hγ₀ Ξ₁ Ξ₂ hΞ₁ hΞ₂ φ hφ
  obtain ⟨χ, hχ, -, -, hcond⟩ := (GlobalTheory.T.exists_splitPoint_frame_character D).2 k p |>.2 ψ hψ
  have hc := hcond hG.unit
  obtain ⟨ε, -, hV⟩ := GlobalTheory.T.doubleUnfoldingStep_at_glued_finite_place D k p q ψ χ hc hχ
  have hO := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D
  have h₁ := (hO k p n (n' ⊕ Fin 1) ψ hψ B.V₀ J.W₀ α₀ β M₀ M₁ hM₀ hM₁ Ξ₁ hΞ₁).2.2 hG.unit _ _ hG.lat hβ
  have hO₂ := hO k p (n'' ⊕ Fin 1) n ψ hψ J.W₀ B'.V₀ β γ₀ M₁ M hM₁ hM Ξ₂ hΞ₂
  refine (hV n n' n'' σ B J B' s₁ s₂ l vL hs₁ hs₂ α α₀ β γ γ₀ hG.sum hγ P P Q).2 Λ M₀ M₁ M₁ M Ξ₁ Ξ₁ Ξ₂ Ξ₂ h₁ ?_ φ hφ
  rcases hγ₀ with h | h
  · exact Or.inl (hO₂.2.2 hG.unit _ _ hβ h)
  · exact Or.inr (hO₂.2.2 hG.unit _ _ hβ h)
