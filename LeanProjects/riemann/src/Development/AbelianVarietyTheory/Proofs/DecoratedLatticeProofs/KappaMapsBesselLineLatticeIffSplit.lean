import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLineConditionsDualStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLineHomLatticeCompletionIffScalarStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KappaMemLineLatticeCompletionIffScalarStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KappaLat

theorem star_self_pair : ∀ (D : D7) (L : HSp D) (ζ : Fin L.rank → D.host.E), star (star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ) = star ζ ⬝ᵥ HSpace.gram L *ᵥ ζ := by
  intro D L ζ
  have hG := GlobalTheory.MixModel.gram_conjTranspose L
  rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hG, Matrix.dotProduct_mulVec]

theorem kappa_line_lat_iff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (n' n'' : Type) [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (α : ∀ i, Frame (p i) B.A n') (α₀ : ∀ i, Frame (p i) B.V₀ (n' ⊕ Fin 1)) (γ : ∀ i, Frame (p i) B'.A n'') (γ₀ : ∀ i, Frame (p i) B'.V₀ (n'' ⊕ Fin 1)) (M : Lat B.V₀) (LS : Lat S) (M' : Lat B'.V₀) (Λ : ι → Submodule 𝒪[k] (n' → k)) (Λ' : ι → Submodule 𝒪[k] (n'' → k)), IsSelfDualC B.V₀ M → IsSelfDualC S LS → IsSelfDualC B'.V₀ M' → (∀ i, IsSumFrame B.o B.ζ (α i) (α₀ i) ∧ IsSumFrame B'.o B'.ζ (γ i) (γ₀ i) ∧ (α₀ i).IsLat M (lastKer (Λ i)) ∧ (γ₀ i).IsLat M' (lastKer (Λ' i))) → ∀ x : WO S B'.L, MxAt P x → ((B'.o.resT S).symm (0, x) ∈ latO S B'.V₀ (LS : Set _) (M' : Set _) P ↔ (B.o.resS S).symm (0, l.κ S x) ∈ latO B.V₀ S (M : Set _) (LS : Set _) P) := by
  intro D k _ _ _ _ ι p I P hP n' n'' _ _ _ _ ρ σ B B' l S α α₀ γ γ₀ M LS M' Λ Λ' hM hLS hM' hfr x hx
  rw [GlobalTheory.T.mem_lineHomLatticeCompletion_iff_scalar D k ι p I P hP n'' σ B' γ γ₀ M' Λ' hM' (fun i => ⟨(hfr i).2.1, (hfr i).2.2.2⟩) S LS hLS x hx,
    GlobalTheory.T.kappa_mem_lineLatticeCompletion_iff_scalar D k ι p I P hP n' ρ σ B B' l S α α₀ M LS Λ hM hLS (fun i => ⟨(hfr i).1, (hfr i).2.2.1⟩) x hx]
  have h1 : (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) ≠ 0 := B.line.2
  have h2 : (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ) ≠ 0 := B'.line.2
  have h3 := star_self_pair D B'.L B'.ζ
  have h4 : (star B.ζ ⬝ᵥ HSpace.gram B.L *ᵥ B.ζ) = D.host.xi0 * star D.host.xi0 * (star B'.ζ ⬝ᵥ HSpace.gram B'.L *ᵥ B'.ζ) := l.norm
  exact forall₂_congr fun y _ => exists_congr fun d => and_congr_right fun hd => and_congr_right fun _ =>
    GlobalTheory.T.splitPlace_lineConditions_dual D k ι p I P hP _ _ h1 h2 h3 h4 d hd

end GlobalTheory.KappaLat
