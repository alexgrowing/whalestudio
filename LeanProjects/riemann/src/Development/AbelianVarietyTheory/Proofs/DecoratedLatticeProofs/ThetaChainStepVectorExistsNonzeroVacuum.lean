import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MapFinNeg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepVecExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.StepVecOK

theorem stepVec_exists_vac : ∀ (D : D7) (c : Com D), c.Is → ∀ (k : Fin D.R.m) (s s' : PiLocalization₂ D), s.Is c k → s'.Is c (k + 1) → (∃ ξ f₀ f, IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ∅ ξ f₀ f) ∧ ∀ ξ f₀ f, IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ∅ ξ f₀ f → IsThetaFunO c.ψ s.V s'.V f ∧ f ≠ 0 ∧ (∀ τ, IsFockVacAt (heisO c.ψ s.V s'.V) c.θ τ (cplxO (cart s.M τ) (cart s'.M τ)) f) ∧ ∀ φ, IsThetaFunO c.ψ s.V s'.V (pureTensorO c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (onb s.M) (onb s'.M) f φ) := by
  classical
  intro D c hc k s s' hs hs'
  have hr : s.V.rank ≤ s'.V.rank := by
    rw [hs.rank, hs'.rank]
    show D.R.r + (k : ℕ) * D.R.t ≤ D.R.r + ((k : ℕ) + 1) * D.R.t
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  refine ⟨?_, fun ξ f₀ f h => ?_⟩
  · obtain ⟨f₀, hf₀⟩ := GlobalTheory.VacuumO.vacExists D c.ψ c.θ hc.std hc.inf s.V s'.V (cart s.M) (cart s'.M) hs.sigOK hs'.sigOK
      (GlobalTheory.Chain.VacVec.cart_isCartanInv s.M) (GlobalTheory.Chain.VacVec.cart_isCartanInv s'.M) s.Λ s'.Λ hs.selfDual hs'.selfDual
    obtain ⟨_, ξL, hL⟩ := hs.lev
    have hsp : ∃ e : AE D, IsIdemSum e (s.L.Pg ∪ ∅) := by
      obtain ⟨e, he⟩ := hc.split
      refine ⟨e, ?_⟩
      rw [Finset.union_empty, hL]
      exact he
    obtain ⟨f, hf⟩ := GlobalTheory.PlaceDatum.stepVecExists D c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L
      (c.chi ((k : ℕ) + 1)) ∅ 1 hs.selfDual hs'.selfDual hs.frame hs'.frame (Finset.disjoint_empty_right _) hsp f₀ hf₀
    exact ⟨1, f₀, f, hf⟩
  · obtain ⟨h1, h2, h3⟩ := GlobalTheory.Chain.StepVac.stepVec_vac hs.selfDual hs'.selfDual hr h
    exact ⟨h1, h2, h3, fun φ => GlobalTheory.FockTheta.ptStable D c.ψ c.θ hc.std hc.inf s.V s'.V _ _ _ _ f φ h1⟩

end GlobalTheory.ChainOnto.StepVecOK
