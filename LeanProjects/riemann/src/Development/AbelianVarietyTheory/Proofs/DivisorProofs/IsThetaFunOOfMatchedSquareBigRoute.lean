import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExternalProductOnHermitianSumSmulLeft
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStable

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RouteSeesaw

theorem isThetaFunO_of_isMatched : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ d ∈ Θ.support, IsThetaFunO W.ψ (G.pS (.chi i (j + 1))) (G.pT (.chi i (j + 1))) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t (i + 1) j)) (G.pT (.mu t (i + 1) j)) d.2 := by
  intro D T L sc G μ₀ _hL W B ρ t i j Θ Θ' hM d hd
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, hF, rfl, -⟩ := hM
  obtain ⟨e, -, -, φ₁, φ₂, hφ, -⟩ := hF
  unfold tensT at hd
  obtain ⟨P, -, hd⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  obtain ⟨d', hd', hd⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  have hd := Finsupp.support_single_subset hd
  rw [Finset.mem_singleton] at hd
  subst hd
  obtain ⟨h₁, h₂⟩ := hφ d' hd'
  have v₁ := (ρ.vX_is i (j + 1) i.2 j.2).2.2
  have v₂ := (ρ.vT_is t (i + 1) j i.2 j.2).2.2
  exact ⟨GlobalTheory.FockTheta.ptStable D _ _ W.ψ_std W.θ_is _ _ _ _ _ _ _ _
      (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h₁.2 v₁),
    GlobalTheory.FockTheta.ptStable D _ _ W.ψ_std W.θ_is _ _ _ _ _ _ _ _
      (GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is h₂.2 v₂)⟩

end GlobalTheory.RouteSeesaw
