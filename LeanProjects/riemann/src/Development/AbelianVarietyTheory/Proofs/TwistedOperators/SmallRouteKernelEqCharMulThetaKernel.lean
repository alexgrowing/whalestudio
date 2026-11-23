import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsGridFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSquareProductRouteBEqExternalProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumAdjointNegSourceKernelsAgree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsOfSmoothThetaStable

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareDict

theorem isThetaFunO_small_of_isMatched {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hM : IsMatched B t ρ i j Θ Θ') :
    ∀ d ∈ Θ'.support, IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) d.2 := by
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, ⟨φ₁, φ₂, hloc, -⟩, -⟩, -, rfl⟩ := hM
  intro d hd
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hd)
  obtain ⟨d₀, hd₀, hd₁⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hP)
  obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hd₁)
  obtain ⟨hA, hB⟩ := hloc d₀ hd₀
  have hv₁ := (ρ.vT_is t i j i.2.le j.2).2.theta
  have hv₂ := (ρ.vX_is i j i.2 j.2.le).2.theta
  have hf₁ := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hA.2 hv₁
  have hf₂ := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hB.2 hv₂
  exact ⟨GlobalTheory.FockTheta.ptStable D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ _ _ _ P.1.2 hf₁,
    GlobalTheory.FockTheta.ptStable D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ _ _ _ P.2 hf₂⟩

theorem kerSmall_eq_thetaKO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (ωB : GlobalTheory.Grid.WRep (G.V (.grid ↑i ↑j)) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))),
    GlobalTheory.Grid.IsWeil W.ψ false _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ωB →
    ∀ (B : Frames G) (ρ : RealMatch W) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ g g₁ u, kerSmall W Θ' g g₁ u = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ *
      thetaKO ωB u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) (GlobalTheory.SquareDict.datumB W Θ') := by
  intro D T L sc G μ₀ hL W t i j ωB hωB B ρ Θ Θ' hM g g₁ u
  have hth := isThetaFunO_small_of_isMatched W B ρ t i j Θ Θ' hM
  have hω := (GlobalTheory.Grid.isWeil_false W.ψ _ _ _ _ ωB).mp hωB
  have key : ∀ d ∈ Θ'.support, W.kerA (.down t i j) d.1.2 g u * W.kerA (.right i j) d.2 u g₁ =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ *
        ωB (u, GlobalTheory.SquareComm.blk _ _ (g, g₁))
          (box2 (S := G.V (.grid i j)) (A := G.V (.grid i (j + 1))) (B := G.V (.grid (i + 1) j)) d.1.2
            (fun y => d.2 (adjM (G.V (.grid i j)) (negSp (G.V (.grid (i + 1) j))) y))) 0 := by
    intro d hd
    have h := (GlobalTheory.SeesawSmall.seesaw_small hL W t i.2 j.2 ωB hω d.1.2 d.2 (hth d hd).1 (hth d hd).2).2 g u g₁
    have hadj : GlobalTheory.SeesawSmall.adjFn (G.V (.grid i j)) (G.V (.grid (i + 1) j)) d.2 =
        fun y => d.2 (adjM (G.V (.grid i j)) (negSp (G.V (.grid (i + 1) j))) y) := by
      funext y
      exact congrArg d.2 (GlobalTheory.AdjSwap.dagger_eq_adjM (G.V (.grid i j)) (negSp (G.V (.grid (i + 1) j))) y)
    rw [hadj] at h
    exact h
  simp only [kerSmall, GlobalTheory.SquareDict.datumB, thetaKO, Finsupp.sum, map_sum, Finset.sum_apply, map_smul,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [key d hd]
  ring

end GlobalTheory.SquareDict
