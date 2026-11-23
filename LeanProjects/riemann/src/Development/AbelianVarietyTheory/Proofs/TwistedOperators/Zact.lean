import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsGridFr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridRouteKernelEqDetCharactersMulThetaKerneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRouteKernelEqCharMulThetaKernelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFramesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRouteDatumMemAlgebraicVectorsGridFramesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSeesawHermitianTripleGridSquareOfStandingStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareDict

theorem dict : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (A : Fr (G.V (.grid (↑i + 1) (↑j + 1)))) (A₁ : Fr (G.V (.grid ↑i ↑j))) (AV : Fr (G.V (.grid ↑i (↑j + 1)))) (AV₁ : Fr (G.V (.grid (↑i + 1) ↑j))),
    GlobalTheory.SquareDict.IsGridFr W _ A → GlobalTheory.SquareDict.IsGridFr W _ A₁ → GlobalTheory.SquareDict.IsGridFr W _ AV →
    GlobalTheory.SquareDict.IsGridFr W _ AV₁ →
    (SquareStanding G t → ∀ M : Vol G, M.Is t →
      GlobalTheory.SquareComm.IsTriple (G.V (.grid (↑i + 1) (↑j + 1))) (G.V (.grid ↑i ↑j)) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j))) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j)) ∧
    ∀ (ωA : GlobalTheory.Grid.WRep (G.V (.grid (↑i + 1) (↑j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))) (ωB : GlobalTheory.Grid.WRep (G.V (.grid ↑i ↑j)) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))),
    GlobalTheory.Grid.IsWeil W.ψ true _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) ωA →
    GlobalTheory.Grid.IsWeil W.ψ false _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ωB →
    ∃ κ : GA D (G.V (.grid ↑i (↑j + 1))) × GA D (G.V (.grid (↑i + 1) ↑j)) → ℂ,
    ∀ (B : Frames G) (ρ : RealMatch W) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
      GlobalTheory.SquareDict.datumA W Θ ∈ GlobalTheory.SquareComm.algF W.ψ W.θ true A (GlobalTheory.SquareComm.frSum AV AV₁) ∧
      GlobalTheory.SquareDict.datumB W Θ' ∈ GlobalTheory.SquareComm.algF W.ψ W.θ false A₁ (GlobalTheory.SquareComm.frSum AV AV₁) ∧
      (∀ g g₁ u, kerBig W Θ g g₁ u = κ (g, g₁) * thetaKO ωA u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) (GlobalTheory.SquareDict.datumA W Θ)) ∧
      (∀ (z : GA D (G.V (.grid ↑i ↑j)) →₀ ℂ) g g₁ u, translates z (kerSmall W Θ' g g₁) u =
        κ (g, g₁) * thetaKO ωB u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) (GlobalTheory.SquareDict.zact ωB z (GlobalTheory.SquareDict.datumB W Θ'))) ∧
      (∀ (M : Vol G) g g₁, ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ =
        κ (g, g₁) * GlobalTheory.SquareComm.thetaInt ωA (M.ν _) (M.fd _) (GlobalTheory.SquareDict.datumA W Θ) (GlobalTheory.SquareComm.blk _ _ (g, g₁))) ∧
      ∀ (M : Vol G) (z : GA D (G.V (.grid ↑i ↑j)) →₀ ℂ) g g₁, ∫ u in M.fd _, translates z (kerSmall W Θ' g g₁) u ∂M.ν _ =
        κ (g, g₁) * GlobalTheory.SquareComm.thetaInt ωB (M.ν _) (M.fd _) (GlobalTheory.SquareDict.zact ωB z (GlobalTheory.SquareDict.datumB W Θ'))
          (GlobalTheory.SquareComm.blk _ _ (g, g₁)) :=
  by
  intro D T L sc G μ₀ hL W t i j A A₁ AV AV₁ hA hA₁ hV hV₁
  refine ⟨GlobalTheory.T.isSeesawHermitianTriple_gridSquare_of_standing hL W t i j, fun ωA ωB hωA hωB => ⟨fun x => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j x.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j x.2,
    fun B ρ Θ Θ' hΘ => ?_⟩⟩
  have kA := GlobalTheory.T.thetaGridRouteKernel_eq_detCharacters_mul_thetaKernel hL W t i j ωA hωA B ρ Θ Θ' hΘ
  have kB := GlobalTheory.T.smallRoute_kernel_eq_char_mul_thetaKernel hL W t i j ωB hωB B ρ Θ Θ' hΘ
  have tr : ∀ (z : GA D (G.V (.grid ↑i ↑j)) →₀ ℂ) g g₁ u, translates z (kerSmall W Θ' g g₁) u =
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁) * thetaKO ωB u (GlobalTheory.SquareComm.blk _ _ (g, g₁))
        (GlobalTheory.SquareDict.zact ωB z (GlobalTheory.SquareDict.datumB W Θ')) := by
    intro z g g₁ u
    simp only [translates, kB, GlobalTheory.SquareDict.zact, thetaKO, Finsupp.sum, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : ωB (u * k, GlobalTheory.SquareComm.blk _ _ (g, g₁)) = ωB (u, GlobalTheory.SquareComm.blk _ _ (g, g₁)) * ωB (k, 1) := by
      rw [← map_mul]; simp
    rw [e, Module.End.mul_apply]; ring
  refine ⟨GlobalTheory.T.routeDatum_mem_algebraicVectors_grid_frames hL W t i j A AV AV₁ hA hV hV₁ B ρ Θ Θ' hΘ, GlobalTheory.T.smallRouteDatum_mem_algebraicVectors_grid_frames hL W t i j A₁ AV AV₁ hA₁ hV hV₁ B ρ Θ Θ' hΘ, kA, tr, ?_, ?_⟩
  · intro M g g₁
    simp only [kA, GlobalTheory.SquareComm.thetaInt]
    exact integral_const_mul _ _
  · intro M z g g₁
    simp only [tr, GlobalTheory.SquareComm.thetaInt]
    exact integral_const_mul _ _

end GlobalTheory.SquareDict

end
