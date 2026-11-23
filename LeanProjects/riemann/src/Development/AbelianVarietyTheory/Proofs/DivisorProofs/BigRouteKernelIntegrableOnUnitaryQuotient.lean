import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RouteBigVertexKernelProductEqConstMulThetaKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareThetaTripleExistsSignatureRankAddLtStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.FunObj

theorem routeBig_kerBig_integrableOn : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (hWC : GlobalTheory.SquareSt.WeilConvergence) {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hT : SquareTriple W t i j)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ g : GA D (G.V (.grid i (j + 1))), IntegrableOn (kerBig W Θ g g₁) (M.fd (.grid (i + 1) (j + 1))) (M.ν (.grid (i + 1) (j + 1))) := by
  intro D T L sc G hWC μ₀ hL W B ρ t i j hT M hM Θ Θ' hΘ g₁ g
  have hHF : GlobalTheory.SquareComm.IsHaarFD _ (M.ν (.grid (i + 1) (j + 1))) (M.fd (.grid (i + 1) (j + 1))) :=
    (hM.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).haar_fund
  obtain ⟨p, hsig, hrk⟩ := GlobalTheory.T.squareThetaTriple_exists_signature_rank_add_lt W t i j hT M hM
  have key : ∀ d ∈ Θ.support, Integrable (fun u => Θ d * (W.kerA (.right i (j + 1)) d.1.2 g u *
      W.kerA (.down t (i + 1) j) d.2 u g₁)) ((M.ν (.grid (i + 1) (j + 1))).restrict (M.fd (.grid (i + 1) (j + 1)))) := by
    intro d hd
    obtain ⟨ε, X, χ, χ', ω, hω, hX, Φ, hΦ, h, c, he⟩ := GlobalTheory.T.routeBigVertex_kernelProduct_eq_const_mul_thetaKernel hL W B ρ t i j hT M hM Θ Θ' hΘ d hd g g₁
    obtain ⟨N, C, hmi⟩ := hWC D W.ψ W.θ W.θ_is ε _ X χ χ' ω hω p hsig (hX ▸ hrk) _ _ hHF Φ hΦ
    refine Integrable.const_mul ?_ _
    simp_rw [he]
    exact ((hmi h).1).const_mul c
  have e : kerBig W Θ g g₁ = fun u => ∑ d ∈ Θ.support, Θ d * (W.kerA (.right i (j + 1)) d.1.2 g u *
      W.kerA (.down t (i + 1) j) d.2 u g₁) := by
    funext u; rfl
  rw [IntegrableOn, e]
  exact integrable_finsetSum _ key

end GlobalTheory.FunObj

end
