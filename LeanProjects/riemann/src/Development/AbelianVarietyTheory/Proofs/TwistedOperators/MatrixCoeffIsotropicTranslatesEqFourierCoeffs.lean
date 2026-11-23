import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicDualMiddlePartsSymplecticOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedHeisenbergTermsPermutedRationalUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaThetaFunctionsOrientedPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistCoefUnfold

theorem pcoef : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ κ : ℝ, (∀ H : WO V W → ℂ, Continuous H → (∃ b : ℝ, ∀ w, ‖H w‖ ≤ b) → (∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w) → ∫ w in 𝓕V, H w ∂μV = κ • ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕', H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ) → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ (y : Mx D W.rank r) (a : Matrix (Fin W.rank) (Fin r) D.host.E), (∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV) = ∫ t in 𝓨, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * (κ • (∫ y' in 𝓨, ∫ x in 𝓕', (heisO ψ V W (isoPart V W C y) F) (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ)) ∂μ := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ μV 𝓕V hμV h𝓕V μ' 𝓕' hμ' h𝓕' κ hκ F G hF hG y a
  have hth := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W
  have horth := GlobalTheory.TwistFormsOrth.orthogonal D V V' W r C B hs C' h1 h2 h3
  have hPt : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C y) F) := hth.1 _ F hF
  have hγrat : isoPart V W C (a.map (incA D)) ∈ ratL W V := by
    rw [← GlobalTheory.TwistEquiRat.ratW_eq_isoPart]; exact ⟨_, rfl⟩
  have hfirst : heisO ψ V W (isoPart V W C (y + a.map (incA D))) F =
      heisO ψ V W (isoPart V W C (a.map (incA D))) (heisO ψ V W (isoPart V W C y) F) := by
    rw [hth.2.1, GlobalTheory.TwistEquiRat.symplOH_isoPart V W C hs.frame, AddChar.map_zero_eq_one, one_smul,
      GlobalTheory.TwistEquiRat.isoPart_add, add_comm]
  have hpt : ∀ w, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) =
      ψ (symplO V W w (isoPart V W C (a.map (incA D)))) * (heisO ψ V W (isoPart V W C y) F w * star (G w)) := by
    intro w
    rw [hfirst, GlobalTheory.ThetaSchur.heisO_rat hPt hγrat]
    ring
  have hsym : ∀ t y' x, symplO V W (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)
      (isoPart V W C (a.map (incA D))) = symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D))) := by
    intro t y' x
    rw [GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_left, horth.1 y' _,
      GlobalTheory.PlaceModel.symplO_skew V W (isoPart V W C (a.map (incA D))) (midPart V V' W B x), horth.2.1 _ x]
    simp
  have hHt : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C (y + a.map (incA D))) F) := hth.1 _ F hF
  have hHc : Continuous fun w => heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) :=
    hHt.cont.mul hG.cont.star
  have hHb : ∃ b : ℝ, ∀ w, ‖heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w)‖ ≤ b := by
    obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
    obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn hHc.continuousOn
    refine ⟨b, fun w => ?_⟩
    obtain ⟨g, hg, h⟩ := hKc w
    rw [← GlobalTheory.ThetaSchur.prod_periodic hψ hHt hG hg w]
    exact hb _ h
  have key := hκ _ hHc hHb (fun g hg w => GlobalTheory.ThetaSchur.prod_periodic hψ hHt hG hg w)
  rw [key]
  simp_rw [hpt, hsym, integral_const_mul]
  rw [← integral_smul]
  congr 1
  funext t
  rw [mul_smul_comm]

end GlobalTheory.TwistCoefUnfold
