import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsThetaSumSiegelSetLeTorusPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianWittFrameColumnsLeWittIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralSiegelTorusConeModulusLtTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsThetaIntLeSetLIntegralOfCoverStatement

noncomputable section

open scoped Matrix NNReal ENNReal TensorProduct Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilThetaConv

theorem weilThetaConvergence_of_siegelSet (hRT : GlobalTheory.Published.SiegelSetUnitary) : GlobalTheory.Published.WeilThetaConvergence := by
  intro D n V _hn hwitt θ hθ ν hν Φ
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨r, Xf, Yf, hW⟩ := GlobalTheory.SiegelSet.exists_isWittFrame (GlobalTheory.AdelicU.isCMExt_host D) (GlobalTheory.Doubling.isHermND_gram V)
  have hr : r ≤ Formalism.MainNotions.SchurIrreducible.wittIdx V := GlobalTheory.T.hermitianWittFrame_columns_le_wittIndex D V r Xf Yf hW
  have hr' : r = 0 ∨ n + r < V.rank := by rcases hwitt with h | h <;> omega
  obtain ⟨K, Ω, c, hK, hΩ, -, hc, -, hcl, hcov, ⟨C₀, hC₀, hconj⟩, hmeas, -, -⟩ :=
    hRT D.host.F D.host.E D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D) V.rank V.gram (GlobalTheory.Doubling.isHermND_gram V) r Xf Yf hW
  obtain ⟨-, C₁, hC₁⟩ := hmeas ν hν
  have hΦc : Continuous Φ.1 := (GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ V.rank n Φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ V.rank n Φ.1 Φ.2)).1
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.absThetaSum_siegelSet_le_torusPower D θ hθ V n r Xf Yf hW c hc (C₀ * (K : Set (GA D V))) (hC₀.mul hK) Φ
  have hI := GlobalTheory.T.lintegral_siegelTorusCone_modulus_lt_top D.host.F V.rank r n c hc hr'
  calc GlobalTheory.SiegelFormula.absThetaInt V ν Φ.1
      ≤ ∫⁻ g in GlobalTheory.SiegelSet.siegelSet D.sp.cm.sig V.gram Xf Yf Ω c K, GlobalTheory.SiegelFormula.absTheta V Φ.1 g ∂ν :=
        GlobalTheory.T.absThetaInt_le_setLIntegral_of_cover' D V n ν hν Φ.1 hΦc _ hcl.measurableSet hcov
    _ ≤ C₁ * ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
          ENNReal.ofReal (C * ∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
          ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹) := by
        refine hC₁ (fun g => GlobalTheory.SiegelFormula.absTheta V Φ.1 g) _ (by fun_prop) fun p hp t ht a ha k hk => ?_
        have e : p * a * k = a * (a⁻¹ * p * a * k) := by group
        rw [e]
        exact hC t ht a ha _ (Set.mul_mem_mul (hconj p hp t ht a ha) hk)
    _ = C₁ * (ENNReal.ofReal C * ∫⁻ t in GlobalTheory.SiegelSet.cone r c,
          ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ D.host.F * (2 * n))) *
          ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus D.host.F V.rank t * ∏ i, t i)⁻¹)) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_congr fun t => by rw [ENNReal.ofReal_mul hC0, mul_assoc]
    _ < ⊤ := by
        have := hI.ne
        finiteness

end GlobalTheory.WeilThetaConv

end
