import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefLatticeIndepCoefMapProofStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOfLowSmoothLines
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLatAtIffHat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormIntegrality

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open GlobalTheory.ConjTwist (BaseOf)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TupLe.CoefPf

theorem coefSt : CoefSt := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j hr hm B hB hBo c hc hS u hu O' hO' h hh v hv
  have hL : Links2 p := GlobalTheory.T.second_link_of_weight_rows _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  obtain ⟨gramR, c0R, c0L, hft, u', hu', hF⟩ := hS
  have huu : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  subst huu
  obtain ⟨F, hF0, rfl⟩ := GlobalTheory.T.coefLattice_indep_coefMap_proof D _ _ _ p.P.A3.A _ (R2 p) (F2 p) hC j c0L ⟨gramR, c0R, hft⟩ h v hv

  have hio : IoExt (R2 p) := hr.ioExt
  have hv0 : IsChosenExtremalVector (R2 p) j (sg0 D p.P.A3.A) (p.v₀ j _) := (hL.2.2.2.2.2.2.1 j).2.lift.v0
  have hval : ∀ w, (R2 p).ioP j (PiTensorProduct.tprod ℂ u') w ∈ harm (Wc D j).rank B.w B.F.BS := by
    have hcV : ((R2 p).cV j).Is := hC.models.cV j
    obtain ⟨u'', w₀, hu'', -, hw⟩ := IsChosenExtremalVector.io _ hv0 hio
    have huu : u'' = u' := funext fun ρ => Subtype.ext ((hu'' ρ).trans (hu ρ).symm)
    rw [huu] at hw
    have hT := GlobalTheory.SeriesTie.Scale.io_act hC.lev hC.thP hB hBo.ψ hBo.θ hBo.sT hBo.BS hBo.BT hBo.mu0 hBo.eta
      (PiTensorProduct.tprod ℂ u')
    have hΔ0 := GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) j
    rcases hcV.2.2.2.2 ((harm (Wc D j).rank B.w B.F.BS).comap ((R2 p).ioP j (PiTensorProduct.tprod ℂ u'))) (fun g => by
        obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 g
        rw [map_mul, hcV.1 k hk, mul_one]
        rintro _ ⟨w, hw', rfl⟩
        rw [Submodule.mem_comap, hT a ha]
        exact fockGL_mem_harm _ _ _ hw') with h0 | h0
    · have h1 : w₀ ∈ (harm (Wc D j).rank B.w B.F.BS).comap ((R2 p).ioP j (PiTensorProduct.tprod ℂ u')) := by
        rw [Submodule.mem_comap, hw, ← hBo.delta]
        exact delta_mem_harm _ _
      rw [h0, Submodule.mem_bot] at h1
      rw [h1, map_zero] at hw
      exact absurd hw.symm hΔ0
    · exact fun w => (h0 ▸ Submodule.mem_top : w ∈ (harm (Wc D j).rank B.w B.F.BS).comap
        ((R2 p).ioP j (PiTensorProduct.tprod ℂ u')))
  have hL0 : (B.F.ΛS : Set (Fin (Vc D j).rank → D.host.E)) = L0c D (Vc D j) := by
    rw [hBo.ΛS]
    exact GlobalTheory.OneMapRef.FactsLat.selfDual_frame_level_one_lattice_eq_standard (hL.1.lev.βV j)
  refine ⟨c⁻¹ • (R2 p).ioP j (PiTensorProduct.tprod ℂ u') (c0L j F), ?_, (smul_inv_smul₀ hc _).symm⟩
  refine (mem_harmLat _ _ _).2 ⟨Submodule.smul_mem _ _ (hval _), ?_⟩
  have hF' : harmFn (Wc D j).rank B.w B.F.BS ((R2 p).ioP j (PiTensorProduct.tprod ℂ u') (c0L j F)) =
      c • coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) := hF F
  rw [map_smul, hF', inv_smul_smul₀ hc, hBo.lam, GlobalTheory.LatAtHLat.latAt_eq_hLat D _ _ B hL0]
  exact Submodule.subset_span ⟨F, hF0, rfl⟩

end GlobalTheory.BigOn.Exp.TupLe.CoefPf
