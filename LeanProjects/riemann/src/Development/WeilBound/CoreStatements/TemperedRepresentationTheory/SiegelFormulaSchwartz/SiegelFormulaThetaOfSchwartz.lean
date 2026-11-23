import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSiegelParabolicConjDoubledCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardUnitaryChartDoubledSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartMemRationalIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumTransportSchwartzBruhatStandard
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerSiegelUnipotentAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylFormulaStandardUnitaryGroupWeilDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsHeckeCharRestrictionEtaInv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelEqTsumSchrodingerFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CosetSumAlongMulEquivSubgroups
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledFlatSectionEqTranslateStandardSection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilFockDoubledPairOfWeilAndIchino
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionUnitary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLeviBlock
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.LeftInvOfIsSection
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionIntegrableAndContinuous
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsoluteThetaIntegralLeContinuousSeminormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableThetaKernelWeilRangeStatement
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergentStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilSchwartzParabolicEquivariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSectionContinuousStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSymmUnitaryChartStatement
open scoped TensorProduct ENNReal Matrix Classical NNReal
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicU GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

theorem PositivityTheory.SiegelWeilFormulaUnitary.siegelFormula_theta_of_schwartz' : GlobalTheory.Published.WeilSiegelFormula →
    ∀ (D : D7) (A B : HSp D) (m : Measure (GA D B)), m.IsHaarMeasure → 1 ≤ A.rank →
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)),
    IsWeilDatumO ψ (dblSp A) B 1 χ ω → ∀ f, IsThetaFunO ψ (dblSp A) B f → 2 * A.rank < B.rank →
    ∀ ν 𝓖, IsCovolOne (ratL B A) ν 𝓖 → LeftInv (siegelQ A) (swSection A B ν 𝓖 ω f) ∧
      ∀ g, CosetConv (siegel A) (GQ (dblSp A)) (swSection A B ν 𝓖 ω f) g ∧
        cosetSum (siegel A) (GQ (dblSp A)) (swSection A B ν 𝓖 ω f) g =
          ⨍ q, descend (GQ B) (fun h => thetaKO ω g h f) q ∂autMeasure B m := by
  intro hSieg D A B m hm hA ψ χ ω hW f hf hB ν 𝓖 hcov
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨μ, hμ, -⟩ := GlobalTheory.StdUnn.ConjElt.exists_isConj D
  obtain ⟨κ, hκ⟩ := GlobalTheory.StdUnn.chart_exists D A μ hμ
  obtain ⟨lam, hlam, hψ', -⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ hW.std θ hθ μ hμ
  obtain ⟨omS, hT⟩ := GlobalTheory.StdUnn.exists_transport_std D ψ A B χ ω hW ν 𝓖 hcov θ hθ κ
  have hχ := GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χ B.rank hW.hecT hW.resT
  have hWS : IsWeilSch (shift ψ lam) χ⁻¹ θ B ν omS :=
    ⟨GlobalTheory.StdUnn.transport_levi D ψ A B χ ω hW ν 𝓖 hcov θ hθ μ hμ κ hκ omS hT lam hlam,
     GlobalTheory.StdUnn.Unip.transport_unip D ψ A B χ ω hW ν 𝓖 hcov θ hθ μ hμ κ hκ omS hT lam hlam,
     GlobalTheory.StdUnn.WeylStd.main D ψ A B χ ω hW ν 𝓖 hcov θ hθ μ hμ κ hκ omS hT lam hlam⟩
  let Φ : schwartzA θ B.rank A.rank :=
    ⟨sch ψ A B ν 𝓖 f, ((GlobalTheory.SchSchwartzAll.schSchwartz D) ψ hW.std θ hθ A B ν 𝓖 hcov).1 f hf⟩
  have hΦ : Φ.1 = sch ψ A B ν 𝓖 (ω (((1 : siegel A) : GA D (dblSp A))⁻¹, 1) f) := by
    simp only [OneMemClass.coe_one, inv_one, Prod.mk_one_one, map_one, Module.End.one_apply]; rfl
  obtain ⟨-, -, hact⟩ := GlobalTheory.StdUnn.flat_swSec_eq_sect D ψ A B χ ω hW ν 𝓖 hcov θ hθ μ hμ κ hκ omS hT lam hlam 1 1 f hf Φ hΦ
  have hact' : ∀ g, (omS (κ g) Φ).1 = sch ψ A B ν 𝓖 (ω (g, 1) f) := fun g => by
    have := hact g; rwa [OneMemClass.coe_one, mul_one] at this
  have hval : ∀ g, swSection A B ν 𝓖 ω f g = 1 * (fun γ => (omS γ Φ).1 0) (κ (g * 1)) := fun g => by
    simp only [one_mul, mul_one]
    rw [hact' g, GlobalTheory.Core.Rk.IP.swSection_eq_swSec]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.swSec, sch, mixS_dblDec_zero]
  obtain ⟨H, hH⟩ := GlobalTheory.StdUnn.exists_height D A.rank
  have hL : LeftInv (P D A.rank ⊓ GF D A.rank) (fun γ => (omS γ Φ).1 0) := by
    have hs := LeftInvSect.leftInv_sect D A.rank (Iwasawa.exists_mul D A.rank) B (shift ψ lam) χ⁻¹ θ ν omS hχ.1 hWS H hH Φ
      (s0 B A.rank)
    intro γ hγ g
    have h := hs γ hγ g
    simpa only [sect, sub_self, npow, Complex.cpow_zero, one_mul] using h
  obtain ⟨hleft, hg⟩ := GlobalTheory.StdUnn.cosetSum_along_mulEquiv _ _ κ (siegel A) (GQ (dblSp A)) (P D A.rank) (GF D A.rank)
    (GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P D A μ hμ κ hκ) (GlobalTheory.StdUnn.chart_mem_GF_iff D A μ hμ κ hκ) (fun γ => (omS γ Φ).1 0) 1 1 _ hval hL
  have hterm : ∀ g, term (P D A.rank) (GF D A.rank) (fun γ => (omS γ (omS (κ g) Φ)).1 0) 1 =
      term (P D A.rank) (GF D A.rank) (fun γ => (omS γ Φ).1 0) (κ (g * 1)) := fun g => by
    funext q
    simp only [term, mul_one, map_mul, Module.End.mul_apply]
  refine ⟨hleft, fun g => ⟨(hg g).1 ?_, ?_⟩⟩
  · have hcφ : Continuous (fun γ => (omS γ Φ).1 0) := by
      have e : (fun γ => (omS γ Φ).1 0) = swSection A B ν 𝓖 ω f ∘ κ.symm := by
        funext γ
        have := hval (κ.symm γ)
        simp only [mul_one, one_mul, MulEquiv.apply_symm_apply] at this
        simp only [Function.comp_apply, this]
      rw [e]
      exact (GlobalTheory.T.theta_section_continuous D ψ A B χ ω hW f hf ν 𝓖 hcov).comp
        (GlobalTheory.T.continuous_symm_unitary_chart D A μ hμ κ hκ)
    have hs : (A.rank : ℝ) / 2 < (s0 B A.rank).re := by
      have : (2 * A.rank : ℝ) < B.rank := by exact_mod_cast hB
      simp only [s0, Complex.sub_re, Complex.div_ofNat_re, Complex.natCast_re]
      linarith
    exact GlobalTheory.T.siegel_eisenstein_convergent D A.rank χ⁻¹ (s0 B A.rank) _ hcφ
      (GlobalTheory.T.weil_schwartz_parabolic_equivariant D A.rank (shift ψ lam) χ⁻¹ θ B ν omS hWS Φ) hs (κ (g * 1))
  · rw [(hg g).2, one_mul]
    have h := hSieg D A.rank B hA hB (shift ψ lam) hψ' χ⁻¹ hχ.1 hχ.2 θ hθ ν 𝓖 hcov omS hWS m hm (omS (κ g) Φ)
    unfold cosetSum at h ⊢
    rw [hterm g] at h
    rw [h]
    congr 1
    funext q
    congr 1
    funext h'
    rw [GlobalTheory.StdUnn.thetaKO_eq_tsum_sch D ψ A B χ ω hW ν 𝓖 hcov f hf g h', hact' g]
    rfl

theorem PositivityTheory.SiegelWeilFormulaUnitary.weilSiegelFormulaUnitary_of_two :
    GlobalTheory.Published.WeilThetaConvergence → GlobalTheory.Published.WeilSiegelFormula → GlobalTheory.Published.WeilSiegelFormulaUnitary := by
  intro hT hS D A B m hm hA hW
  refine ⟨GlobalTheory.T.absoluteThetaIntegral_le_continuousSeminorm hT D A B m hm hA hW, fun ψ χ ω hω f hf => ⟨GlobalTheory.T.integrable_thetaKernel_weilRange hT D A B m hm hA hW ψ χ ω hω f hf, ?_⟩⟩
  intro hab ν 𝓖 hν
  exact PositivityTheory.SiegelWeilFormulaUnitary.siegelFormula_theta_of_schwartz' hS D A B m hm hA ψ χ ω hω f hf hab ν 𝓖 hν
