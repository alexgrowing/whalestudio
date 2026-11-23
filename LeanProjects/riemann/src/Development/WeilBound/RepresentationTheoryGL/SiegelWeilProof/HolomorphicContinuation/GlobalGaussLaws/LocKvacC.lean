import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulasStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFockVectorOfSchrodingerMemFockSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStandardCartanInvolutionCommuteCompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanParametersAddCharUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnnihilationOperatorDoubledHermitianSpaceDecompStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledPairThetaFunctionEqZeroOfSchrodingerEqZerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnnihilationOperatorSchroedingerFunctionsDoubledStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorWeilOperatorCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerFunctionFockVectorPolynomialGaussian
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ShiftedAdditiveCharacterArchimedeanParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionLinearThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCartanInvStandardInvolutionDoubledGram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLeviBlock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorFiniteUnderCompactCommutingCartan
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IterPLin
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.RhoH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

theorem annS_stable : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
    ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ V.rank → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (μ : Measure (Mx D V.rank n)) (𝓕 : Set (Mx D V.rank n)), IsCovolOne (ratMx D V.rank n) μ 𝓕 →
    ∀ ω : G D n →* Module.End ℂ (schwartzA θ V.rank n), IsWeilSch ψ χ θ V μ ω → ∀ l : D.what₂.Tau → ℝ, HasRealPar ψ θ l →
    ∀ s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsCartanInv (gramAt D V τ) (s τ)) →
    ∀ (τ : D.what₂.Tau) (Φ : schwartzA θ V.rank n), (∀ X, annS V l s θ τ X Φ.1 = 0) →
    ∀ k ∈ K D n, ∀ X, annS V l s θ τ X (ω k Φ).1 = 0 := by
  intro D n V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω l hl s hs τ Φ hann k hk X
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  obtain ⟨hschS, hsurj, -⟩ := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ₀ hstd θ hθ A V μ 𝓕 hμ
  obtain ⟨f, hf, hfΦ⟩ := hsurj Φ.1 Φ.2
  obtain ⟨s', hstd', hcomm⟩ := GlobalTheory.T.exists_standardCartanInvolution_commute_compact D A μ' hsk κ hchart θ hθ

  have hkill1 : ∀ Z : Matrix (Fin V.rank) (Fin A.rank) ℂ,
      annih (heisO ψ₀ (dblSp A) V) θ τ (cplxO (s' τ) (s τ)) (Z * (dblDec A).qX.map (tauE D τ)) f = 0 := by
    intro Z
    apply GlobalTheory.T.doubledPairThetaFunction_eq_zero_of_schrodinger_eq_zero D ψ₀ hstd A V μ 𝓕 hμ _ (GlobalTheory.StdUnn.isThetaFunO_annih_of_std (A := A) (B := V) (ν := μ) (𝓨 := 𝓕) hstd hθ hμ τ _ _ hf)
    rw [GlobalTheory.T.annihilationOperator_schroedingerFunctions_doubledPair D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs f hf τ Z, hfΦ]
    exact hann Z
  have hkill : ∀ Y : Matrix (Fin V.rank) (Fin (dblSp A).rank) ℂ,
      annih (heisO ψ₀ (dblSp A) V) θ τ (cplxO (s' τ) (s τ)) Y f = 0 := by
    intro Y
    obtain ⟨Z, Z', c, hdec⟩ := GlobalTheory.T.annihilationOperator_doubledHermitianSpace_decomp D ψ₀ hstd θ hθ A V μ' hsk s' s hstd' hs τ Y
    rw [hdec f hf, hkill1, hkill1, smul_zero, add_zero]

  have hkk : κ (κ.symm k) ∈ K D A.rank := by
    rw [show κ (κ.symm k) = k from κ.apply_symm_apply k]
    exact hk
  have hS : ∀ τ', s' τ' * compAt θ τ' (Formalism.L2.Theta.mt (dblSp A) (κ.symm k)) =
      compAt θ τ' (Formalism.L2.Theta.mt (dblSp A) (κ.symm k)) * s' τ' := fun τ' => (hcomm (κ.symm k) hkk τ').symm
  have hm1 : ∀ τ', compAt θ τ' (Formalism.L2.Theta.mt V 1) = 1 := by
    intro τ'
    simp [Formalism.L2.Theta.mt, compAt, Matrix.map_one]
  have hT : ∀ τ', s τ' * compAt θ τ' (Formalism.L2.Theta.mt V 1) = compAt θ τ' (Formalism.L2.Theta.mt V 1) * s τ' := by
    intro τ'
    rw [hm1, Matrix.mul_one, Matrix.one_mul]
  let X' : Matrix (Fin V.rank) (Fin A.rank) ℂ := X
  set Y0 : Matrix (Fin V.rank) (Fin (dblSp A).rank) ℂ :=
    (X' * (dblDec A).qX.map (tauE D τ)) * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k)) with hY0
  have hmove := (GlobalTheory.FockMove.om_foldr hdat hθ (κ.symm k) 1 hS hT hf [(τ, Y0)]).2
  simp only [List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil] at hmove
  rw [hkill Y0, map_zero, hm1, Matrix.one_mul, hY0, Matrix.mul_assoc,
    GlobalTheory.WeilVacMove.compAt_mt_mul_inv, Matrix.mul_one] at hmove

  have htk := htr (κ.symm k) f hf Φ hfΦ.symm
  rw [show κ (κ.symm k) = k from κ.apply_symm_apply k] at htk
  have hth' : IsThetaFunO ψ₀ (dblSp A) V (omh (κ.symm k, 1) f) := hdat.om_pres _ f hf
  have e := GlobalTheory.T.annihilationOperator_schroedingerFunctions_doubledPair D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs _ hth' τ X'
  rw [← hmove] at e
  have hs0 : sch ψ₀ A V μ 𝓕 (0 : WO (dblSp A) V → ℂ) = 0 := by
    have := (GlobalTheory.StdUnn.sch_linear D ψ₀ hstd A V μ 𝓕 hμ f f hf hf 0).2.2.2
    rw [zero_smul, zero_smul] at this
    exact this
  rw [hs0] at e
  show annS V l s θ τ X ((ω k) Φ).1 = 0
  rw [show ((ω k) Φ).1 = sch ψ₀ A V μ 𝓕 (omh (κ.symm k, 1) f) from htk]
  exact e.symm

end PositivityTheory.Rg.Sw.Glob.RhoH
