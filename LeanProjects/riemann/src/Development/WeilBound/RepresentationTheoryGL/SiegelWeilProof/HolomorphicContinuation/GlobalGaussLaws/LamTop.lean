import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LamSing
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.UnipotentBlockMulAdd
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HermFourierZero
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PlaceFacts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentMapContinuousAdditiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCharacterContinuousUnitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientDataExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockWeilActionThetaUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPoints
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealParOfIsCharAF

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem nbFacts : NbFacts := GlobalTheory.T.unipotent_map_continuous_additive

theorem charFacts : CharFacts := GlobalTheory.T.hermitian_character_continuous_unit

theorem gLamBd : GLamBd := gLamBd_of nbFacts charFacts hermCocompact

theorem splitTauP : SplitTauP := fun _ _ _ _ _ hθ hι g => splitTau hθ hι g

namespace LamTopH

theorem chiPer : ChiPer := by
  intro D n ψ hψ β l hl
  have hl' : (hermA D n).subtype l ∈ ratMx D n n := AddSubgroup.mem_comap.1 hl
  obtain ⟨γ, hγ⟩ := hl'
  have e : Matrix.trace (HMul.hMul (β.1.map (incA D)) l.1 : Mx D n n) = incA D (Matrix.trace (β.1 * γ)) := by
    change Matrix.trace (β.1.map (incA D) * ((hermA D n).subtype l)) = _
    rw [← hγ]
    change Matrix.trace (β.1.map (incA D) * γ.map (incA D)) = _
    rw [← Matrix.map_mul]
    exact (AddMonoidHom.map_trace (incA D).toAddMonoidHom (β.1 * γ)).symm
  rw [e]
  have h2 : -halfTr (incA D (Matrix.trace (β.1 * γ))) = halfTr (incA D (-(Matrix.trace (β.1 * γ)))) := by
    simp only [halfTr, map_neg, mul_neg]
  rw [h2]
  exact GlobalTheory.CompanionTheory.EisUnfold.Summand.psi_halfTr_incA ψ hψ _

theorem nbTauP : NbTauP := by
  intro D n ψ θ τ ι hψ hθ hι nb hnb nb' hnb'
  refine ⟨fun x => ?_, fun β => ?_⟩
  · obtain ⟨b, hb, -⟩ := nbTau hθ hι nb hnb nb' hnb' x
    exact ⟨b, hb⟩
  obtain ⟨l, hl⟩ := GlobalTheory.StdUnn.exists_realPar_of_isCharAF D ψ hψ θ hθ
  have hβh : (β.1.map (tauE D τ)).IsHermitian := by
    ext i j
    have h1 : (β.1.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = β.1 := β.2
    have h2 : D.sp.cm.sig (β.1 j i) = β.1 i j := by
      have := congrFun (congrFun h1 i) j
      simpa [Matrix.transpose_apply, Matrix.map_apply] using this
    have h3 : tauE D τ (D.sp.cm.sig (β.1 j i)) = starRingEnd ℂ (tauE D τ (β.1 j i)) := D.sp.cm.cmUnram.2.1 _ _
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← h2, h3]
    rfl
  refine ⟨((l τ : ℝ) : ℂ) • β.1.map (tauE D τ), ?_, ?_, ?_⟩
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hβh.eq, Complex.star_def, Complex.conj_ofReal]
  · intro h0
    have h4 : (β.1.map (tauE D τ)).det = tauE D τ β.1.det := (RingHom.map_det (tauE D τ) β.1).symm
    rw [Matrix.det_smul, h4, h0, map_zero, mul_zero]
  · intro x b hb
    obtain ⟨b0, hb0, hfin, hτ, hoth, -⟩ := nbTau hθ hι nb hnb nb' hnb' x
    have hbb : b = b0 := by
      have h3 : nb b = nb b0 := hb.symm.trans hb0
      have hm := congrArg mat h3
      rw [hnb b, hnb b0] at hm
      have := congrArg PlaceFactsH.bOf hm
      rw [PlaceFactsH.upper_right_entry_block_matrix, PlaceFactsH.upper_right_entry_block_matrix] at this
      exact Subtype.ext this
    subst hbb
    set t := Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n) with ht
    have htfin : finPart D t = 0 := GlobalTheory.PhaseReal.finPart_trace _ _ hfin
    have hT := GlobalTheory.PhaseReal.trace_real htfin
    have hH : halfTr t = pairA D.host.F (fstA D.host.F (halfTr t)) 0 := by
      refine Prod.ext rfl ?_
      have h2 : (Algebra.trace (AF D.host.F) (AE D) t).2 = 0 := by rw [hT]; rfl
      show (algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) t).2 = 0
      rw [show (algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) t).2 =
        (algebraMap D.host.F (AF D.host.F) (1 / 2)).2 * (Algebra.trace (AF D.host.F) (AE D) t).2 from rfl, h2, mul_zero]
    rw [hH]
    have hpsi := hl (fstA D.host.F (halfTr t))
    rw [show psiInf D.host.F ψ (fstA D.host.F (halfTr t)) = ψ (pairA D.host.F (fstA D.host.F (halfTr t)) 0) from rfl]
      at hpsi
    rw [hpsi]

    have hθv : ∀ ρ, θ ρ (fstA D.host.F (halfTr t) ⊗ₜ[D.host.F] (1 : D.host.E)) = ((θ ρ (infPart D t)).re : ℂ) := by
      intro ρ
      have h2t : Algebra.trace (AF D.host.F) (AE D) t = algebraMap D.host.F (AF D.host.F) 2 * halfTr t := by
        show _ = algebraMap D.host.F (AF D.host.F) 2 *
          (algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) t)
        rw [← mul_assoc, ← map_mul]
        norm_num
      have hf : fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) t) = 2 * fstA D.host.F (halfTr t) := by
        rw [h2t, map_mul, AlgHom.commutes, map_ofNat]
      have hT2 := GlobalTheory.PhaseReal.theta_trace θ hθ ρ t
      rw [hf] at hT2
      have hmul : θ ρ ((2 * fstA D.host.F (halfTr t)) ⊗ₜ[D.host.F] (1 : D.host.E)) =
          2 * θ ρ (fstA D.host.F (halfTr t) ⊗ₜ[D.host.F] (1 : D.host.E)) := by
        have e : (2 * fstA D.host.F (halfTr t)) ⊗ₜ[D.host.F] (1 : D.host.E) =
            2 * (fstA D.host.F (halfTr t) ⊗ₜ[D.host.F] (1 : D.host.E)) := by
          rw [two_mul, TensorProduct.add_tmul, two_mul]
        rw [e, map_mul, map_ofNat]
      rw [hmul] at hT2
      push_cast at hT2
      linear_combination hT2 / 2
    simp_rw [hθv]
    have hpair : ∀ ρ, θ ρ (infPart D t) = Matrix.trace (β.1.map (tauE D ρ) * compAt θ ρ b.1) :=
      fun ρ => GlobalTheory.PhaseReal.theta_pair θ hθ ρ β.1 b.1
    rw [Finset.sum_eq_single τ]
    · rw [hpair, hτ]
      have hreal : (((Matrix.trace (β.1.map (tauE D τ) * herm x)).re : ℝ) : ℂ) =
          Matrix.trace (β.1.map (tauE D τ) * herm x) := by
        apply Complex.conj_eq_iff_re.1
        rw [← Complex.star_def, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
          PlaceFactsH.herm_conjTranspose, hβh.eq, Matrix.trace_mul_comm]
      rw [hreal]
      simp only [eTr, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    · intro ρ _ hρ
      rw [hpair, hoth ρ hρ, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re, Complex.ofReal_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ τ) h

end LamTopH

open LamTopH

theorem gLsing_of (hFZ : FourierZeroN) (hTS : TwoSided) (hD : DenseTau) : GLsing :=
  gLsing_core hFZ hTS hD GlobalTheory.T.coefficient_data_exists nbFacts charFacts hermCocompact splitTauP nbTauP chiPer

theorem gLsing (hTS : TwoSided) (hD : DenseTau) : GLsing := gLsing_of fourierZeroN hTS hD

end PositivityTheory.Rg.Sw.Glob
