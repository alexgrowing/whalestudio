import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MixedModelTargetHeisenbergAnisotropicPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixQuotientPeriodicIntegralContinuousPaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionMixedCoordsRankZeroStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesSummableOnCovolumeDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HeisMixSource

theorem heis_mixS : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ x a, d.mixS T ψ v.μ v.𝓕 (heisO ψ S T (d.extX T a) f) x = d.mixS T ψ v.μ v.𝓕 f (x + a)) ∧ (∀ x a, d.mixS T ψ v.μ v.𝓕 (heisO ψ S T (d.extY T a) f) x = ψ (symplO S T (d.extX T x) (d.extY T a)) • d.mixS T ψ v.μ v.𝓕 f x) ∧ (∀ x w, d.mixS T ψ v.μ v.𝓕 (heisO ψ S T (d.ext0 T w) f) x = heisO ψ S₀ T w (d.mixS T ψ v.μ v.𝓕 f x)) ∧ (Continuous fun p : Mx D T.rank ρ × WO S₀ T => d.mixS T ψ v.μ v.𝓕 f p.1 p.2) ∧ ∀ w, HasSum (fun x : Matrix (Fin T.rank) (Fin ρ) D.host.E => d.mixS T ψ v.μ v.𝓕 f (rat x) w) (f (d.ext0 T w)) := by
  intro D ψ hψ S S₀ T ρ d v f hf
  have hψc : Continuous ψ := hψ.1.1
  refine ⟨fun x a => GlobalTheory.MixModel.Check.mixS_heis_extX d v.μ v.𝓕 f a x, fun x a => ?_,
    fun x w => GlobalTheory.MixModel.Check.mixedModelSource_heisenberg_anisotropic_part d v.μ v.𝓕 f w x, ?_, fun w => ?_⟩
  · funext w₀
    rw [GlobalTheory.MixModel.Check.mixS_heis_extY d v.covol hf a x w₀]
    rfl
  · have hX : Continuous (d.extX T) := continuous_id.matrix_mul continuous_const
    have hY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
    have h0 : Continuous (d.ext0 T) := continuous_id.matrix_mul continuous_const
    have K := GlobalTheory.T.adelicMatrixQuotient_periodicIntegral_continuous_param D T.rank ρ v (Mx D T.rank ρ × WO S₀ T)
      (fun a p => heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T p.1) (heisO ψ S T (d.ext0 T p.2) f)) 0) ?_
      (fun γ hγ x p => d.integrandS_periodic hf p.1 p.2 γ hγ x)
    · exact K.2.1
    · have e : (Function.uncurry fun (a : Mx D T.rank ρ) (p : Mx D T.rank ρ × WO S₀ T) =>
          heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T p.1) (heisO ψ S T (d.ext0 T p.2) f)) 0) =
          fun q => ψ (symplOH S T (d.extY T q.1) (d.extX T q.2.1)) *
            f (d.extY T q.1 + d.extX T q.2.1 + d.ext0 T q.2.2) := by
        funext q; exact d.integrandS_eq f q.2.1 q.1 q.2.2
      rw [e]
      exact (hψc.comp (GlobalTheory.OrientedHeis.continuous_symplOH (hY.comp continuous_fst)
        (hX.comp (continuous_fst.comp continuous_snd)))).mul
        (hf.cont.comp (((hY.comp continuous_fst).add (hX.comp (continuous_fst.comp continuous_snd))).add
          (h0.comp (continuous_snd.comp continuous_snd))))
  · have hg0 : heisO ψ S T (d.ext0 T w) f 0 = f (d.ext0 T w) := by
      simp only [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]
    rcases Nat.eq_zero_or_pos ρ with rfl | hρ
    · have hz := (GlobalTheory.T.wittDecomposition_mixedCoords_rank_zero D ψ).1 S S₀ T d v.μ v.𝓕 v.covol f
      haveI : Subsingleton (Matrix (Fin T.rank) (Fin 0) D.host.E) := ⟨fun a b => Matrix.ext fun _ j => j.elim0⟩
      have h1 : ∀ x : Matrix (Fin T.rank) (Fin 0) D.host.E, d.mixS T ψ v.μ v.𝓕 f (rat x) w = f (d.ext0 T w) :=
        fun x => by rw [hz]
      rw [show (fun x : Matrix (Fin T.rank) (Fin 0) D.host.E => d.mixS T ψ v.μ v.𝓕 f (rat x) w) =
        fun _ => f (d.ext0 T w) from funext h1]
      exact hasSum_single (f := fun _ : Matrix (Fin T.rank) (Fin 0) D.host.E => f (d.ext0 T w))
        (0 : Matrix (Fin T.rank) (Fin 0) D.host.E) fun b hb => absurd (Subsingleton.elim b 0) hb
    · obtain ⟨hsplit, hrat, hYe, hXe, -, hres, -, -, -⟩ := GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d
      have hg : IsThetaFunO ψ S T (heisO ψ S T (d.ext0 T w) f) :=
        (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 _ _ hf
      have hcov : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ) v.μ v.𝓕 := hrat ▸ v.covol
      have hG := GlobalTheory.MixModel.gram_conjTranspose S
      have c1 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e * S.gram * d.e' = 1 := by
        have h := congrArg Matrix.conjTranspose d.e'e
        rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
          Matrix.conjTranspose_one, ← Matrix.mul_assoc] at h
      have c2 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e' * S.gram * d.e' = 0 := d.e'e'
      have c3 : GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D d.e' * S.gram * d.i₀ = 0 := by
        have h := congrArg Matrix.conjTranspose d.i₀e'
        rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hG,
          Matrix.conjTranspose_zero, ← Matrix.mul_assoc] at h
      have H := (GlobalTheory.TwFour.value_zero_eq_sum_restrictions D S S₀ T ρ d.e d.e' d.i₀ (hsplit hρ) c1 c2 c3 ψ hψ
        v.μ v.𝓕 hcov _ hg).2
      rw [hg0] at H
      convert H using 1
      funext y
      rw [hXe, ← hres, GlobalTheory.MixModel.Check.mixedModelSource_heisenberg_anisotropic_part]
      simp only [heisO, symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]
      rfl

end GlobalTheory.HeisMixSource
