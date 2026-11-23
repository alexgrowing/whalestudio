import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.FlatTheta

variable {D : D7} {σ : ℕ}

def lastQ (B : BesLev D σ) : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E :=
  Matrix.of fun k => Fin.snoc (α := fun _ => D.host.E) (B.d.e k) ((B.d.i₀ *ᵥ vecB B.o B.ζ) k)

theorem rat_lastQ (B : BesLev D σ) : rat (lastQ B) = xLast B.d (vecB B.o B.ζ) := by
  funext k j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · have := congrFun (ratV_mulVec B.d.i₀ (vecB B.o B.ζ)) k
    simp only [xLast, lastQ, rat, Matrix.map_apply, Matrix.of_apply, Fin.snoc_last]
    exact this
  · simp only [xLast, lastQ, rat, Matrix.map_apply, Matrix.of_apply, Fin.snoc_castSucc]
    rfl

theorem zeta_ne (B : BesLev D σ) : B.ζ ≠ 0 := fun h => B.line.2 (by rw [h]; simp)

theorem lastQ_indep (B : BesLev D σ) : LinearIndependent D.host.E (lastQ B).transpose := by
  have key : ∀ c : Fin (σ + 1) → D.host.E, lastQ B *ᵥ c =
      B.d.e *ᵥ (fun i => c i.castSucc) + c (Fin.last σ) • (B.d.i₀ *ᵥ (B.o.iB *ᵥ B.ζ)) := fun c => by
    funext k
    change ∑ j, lastQ B k j * c j = ∑ i, B.d.e k i * c i.castSucc + c (Fin.last σ) * (B.d.i₀ *ᵥ vecB B.o B.ζ) k
    rw [Fin.sum_univ_castSucc, mul_comm (c _)]
    simp only [lastQ, Matrix.of_apply, Fin.snoc_castSucc, Fin.snoc_last]
  refine Matrix.mulVec_injective_iff.1 ((injective_iff_map_eq_zero (lastQ B).mulVecLin).2 fun c hc => ?_)
  rw [Matrix.mulVecLin_apply, key] at hc
  have h1 := congrArg (B.d.qX *ᵥ ·) hc
  have h2 := congrArg ((B.o.qB * B.d.q0) *ᵥ ·) hc
  have a1 : B.d.qX * B.d.i₀ = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact B.d.pX_j0)
  have a2 : B.d.q0 * B.d.e = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact B.d.p0_jX)
  have a3 : B.d.q0 * B.d.i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact B.d.p0_j0)
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_zero, qX_e, Matrix.one_mulVec,
    ← Matrix.mul_assoc, a1, Matrix.zero_mul, Matrix.zero_mulVec, smul_zero, add_zero] at h1
  have a4 : B.o.qB * B.d.q0 * B.d.e = 0 := by rw [Matrix.mul_assoc, a2, Matrix.mul_zero]
  have a5 : B.o.qB * B.d.q0 * B.d.i₀ * B.o.iB = 1 := by
    rw [Matrix.mul_assoc B.o.qB, a3, Matrix.mul_one, B.o.qB_iB]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_zero,
    ← Matrix.mul_assoc, a4, a5, Matrix.zero_mulVec, zero_add, Matrix.one_mulVec] at h2
  funext j
  refine Fin.lastCases ?_ (fun i => congrFun h1 i) j
  exact (smul_eq_zero.1 h2).resolve_right (zeta_ne B)

theorem flat_isThetaFun : ∀ D : D7, FlatLaw D → ∀ (ψ : AddChar (AF D.host.F) ℂ), (∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) Ψ, IsThetaFunO ψ B.V J.W Ψ → IsThetaFunO ψ B.V₀ J.W₀ (flatBF s Ψ)) ∧ ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) Ψ, IsThetaFunO ψ J.W B.V Ψ → IsThetaFunO ψ J.W₀ B.V₀ (flatFB s Ψ) := by
  intro D hF ψ
  refine ⟨fun ρ B J s Ψ hΨ => ?_, fun σ J B s Ψ hΨ => ?_⟩
  · exact (hF ψ s.weil.std B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU J.d.e (isIsoSub_e J.d).1
      (yZero B.V₀ ρ (vecB B.o B.ζ)) Ψ hΨ).2
  · have h := (hF ψ s.weil.std J.W J.W₀ B.V B.V₀ (σ + 1) σ J.d B.d s.vS s.vT s.vU (lastQ B) (lastQ_indep B) 0 Ψ hΨ).2
    rw [rat_lastQ] at h
    exact h

end GlobalTheory.Unf.FlatTheta

end
