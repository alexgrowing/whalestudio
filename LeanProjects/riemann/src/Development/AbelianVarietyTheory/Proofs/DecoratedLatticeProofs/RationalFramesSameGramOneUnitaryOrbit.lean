import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionHermitianFrames
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.WittOrbit
variable {D : D7}

theorem isQA_sig (D : D7) : GlobalTheory.SgAlg.IsQA (D.sp.cm.sig : D.host.E →+* D.host.E) := by
  refine ⟨fun x => star_star x, ?_, inferInstance, ?_, fun x _ hx => isUnit_iff_ne_zero.2 hx⟩
  · by_contra h
    push_neg at h
    have hbot : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ :=
      eq_top_iff.2 fun x _ => Algebra.mem_bot.2 ((D.sp.cm.fixed x).1 (h x))
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 hbot
    rw [D.sp.cm.deg2] at h1
    exact absurd h1 (by norm_num)
  · exact isUnit_iff_ne_zero.2 two_ne_zero

theorem free_of_li {n ρ : ℕ} (x : Matrix (Fin n) (Fin ρ) D.host.E) (h : LinearIndependent D.host.E x.transpose) :
    GlobalTheory.SgAlg.Free x := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' x)
    (LinearMap.ker_eq_bot.2 (Matrix.mulVec_injective_iff.2 h))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this

theorem isUnit_of_unitary (W : HSp D) {g : Matrix (Fin W.rank) (Fin W.rank) D.host.E}
    (h : gᴴ * W.gram * g = W.gram) : IsUnit g := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
  exact gram_det_ne W this.symm

theorem orb_eq_orbit : ∀ (D : D7) (W : HSp D) (ρ : ℕ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E),
    LinearIndependent D.host.E x₀.transpose →
      (∀ x ∈ Orb W x₀, ∃ γ ∈ GQ W, mt W γ ⬝ (rat x₀ : Mx D W.rank ρ) = rat x) ∧
        ∀ γ ∈ GQ W, ∀ x ∈ Orb W x₀, ∃ x' ∈ Orb W x₀, mt W γ ⬝ (rat x : Mx D W.rank ρ) = rat x' := by
  intro D W ρ x₀ h₀
  have hJ : GlobalTheory.SgAlg.IsHermU (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram :=
    ⟨gram_conjTranspose W, gram_isUnit_det W⟩
  refine ⟨fun x hx => ?_, fun γ hγ x hx => ?_⟩
  · obtain ⟨g, hg, hgx⟩ := GlobalTheory.SgAlg.witt_free_field _ (isQA_sig D) W.gram hJ x₀ x (free_of_li x₀ h₀)
      (free_of_li x hx.1) (by
        show x₀ᴴ * W.gram * x₀ = xᴴ * W.gram * x
        rw [Matrix.mul_assoc, Matrix.mul_assoc]
        exact hx.2.symm)
    have hg' : gᴴ * W.gram * g = W.gram := hg
    have hu : adj (rat g) * (gA W * rat g) = gA W := by
      rw [← rat_conjTranspose, gA, ← rat_mul, ← rat_mul, ← Matrix.mul_assoc, hg']
    refine ⟨ofMat W (rat g) hu, (mem_GQ_iff W _).2 ⟨g, rfl⟩, ?_⟩
    rw [mt_ofMat, ← rat_mul, hgx]
  · obtain ⟨g, hg⟩ := (mem_GQ_iff W γ).1 hγ
    replace hg : rat g = mt W γ := hg
    have hu : gᴴ * W.gram * g = W.gram := rat_injective (by
      rw [rat_mul, rat_mul, rat_conjTranspose, hg]
      exact mt_rel W γ)
    have hgu := isUnit_of_unitary W hu
    refine ⟨g * x, ⟨?_, ?_⟩, by rw [← hg, ← rat_mul]⟩
    · refine Matrix.mulVec_injective_iff.1 ?_
      intro v w hvw
      simp only [← Matrix.mulVec_mulVec] at hvw
      exact Matrix.mulVec_injective_iff.2 hx.1 (Matrix.mulVec_injective_iff_isUnit.2 hgu hvw)
    · show (g * x)ᴴ * (W.gram * (g * x)) = gramQ W x₀
      rw [← hx.2, gramQ, Matrix.conjTranspose_mul]
      calc xᴴ * gᴴ * (W.gram * (g * x)) = xᴴ * ((gᴴ * W.gram * g) * x) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hu]

end GlobalTheory.WittOrbit
