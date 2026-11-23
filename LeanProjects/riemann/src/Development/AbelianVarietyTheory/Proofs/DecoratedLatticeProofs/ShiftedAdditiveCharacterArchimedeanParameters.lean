import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

set_option synthInstance.maxHeartbeats 400000 in

theorem shift_char_realPar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∃ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ ∧ IsCharAF D.host.F (shift ψ lam) ∧ ∃ l : D.what₂.Tau → ℝ, HasRealPar (shift ψ lam) θ l ∧ ∀ τ, |l τ| = ‖tauE D τ D.host.xi0‖ / ‖tauE D τ μ‖ := by
  intro D ψ hψ θ hθ μ hμ
  have hstar : ∀ x : D.host.E, star x = IsCMField.complexConj D.host.E x := fun _ => rfl
  set y : D.host.E := -D.host.xi0 / μ with hy_def
  have hyc : IsCMField.complexConj D.host.E y = y := by
    rw [hy_def, map_div₀, map_neg, conj_xi0_alt, ← hstar μ, hμ.2, neg_neg, div_neg, neg_div]
  have hyF : y ∈ D.host.F := (IsCMField.complexConj_eq_self_iff D.host.E y).1 hyc
  have hy0 : y ≠ 0 := div_ne_zero (neg_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)) hμ.1
  let lam : D.host.F := ⟨y, hyF⟩
  have hlam : algebraMap D.host.F D.host.E lam = y := rfl
  have hlam0 : lam ≠ 0 := fun h => hy0 (by rw [← hlam, h, map_zero])
  refine ⟨lam, hlam, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hψ.1.1.comp (continuous_const.mul continuous_id)
    · intro x; exact hψ.1.2.1 _
    · intro a
      rw [shift, AddChar.mulShift_apply, ← map_mul]
      exact hψ.1.2.2.1 _
    · obtain ⟨x, hx⟩ := hψ.1.2.2.2
      refine ⟨algebraMap D.host.F (AF D.host.F) lam⁻¹ * x, ?_⟩
      rw [shift, AddChar.mulShift_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hlam0, map_one, one_mul]
      exact hx
  ·
    have hreal : ∀ τ, (tauE D τ y).im = 0 := by
      intro τ
      have h := IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) y
      rw [hyc] at h
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
    refine ⟨fun τ => -(tauE D τ y).re, ?_, ?_⟩
    · intro x
      have e1 : psiInf D.host.F (shift ψ lam) x =
          psiInf D.host.F ψ (algebraMap D.host.F (Ainf D.host.F) lam * x) := by
        simp only [psiInf, shift, AddChar.mulShift_apply]
        congr 1
        show (algebraMap D.host.F (Ainf D.host.F) lam * x, algebraMap D.host.F (Af D.host.F) lam * 0) = _
        rw [mul_zero]; rfl
      rw [e1, hψ.2.2 θ hθ]
      congr 1
      have e2 : ∀ ρ, θ ρ ((algebraMap D.host.F (Ainf D.host.F) lam * x) ⊗ₜ[D.host.F] (1 : D.host.E)) =
          θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) * tauE D ρ y := by
        intro ρ
        have e3 : (algebraMap D.host.F (Ainf D.host.F) lam * x) ⊗ₜ[D.host.F] (1 : D.host.E) =
            (x ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : Ainf D.host.F) ⊗ₜ[D.host.F] y) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ← Algebra.smul_def, ← TensorProduct.smul_tmul',
            ← TensorProduct.tmul_smul, Algebra.smul_def, mul_one, hlam]
        rw [e3, map_mul, (hθ ρ).1]
      simp only [e2]
      have e4 : ∀ ρ, (((-(tauE D ρ y).re : ℝ)) : ℂ) = -tauE D ρ y := by
        intro ρ
        apply Complex.ext <;> simp [hreal ρ]
      simp only [e4, Finset.mul_sum]
      push_cast
      refine Finset.sum_congr rfl fun ρ _ => ?_
      ring
    · intro τ
      have h1 : |(tauE D τ y).re| = ‖tauE D τ y‖ := by
        rw [← Complex.abs_re_eq_norm.2 (hreal τ)]
      rw [abs_neg, h1, hy_def, map_div₀, map_neg, norm_div, norm_neg]

end GlobalTheory.StdUnn
