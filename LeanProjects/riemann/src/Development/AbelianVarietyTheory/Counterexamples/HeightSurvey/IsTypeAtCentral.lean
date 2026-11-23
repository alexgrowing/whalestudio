import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.TypeAtTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rep
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem dRep_char (m : ℤ) (θ : ℝ) (w : ℂ) :
    dRep (n := 1) (fun g => (g 0 0 ^ m) • ContinuousLinearMap.id ℂ ℂ) (diagonal fun _ => (θ : ℂ) * Complex.I) w =
      ((m : ℂ) * θ * Complex.I) * w := by
  have hexp : ∀ s : ℝ, NormedSpace.exp (s • (diagonal fun _ : Fin 1 => (θ : ℂ) * Complex.I)) 0 0 =
      Complex.exp ((s : ℂ) * ((θ : ℂ) * Complex.I)) := by
    intro s
    rw [← Matrix.diagonal_smul, Matrix.exp_diagonal, Matrix.diagonal_apply_eq, Pi.exp_def,
      ← Complex.exp_eq_exp_ℂ]
    simp [Complex.real_smul]
  have hd : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * ((m : ℂ) * ((θ : ℂ) * Complex.I))) * w)
      (((m : ℂ) * θ * Complex.I) * w) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * ((m : ℂ) * ((θ : ℂ) * Complex.I)))
        (((1 : ℝ) : ℂ) * ((m : ℂ) * ((θ : ℂ) * Complex.I))) 0 :=
      (hasDerivAt_id' (0 : ℝ)).ofReal_comp.mul_const _
    refine (h1.cexp.mul_const w).congr_deriv ?_
    simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_mul, Complex.exp_zero, one_mul]
    ring
  unfold dRep
  refine HasDerivAt.deriv (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_))
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, hexp]
  rw [← Complex.exp_int_mul]
  congr 2
  ring

end Rep

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem isTypeAt_zero {τ : D.what₂.Tau} {S : SPar} : IsTypeAt θ V τ S 0 ↔
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
      (P : Matrix (Fin V.rank) (Fin V.rank) ℂ),
      IsEnum S lam ε ∧ IsDS ε lam σ ∧ IsUnit P ∧ Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ := by
  constructor
  · rintro ⟨H, i1, i2, σ, lam, ε, P, h1, h2, h3, h4, -⟩
    exact ⟨H, i1, i2, σ, lam, ε, P, h1, h2, h3, h4⟩
  · rintro ⟨H, i1, i2, σ, lam, ε, P, h1, h2, h3, h4⟩
    refine ⟨H, i1, i2, σ, lam, ε, P, h1, h2, h3, h4, fun x => ⟨fun _ => 0, fun i => ?_, fun _ => 0,
      fun i => ?_, ⟨[], fun _ => 0, by simp, fun i w _ => by simp, fun S' _ => by simp,
        ⟨fun _ => 0, continuous_const, fun g _ w _ => by simp⟩⟩, fun g _ => by simpa using hasSum_zero⟩⟩
    · intro k Xs _
      simp only [map_zero]
      exact contDiff_const
    · exact ⟨[], 0, by simp, fun w _ => by simp⟩

end GlobalTheory.TypeAtTest
end
