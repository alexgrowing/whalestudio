import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactUnitaryFiniteInvariantSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalar
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

namespace GlobalTheory

theorem jm_mul_self_uj {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem jm_conjTranspose_uj {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

theorem exists_inv_mem_UJset {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) : ∃ h ∈ UJset ε, h * g = 1 ∧ g * h = 1 := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have hJ := jm_mul_self_uj ε
  have hJs := jm_conjTranspose_uj ε
  set J := Formalism.REAL.Jm ε
  have hhg : (J * gᴴ * J) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hJ]
  have hgh : g * (J * gᴴ * J) = 1 := mul_eq_one_comm.1 hhg
  refine ⟨J * gᴴ * J, ?_, hhg, hgh⟩
  have hgJ : g * J * gᴴ = J := by
    have : g * J * gᴴ * J * J = J := by
      rw [show g * J * gᴴ * J = g * (J * gᴴ * J) by simp only [Matrix.mul_assoc], hgh, Matrix.one_mul]
    rwa [Matrix.mul_assoc (g * J * gᴴ), hJ, Matrix.mul_one] at this
  show (J * gᴴ * J)ᴴ * J * (J * gᴴ * J) = J
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJs]
  calc J * (g * J) * J * (J * gᴴ * J) = J * (g * J * (J * J) * gᴴ) * J := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [hJ, Matrix.mul_one, hgJ, hJ, Matrix.one_mul]

theorem star_eq_of_inv_UJset {n : ℕ} {ε : Fin n → Bool} {X : Type} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X] {σ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)}
    (hσ : IsURepOn (UJset ε) σ) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε)
    (hgh : g * h = 1) : star (σ g) = σ h := by
  have h1 : star (σ g) * σ g = 1 :=
    (ContinuousLinearMap.norm_map_iff_adjoint_comp_self (σ g)).1 (hσ.2.1 g hg)
  have h2 : σ g * σ h = 1 := by
    rw [ContinuousLinearMap.mul_def, ← hσ.1.2 g hg h hh, hgh, hσ.1.1]
  calc star (σ g) = star (σ g) * (σ g * σ h) := by rw [h2, mul_one]
    _ = σ h := by rw [← mul_assoc, h1, one_mul]

end GlobalTheory

namespace GlobalTheory

theorem uEquiv_of_intertwiner_ne_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (UJset ε) ρ → IsIrredOn (UJset ε) ρ → IsURepOn (UJset ε) π → IsIrredOn (UJset ε) π → ∀ B : H →L[ℂ] V, B ≠ 0 → (∀ g ∈ UJset ε, ∀ x, B (ρ g x) = π g (B x)) → UEquiv ε π ρ := by
  intro n ε H _ _ _ ρ V _ _ _ π hρ hρi hπ hπi B hB hBc

  have hBadj : ∀ g ∈ UJset ε, ∀ v, B.adjoint (π g v) = ρ g (B.adjoint v) := by
    intro g hg v
    obtain ⟨h, hh, hhg, hgh⟩ := exists_inv_mem_UJset hg
    have hcomp : B ∘L ρ h = π h ∘L B := ContinuousLinearMap.ext fun x => hBc h hh x
    have := congrArg ContinuousLinearMap.adjoint hcomp
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.star_eq_adjoint,
      star_eq_of_inv_UJset hρ hh hg hhg, star_eq_of_inv_UJset hπ hh hg hhg] at this
    exact (DFunLike.congr_fun this v).symm
  set A : H →L[ℂ] H := B.adjoint ∘L B with hAdef
  have hAsa : IsSelfAdjoint A := by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, hAdef, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  obtain ⟨c, hc⟩ := hilbert_schur_selfAdjoint H (UJset ε) (fun g => ρ g.1)
    (fun S hS hinv => hρi S hS (fun g hg v hv => hinv ⟨g, hg⟩ v hv)) A hAsa
    (fun g => ContinuousLinearMap.ext fun x => by
      simp only [ContinuousLinearMap.mul_apply, hAdef, ContinuousLinearMap.comp_apply]
      rw [hBc g.1 g.2 x, hBadj g.1 g.2])

  have hnorm : ∀ x, ((‖B x‖ ^ 2 : ℝ) : ℂ) = c * ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    have h1 : ⟪x, A x⟫_ℂ = ⟪B x, B x⟫_ℂ := by
      simp only [hAdef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    rw [hc] at h1
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right] at h1
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
    push_cast
    exact_mod_cast h1.symm
  obtain ⟨x0, hx0⟩ : ∃ x0, B x0 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hB (ContinuousLinearMap.ext hcon)
  have hx0' : x0 ≠ 0 := fun h => hx0 (by rw [h, map_zero])
  set r : ℝ := c.re with hr
  have hcr : c = (r : ℂ) := by
    have := hnorm x0
    have hpos : (0 : ℝ) < ‖x0‖ ^ 2 := by positivity
    have hc' : c = ((‖B x0‖ ^ 2 / ‖x0‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, this, mul_div_assoc, div_self (by exact_mod_cast hpos.ne'), mul_one]
    rw [hr, hc', Complex.ofReal_re]
  have hnormr : ∀ x, ‖B x‖ ^ 2 = r * ‖x‖ ^ 2 := by
    intro x
    have := hnorm x
    rw [hcr, ← Complex.ofReal_mul] at this
    exact_mod_cast this
  have hrpos : 0 < r := by
    have := hnormr x0
    have h1 : (0 : ℝ) < ‖B x0‖ ^ 2 := by positivity
    have h2 : (0 : ℝ) < ‖x0‖ ^ 2 := by positivity
    nlinarith
  set s : ℝ := Real.sqrt r with hs
  have hspos : 0 < s := Real.sqrt_pos.2 hrpos

  let U : H →L[ℂ] V := ((s⁻¹ : ℝ) : ℂ) • B
  have hU : ∀ x, ‖U x‖ = ‖x‖ := by
    intro x
    have hBx : ‖B x‖ = s * ‖x‖ := by
      rw [hs, ← Real.sqrt_sq (norm_nonneg (B x)), hnormr x, Real.sqrt_mul hrpos.le,
        Real.sqrt_sq (norm_nonneg x)]
    simp only [U, ContinuousLinearMap.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_inv, abs_of_pos hspos, hBx]
    field_simp
  have hUc : ∀ g ∈ UJset ε, ∀ x, U (ρ g x) = π g (U x) := by
    intro g hg x
    simp only [U, ContinuousLinearMap.smul_apply, hBc g hg x, map_smul]
  let L : H →ₗᵢ[ℂ] V := { toLinearMap := U.toLinearMap, norm_map' := hU }
  have hrange : LinearMap.range L.toLinearMap = ⊤ := by
    rcases hπi (LinearMap.range L.toLinearMap)
      (L.antilipschitz.isClosed_range L.isometry.uniformContinuous) (by
        rintro g hg v ⟨x, rfl⟩
        exact ⟨ρ g x, (hUc g hg x)⟩) with h | h
    · exfalso
      have hmem : L x0 ∈ LinearMap.range L.toLinearMap := ⟨x0, rfl⟩
      rw [h, Submodule.mem_bot] at hmem
      apply hx0'
      rw [← norm_eq_zero, ← L.norm_map x0, hmem, norm_zero]
    · exact h
  have hsurj : Function.Surjective L := by
    intro y
    have : y ∈ LinearMap.range L.toLinearMap := by rw [hrange]; trivial
    obtain ⟨x, hx⟩ := this
    exact ⟨x, hx⟩
  let e : H ≃ₗᵢ[ℂ] V := LinearIsometryEquiv.ofSurjective L hsurj
  refine ⟨e.symm, fun g hg v => e.injective ?_⟩
  rw [LinearIsometryEquiv.apply_symm_apply]
  show π g v = U (ρ g (e.symm v))
  rw [hUc g hg]
  congr 1
  exact (e.apply_symm_apply v).symm

end GlobalTheory
