import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.CxDataModel
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ExtraSt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLoc

noncomputable section

open Matrix
open scoped Kronecker ComplexConjugate

namespace PositivityTheory.RgBcC

variable {n : ℕ} {lam : Fin n → ℤ}

theorem diag_inv_eq (z : Fin n → ℂ) (hz : ∀ a, ‖z a‖ = 1) :
    (diagonal z)⁻¹ = diagonal (fun a => conj (z a)) ∧ (diagonal z)ᴴ = diagonal (fun a => conj (z a)) := by
  have hc : ∀ a, z a * conj (z a) = 1 := fun a => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz a]; simp
  refine ⟨Matrix.inv_eq_right_inv (by rw [diagonal_mul_diagonal]; simp [hc]), ?_⟩
  rw [diagonal_conjTranspose]; rfl

theorem isLefK_of (hGT : GamTrace) (hlam : Antitone lam) : Real.IsLefK lam (lefE n lam) (lefT n lam) := by
  have hu := (avg n lam).1
  have hS := swapLaws_of rmLaws
  refine ⟨fun k => TK_f hu hS k, Tsq_f hu hS, fun k z hk hinj => ?_⟩
  have hz : ∀ a, ‖z a‖ = 1 := by
    intro a
    have h1 : k.1ᴴ * k.1 = 1 := Unitary.star_mul_self_of_mem k.2
    rw [hk, diagonal_conjTranspose, diagonal_mul_diagonal] at h1
    have h2 := congrFun (congrFun h1 a) a
    simp only [diagonal_apply_eq, one_apply_eq, Pi.star_apply] at h2
    have h3 : Complex.normSq (z a) = 1 := by
      rw [← Complex.ofReal_inj, ← Complex.mul_conj, mul_comm]; simpa using h2
    rw [Complex.normSq_eq_norm_sq] at h3
    nlinarith [norm_nonneg (z a)]
  obtain ⟨hinv, hH⟩ := diag_inv_eq z hz
  have hz0 : ∀ a, z a ≠ 0 := fun a h => by
    have := hz a; rw [h, norm_zero] at this; exact zero_ne_one this
  have hne : ∀ a, conj (z a) ≠ 0 := fun a h => hz0 a ((map_eq_zero _).mp h)
  have hinj1 : Function.Injective z := fun a b h => hinj (by simp [h])
  have hinjc : Function.Injective fun a => conj (z a) := fun a b h =>
    hinj1 ((RingHom.injective (starRingEnd ℂ)) h)
  have hρ : ((lefE n lam).ρ k) = lefFr n lam (diagonal z) := by rw [← hk]; rfl
  have hR := rmLaws n lam
  have hd : IsUnit (diagonal z).det := by
    rw [det_diagonal]; exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => hz0 a)
  have hdi : IsUnit ((diagonal z)⁻¹).det := by
    rw [hinv, det_diagonal]; exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => hne a)
  have hinvR : (Rm lam (diagonal z))⁻¹ = Rm lam (diagonal z)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [← hR.2.1 _ _ hd hdi, Matrix.mul_nonsing_inv _ hd, hR.1]
  have hch : (Rm lam (diagonal fun a => conj (z a))).trace = conj (weylChar lam z) := by
    rw [rmChar n lam hlam _ hne hinjc, weylChar_conj]
  constructor
  · rw [hρ]
    show LinearMap.trace ℂ (EV n lam) ((lefFr n lam (diagonal z) : EV n lam →L[ℂ] EV n lam) : EV n lam →ₗ[ℂ] EV n lam) = _
    rw [lefFr_apply, trace_cj hu, frame_zero_apply, trace_kronecker, hGT n z hz, rhoW, trace_kronecker, trace_transpose,
      trace_transpose, hinvR, hinv, hH, hch, pow_two]
  · rw [hρ]
    show LinearMap.trace ℂ (EV n lam) ((lefFr n lam (diagonal z) * lefT n lam : EV n lam →L[ℂ] EV n lam) :
      EV n lam →ₗ[ℂ] EV n lam) = _
    rw [lefT_apply, lefFr_apply, cj_mul hu, frame_zero_apply, ← mul_kronecker_mul, mul_one, trace_cj hu, trace_kronecker,
      hGT n z hz, rhoW, (hS n lam).2.2.2.2, ← transpose_mul, trace_transpose, hinvR, ← hR.2.1 _ _ (by rw [hH, det_diagonal]; exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => hne a)) hdi, hH, hinv,
      diagonal_mul_diagonal]
    have hne2 : ∀ a, conj (z a) * conj (z a) ≠ 0 := fun a => mul_ne_zero (hne a) (hne a)
    have hinj2 : Function.Injective fun a => conj (z a) * conj (z a) := fun a b h => hinj (by
      have h' : conj (z a ^ 2) = conj (z b ^ 2) := by simpa [pow_two] using h
      exact (RingHom.injective (starRingEnd ℂ)) h')
    rw [rmChar n lam hlam _ hne2 hinj2, ← weylChar_conj]
    congr 2; funext a; simp [pow_two]

end PositivityTheory.RgBcC
