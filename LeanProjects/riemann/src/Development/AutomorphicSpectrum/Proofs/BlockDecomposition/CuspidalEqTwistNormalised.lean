import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterPrescribedCentre
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec GlobalTheory.UnitaryBC PositivityTheory.PRW.GKD

namespace GlobalTheory.CompanionTheory.TwistNorm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem val_expId (ω : HChar E) (t : ℝ) :
    ((ω.1 (GlobalTheory.DiscChar.expId E t) : ℂˣ) : ℂ) = Complex.exp (t * dchi ω 1) := by
  refine (chiInf_expU ω _).trans (congrArg _ ?_)
  rw [show (fun _ : InfinitePlace E => (t : ℂ)) = t • (1 : Cinf E) from funext fun _ => by simp, map_smul]
  simp

theorem isNormalised_rank_zero (π : CuspSub E 0) : IsNormalised π := fun φ _ t g => by
  rw [Subsingleton.elim (splitCentre E 0 t * g) g]

theorem isNormalised_twist {π : CuspSub E a} {ω ν : HChar E} (hω : π.HasCentral ω)
    (hν : ∀ t : ℝ, ((chiDet a ν (splitCentre E a t) : ℂˣ) : ℂ) = Complex.exp (-(t * dchi ω 1))) :
    IsNormalised (π.twist ν) := by
  rintro _ ⟨ψ, hψ, rfl⟩ t g
  change ψ.1 (splitCentre E a t * g) * (chiDet a ν (splitCentre E a t * g) : ℂˣ) = ψ.1 g * (chiDet a ν g : ℂˣ)
  have h1 : ψ.1 (splitCentre E a t * g) = Complex.exp (t * dchi ω 1) * ψ.1 g := by
    rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_eq_scalar, hω.apply hψ]
    exact congrArg (· * ψ.1 g) (val_expId ω t)
  rw [h1, map_mul, Units.val_mul, hν, mul_mul_mul_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

theorem exists_twist_normalised : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}, ∀ (π : CuspSub E a),
    ∃ (π₀ : CuspSub E a) (χ : HChar E), IsNormalised π₀ ∧ π = π₀.twist χ := by
  intro E _ _ _ a π
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨π, 1, isNormalised_rank_zero π, π.twist_one.symm⟩
  · obtain ⟨ω, hω⟩ := Central.exists_hasCentral E a π
    obtain ⟨ν, hν⟩ := GlobalTheory.SplitCentreChar.exists_hChar_splitCentre E a ha (dchi ω 1)
    refine ⟨π.twist ν, ν⁻¹, isNormalised_twist hω hν, ?_⟩
    rw [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one]

end GlobalTheory.CompanionTheory.TwistNorm

end
