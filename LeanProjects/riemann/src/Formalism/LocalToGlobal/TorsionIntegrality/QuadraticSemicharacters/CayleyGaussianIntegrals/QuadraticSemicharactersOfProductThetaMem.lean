import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactVersion
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LogarithmEquivalence

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.H

section Arith

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem relIdx_smul_mem (Λ₁ Λ₂ : AddSubgroup V) {x : V} (hx : x ∈ Λ₂) :
    (relIdx Λ₁ Λ₂ : ℂ) • x ∈ Λ₁ := by
  have h := AddSubgroup.nsmul_index_mem (Λ₁.addSubgroupOf Λ₂) ⟨x, hx⟩
  rw [AddSubgroup.mem_addSubgroupOf] at h
  unfold relIdx
  rw [Nat.cast_smul_eq_nsmul]
  simpa [AddSubgroup.relIndex] using h

theorem altE_natCast_smul_left (H : Sesq V) (N : ℕ) (s x : V) :
    altE H ((N : ℂ) • s) x = (N : ℝ) * altE H s x := by
  simp [altE, map_smul]

theorem phase_root (H : Sesq V) (Λ : AddSubgroup V) (hΛ : Λ ≤ dualLat H Λ) (N : ℕ) {s x : V}
    (hs : (N : ℂ) • s ∈ Λ) (hx : x ∈ Λ) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ)) ^ (2 * N) = 1 := by
  obtain ⟨m, hm⟩ := (show ∀ y ∈ Λ, ∃ m : ℤ, altE H ((N : ℂ) • s) y = (m : ℝ) from hΛ hs) x hx
  rw [altE_natCast_smul_left] at hm
  have hm' : (N : ℂ) * (altE H s x : ℂ) = (m : ℂ) := by exact_mod_cast hm
  rw [← Complex.exp_nat_mul]
  have h2 : ((2 * N : ℕ) : ℂ) * (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ)) =
      ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    linear_combination (-2 * (Real.pi : ℂ) * Complex.I) * hm'
  rw [h2, Complex.exp_int_mul_two_pi_mul_I]

theorem phase_root_selfDual (H : Sesq V) (Λ : AddSubgroup V) (hΛ : IsSelfDual H Λ) (N : ℕ) {s x : V}
    (hs : (N : ℂ) • s ∈ Λ) (hx : x ∈ Λ) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H s x : ℂ)) ^ (2 * N) = 1 := by
  exact phase_root H Λ hΛ.ge N hs hx

end Arith

theorem quadraticSemicharacters_of_productThetaMem (hF0 : ProductThetaMem) : quadraticSemicharacterIdentityReformulated₂ := by
  intro L ω₀ n _ _ h Λ α β g D ε θ hθ S hS t y
  have hH : IsHerm (stdH L (Fin 4 × n)) := (standardFormBasic L (Fin 4 × n)).2.1
  have hfix : F0 L ω₀ (Fin 4 × n) ∈ fixedBy (stdH L (Fin 4 × n)) β (stdLat L (Fin 4 × n)) :=
    ((hF0 L ω₀ (Fin 4 × n) D.per D.half β D.betaStd).1).2

  have h1 : tens4 (opU (matH h) t θ) (g.symm y)
      = opU (matH (blk4 h)) (fun w => t w.2) (tens4 θ) (g.symm y) :=
    ((heisenbergFourfold n h).2 (fun w => t w.2) (fun _ => θ) (g.symm y)).symm

  have h2 : tens4 θ = fun v => ε * (fun z => ((Real.sqrt (relIdx (stdLat L (Fin 4 × n))
      (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) : ℝ) : ℂ)⁻¹ *
        ∑ x ∈ S, β x * opU (stdH L (Fin 4 × n)) x (F0 L ω₀ (Fin 4 × n)) z)
          ((g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) v) := by
    rw [hθ]
    funext v
    have := InterReps_of semicharacterHom (Fin 4 × n → ℂ) (stdH L (Fin 4 × n)) hH (stdLat L (Fin 4 × n))
      (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ)) β D.betaSemi _ hfix S hS (g v)
    simp only [Pi.smul_apply, smul_eq_mul, kernel4]
    rw [this]
    rfl
  rw [h1, h2, Inv.opU_const_mul]
  erw [heisenbergIsometry _ _ _ _ _ D.isom (fun w => t w.2) (fun z => ((Real.sqrt (relIdx (stdLat L (Fin 4 × n))
      (imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ))) : ℝ) : ℂ)⁻¹ *
        ∑ x ∈ S, β x * opU (stdH L (Fin 4 × n)) x (F0 L ω₀ (Fin 4 × n)) z) (g.symm y)]
  rw [Inv.opU_const_mul, Inv.opU_finset_sum]
  simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Inv.opU_const_mul, heisenbergMul _ _ hH, F0, heisenbergStandard]
  simp only [Pi.add_apply]
  ring

end Formalism.L2.Th1.H
