import Mathlib
import Formalism.PeriodIntegrals.UpqRep
import Formalism.PeriodIntegrals.IsLowUnitH
import Formalism.PeriodIntegrals.ZuckTensor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.DualDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.DualChoice

open Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor

def RevUJ : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ), g ∈ UJset (revE ε) → revM g ∈ UJset ε

def DualVec : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ), g ∈ UJset ε → ∀ x y : Fin n → ℂ,
    (starRingEnd ℂ) (star y ⬝ᵥ (revM g *ᵥ x)) =
      star (Jm ε *ᵥ (x ∘ Fin.rev)) ⬝ᵥ (g⁻¹ *ᵥ (Jm ε *ᵥ (y ∘ Fin.rev)))

def JJ : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (x : Fin n → ℂ), Jm ε *ᵥ (Jm ε *ᵥ x) = x

def RevSingle : Prop :=
  ∀ (n : ℕ) (lam : Fin n → ℝ) (s : Fin n), revP (lam + Pi.single s 1) = revP lam - Pi.single (Fin.rev s) 1

section Eq
variable {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [NormedAddCommGroup B] [InnerProductSpace ℂ B]

def cjEquivInv (U : Cj A ≃ₗᵢ[ℂ] Cj B) : A ≃ₗᵢ[ℂ] B where
  toFun x := Cj.un (U (Cj.mk x))
  invFun y := Cj.un (U.symm (Cj.mk y))
  left_inv x := by
    show Cj.un (U.symm (U (Cj.mk x))) = x
    rw [U.symm_apply_apply]; rfl
  right_inv y := by
    show Cj.un (U (U.symm (Cj.mk y))) = y
    rw [U.apply_symm_apply]; rfl
  map_add' x y := by
    show Cj.un (U (Cj.mk x + Cj.mk y)) = _
    rw [map_add]; rfl
  map_smul' c x := by
    have e : Cj.mk (c • x) = (starRingEnd ℂ) c • Cj.mk x := by
      show c • x = (starRingEnd ℂ) ((starRingEnd ℂ) c) • x
      rw [Complex.conj_conj]
    show Cj.un (U (Cj.mk (c • x))) = c • Cj.un (U (Cj.mk x))
    rw [e, map_smul, Cj.un_smul, Complex.conj_conj]
  norm_map' x := U.norm_map (Cj.mk x)

end Eq

end PI.ZuckTensorWork
end
