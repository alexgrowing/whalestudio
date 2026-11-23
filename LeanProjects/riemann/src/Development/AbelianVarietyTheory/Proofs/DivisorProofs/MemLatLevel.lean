import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt

noncomputable section

namespace GlobalTheory.ThKLevel

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d : ℕ}

variable (σ) in

def latLevel (W : Spc F E d) : Subgroup (UA σ W.J) where
  carrier := {k | k ∈ GlobalTheory.ThKAdm.FinPt σ W ∧ ∀ w : Pl F, ∀ z ∈ GlobalTheory.InertSph.latAt W w,
    mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt W w ∧ mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt W w}
  one_mem' := ⟨(UAtSub σ W (fun a : AF F => a.2)).one_mem, fun w z hz => by
    simp only [inv_one]
    rw [show mat (1 : UA σ W.J) = 1 from rfl, Matrix.one_mulVec]
    exact ⟨hz, hz⟩⟩
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨(UAtSub σ W (fun a : AF F => a.2)).mul_mem hx hy, fun w z hz => ⟨?_, ?_⟩⟩
    · rw [show mat (x * y) = mat x * mat y from rfl, ← Matrix.mulVec_mulVec]
      exact (hx' w _ (hy' w z hz).1).1
    · rw [mul_inv_rev, show mat (y⁻¹ * x⁻¹) = mat y⁻¹ * mat x⁻¹ from rfl, ← Matrix.mulVec_mulVec]
      exact (hy' w _ (hx' w z hz).2).2
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨(UAtSub σ W (fun a : AF F => a.2)).inv_mem hx, fun w z hz => ⟨(hx' w z hz).2, ?_⟩⟩
    rw [inv_inv]
    exact (hx' w z hz).1

theorem mem_latLevel {W : Spc F E d} {k : UA σ W.J} : k ∈ latLevel σ W ↔ k ∈ GlobalTheory.ThKAdm.FinPt σ W ∧
    ∀ w : Pl F, ∀ z ∈ GlobalTheory.InertSph.latAt W w,
      mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt W w ∧ mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt W w := Iff.rfl

theorem latLevel_le (W : Spc F E d) : (latLevel σ W : Set (UA σ W.J)) ⊆ GlobalTheory.ThKAdm.FinPt σ W := fun _ h => h.1

end GlobalTheory.ThKLevel

end
