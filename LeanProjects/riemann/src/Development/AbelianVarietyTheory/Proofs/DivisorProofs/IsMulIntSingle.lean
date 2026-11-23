import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLatticeDenominatorHeightBoundProof

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.ThetaDenom

variable (F : Type) [Field F] [NumberField F] in

def IsMulInt {κ : Type} (M : ℕ) (z : κ → AF F) : Prop :=
  (∀ i, (z i).1 = 0) ∧ ∀ v i, ‖evFin F v (z i)‖ ≤ ‖(M : Fv F v)‖

theorem isMulInt_single {F : Type} [Field F] [NumberField F] {κ : Type} [DecidableEq κ] (K : ℕ) (i : κ) (t : AF F)
    (ht0 : t.1 = 0) (ht1 : ∀ v, ‖evFin F v t‖ ≤ 1) : IsMulInt F K (Pi.single i ((K : AF F) * t)) := by
  refine ⟨fun j => ?_, fun v j => ?_⟩
  · by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same, show ((K : AF F) * t).1 = (K : AF F).1 * t.1 from rfl, ht0, mul_zero]
    · rw [Pi.single_eq_of_ne hj]; rfl
  · by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same, map_mul, map_natCast, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (ht1 v)
    · rw [Pi.single_eq_of_ne hj, map_zero, norm_zero]; exact norm_nonneg _

theorem IsMulInt.mono {F : Type} [Field F] [NumberField F] {κ : Type} {k m : ℕ} {a : κ → AF F}
    (h : IsMulInt F (k * m) a) : IsMulInt F m a := by
  refine ⟨h.1, fun v i => (h.2 v i).trans ?_⟩
  rw [Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (GlobalTheory.SmoothForms.denom_norm_natCast_le_one v k)

theorem fin_step {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ] (ψ : AddChar (AF F) ℂ)
    (K : ℕ) (Ψ : (κ → AF F) → ℂ) (hfix : ∀ y, IsMulInt F K y → schr ψ (0, y) Ψ = Ψ) (ξ : κ → F)
    (hξ : Ψ (fun j => algebraMap F (AF F) (ξ j)) ≠ 0) (i : κ) (t : AF F) (ht0 : t.1 = 0)
    (ht1 : ∀ v, ‖evFin F v t‖ ≤ 1) : ψ (algebraMap F (AF F) ((K : F) * ξ i) * t) = 1 := by
  have e1 := congrFun (hfix _ (isMulInt_single K i t ht0 ht1)) (fun j => algebraMap F (AF F) (ξ j))
  simp only [schr, dotProduct_single, zero_dotProduct, Pi.zero_apply, zero_mul, mul_zero, add_zero] at e1
  have e2 := (mul_eq_right₀ hξ).1 e1
  rw [← e2]
  congr 1
  rw [(algebraMap F (AF F)).map_mul, map_natCast]
  ring

def sand {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) :
    Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AF F ⊗[F] E) where
  toFun X := g * X * hᵀ
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

example {F : Type} [Field F] [NumberField F] (M : ℕ) : IsMulInt F M (0 : Fin 2 → AF F) :=
  ⟨fun _ => rfl, fun v _ => by rw [Pi.zero_apply, map_zero, norm_zero]; exact norm_nonneg _⟩

end GlobalTheory.ThetaDenom

end
