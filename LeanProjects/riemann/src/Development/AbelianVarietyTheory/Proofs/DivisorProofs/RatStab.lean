import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeSmallUnf

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (σ) in

def ratStab {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) : Subgroup (UA σ J) where
  carrier := {γ | γ ∈ ratU σ J ∧ ∃ l : (AE F E)ˣ, mat γ *ᵥ incV F x = l.1 • incV F x}
  mul_mem' := by
    rintro g h ⟨hg, l, hl⟩ ⟨hh, m, hm⟩
    refine ⟨mul_mem hg hh, m * l, ?_⟩
    have : mat (g * h) = mat g * mat h := rfl
    rw [this, ← Matrix.mulVec_mulVec, hm, Matrix.mulVec_smul, hl, smul_smul, Units.val_mul]
  one_mem' := ⟨one_mem _, 1, by simp [mat]⟩
  inv_mem' := by
    rintro g ⟨hg, l, hl⟩
    refine ⟨inv_mem hg, l⁻¹, ?_⟩
    have h1 : mat g⁻¹ * mat g = 1 := by simp [mat]
    have h2 : incV F x = l.1 • (mat g⁻¹ *ᵥ incV F x) := by
      rw [← Matrix.mulVec_smul, ← hl, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    calc mat g⁻¹ *ᵥ incV F x = ((l⁻¹ : (AE F E)ˣ).1 * l.1) • (mat g⁻¹ *ᵥ incV F x) := by simp
      _ = (l⁻¹ : (AE F E)ˣ).1 • incV F x := by rw [mul_smul, ← h2]

variable (σ) in

def IsoV {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Type := {w : Fin n → E // w ≠ 0 ∧ form σ J w w = 0}

def IsWitt {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (x : Fin n → E) (γ : IsoV σ J → UA σ J) : Prop :=
  ∀ w, γ w ∈ ratU σ J ∧ mat (γ w) *ᵥ incV F w.1 = incV F x

def termW (B : Base F E) {n n₁ d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (H : Plane E n n₁)
    (H' : Plane E d d₁) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (om : Rep σ X W) (Φ : Fn F n d) (γ : IsoV σ W.J → UA σ W.J)
    (w : IsoV σ W.J) (g : UA σ X.J) (h : UA σ W.J) : ℂ :=
  thetaSum F (e (M.co.rho B.ψ (shiftB σ H H' 1) (om (g, γ w * h) Φ)))

example {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) : (1 : UA σ J) ∈ ratStab σ J x := one_mem _

end GlobalTheory.ConeSmallUnf

end
