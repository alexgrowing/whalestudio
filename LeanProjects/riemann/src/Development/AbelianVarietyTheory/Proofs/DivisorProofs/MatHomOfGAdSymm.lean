import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact

noncomputable section

namespace GlobalTheory.IwLine

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_eq_sigR (σ : E →ₐ[F] E) (z : AE F E) : cA σ z = sigR (AF F) σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem UG_eq_HR (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    GlobalTheory.WeilM.UG (cA σ) (incM F J) = HR (AF F) σ Jᵀ := by
  have hc : ∀ M : Matrix (Fin n) (Fin n) (AE F E), M.map (cA σ) = M.map (sigR (AF F) σ) := fun M => by
    ext i j; exact cA_eq_sigR σ _
  have hJ : JR (AF F) Jᵀ = (incM F J)ᵀ := rfl
  ext g
  change (g.1)ᵀ * incM F J * (g.1).map (cA σ) = incM F J ↔ cT (sigR (AF F) σ) g.1 * JR (AF F) Jᵀ * g.1 = JR (AF F) Jᵀ
  rw [hc, hJ, cT]
  constructor
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  · intro h
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def ofGAd : GAd σ Jᵀ ≃* UA σ J := MulEquiv.subgroupCongr (UG_eq_HR σ J).symm

theorem mat_ofGAd (g : GAd σ Jᵀ) : mat (ofGAd σ J g) = (matHom (AF F) σ Jᵀ g).1 := rfl

theorem matHom_ofGAd_symm (g : UA σ J) : (matHom (AF F) σ Jᵀ ((ofGAd σ J).symm g)).1 = mat g := rfl

def lineStab (x : Fin n → E) : Subgroup (UA σ J) where
  carrier := {g | ∃ a : (AE F E)ˣ, mat g *ᵥ incV F x = (a : AE F E) • incV F x}
  one_mem' := ⟨1, by simp [mat, Matrix.one_mulVec]⟩
  mul_mem' := by
    rintro g h ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨b * a, ?_⟩
    show (mat g * mat h) *ᵥ incV F x = _
    rw [← Matrix.mulVec_mulVec, hb, Matrix.mulVec_smul, ha, smul_smul, Units.val_mul]
  inv_mem' := by
    rintro g ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    have e : mat g⁻¹ *ᵥ (mat g *ᵥ incV F x) = incV F x := by
      rw [Matrix.mulVec_mulVec, GlobalTheory.StabHaar.mat_inv_mul, Matrix.one_mulVec]
    rw [ha, Matrix.mulVec_smul] at e
    calc mat g⁻¹ *ᵥ incV F x = ((a⁻¹ : (AE F E)ˣ) : AE F E) • ((a : AE F E) • mat g⁻¹ *ᵥ incV F x) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e]

theorem mem_lineStab {x : Fin n → E} {g : UA σ J} :
    g ∈ lineStab σ J x ↔ ∃ a : (AE F E)ˣ, mat g *ᵥ incV F x = (a : AE F E) • incV F x := Iff.rfl

end GlobalTheory.IwLine
