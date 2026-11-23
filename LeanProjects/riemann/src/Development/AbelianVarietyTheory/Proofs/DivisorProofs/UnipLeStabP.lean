import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipEv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d d₁ : ℕ}

theorem mat_mul' {W : Spc F E d} (g h : UA σ W.J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one' {W : Spc F E d} : mat (1 : UA σ W.J) = 1 := rfl

theorem mat_inv_mul' {W : Spc F E d} (g : UA σ W.J) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul', inv_mul_cancel, mat_one']

variable (σ) in

def stabilizer₂ (W : Spc F E d) (H' : Plane E d d₁) : Subgroup (UA σ W.J) where
  carrier := {g | (∃ t : (AE F E)ˣ, mat g *ᵥ incV F H'.x = (t : AE F E) • incV F H'.x) ∧
    ∀ z, ∃ a : AE F E, mat g *ᵥ (incM F H'.ι *ᵥ z) = incM F H'.ι *ᵥ z + a • incV F H'.x}
  one_mem' := ⟨⟨1, by simp [mat_one']⟩, fun z => ⟨0, by simp [mat_one']⟩⟩
  mul_mem' := by
    rintro g h ⟨⟨s, hs⟩, hg⟩ ⟨⟨t, ht⟩, hh⟩
    refine ⟨⟨s * t, ?_⟩, fun z => ?_⟩
    · rw [mat_mul', ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_smul, hs, smul_smul, Units.val_mul, mul_comm]
    · obtain ⟨a, ha⟩ := hh z
      obtain ⟨b, hb⟩ := hg z
      refine ⟨b + a * s, ?_⟩
      rw [mat_mul', ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, hb, hs, smul_smul, add_smul, add_assoc]
  inv_mem' := by
    rintro g ⟨⟨s, hs⟩, hg⟩
    have key : ∀ v, mat g⁻¹ *ᵥ (mat g *ᵥ v) = v := fun v => by
      rw [Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]
    have hx : mat g⁻¹ *ᵥ incV F H'.x = ((s⁻¹ : (AE F E)ˣ) : AE F E) • incV F H'.x := by
      have := key (incV F H'.x)
      rw [hs, Matrix.mulVec_smul] at this
      calc mat g⁻¹ *ᵥ incV F H'.x
          = ((s⁻¹ : (AE F E)ˣ) : AE F E) • ((s : AE F E) • mat g⁻¹ *ᵥ incV F H'.x) := by
            rw [smul_smul, Units.inv_mul, one_smul]
        _ = _ := by rw [this]
    refine ⟨⟨s⁻¹, hx⟩, fun z => ?_⟩
    obtain ⟨a, ha⟩ := hg z
    refine ⟨-(a * ((s⁻¹ : (AE F E)ˣ) : AE F E)), ?_⟩
    have := key (incM F H'.ι *ᵥ z)
    rw [ha, Matrix.mulVec_add, Matrix.mulVec_smul, hx, smul_smul] at this
    rw [neg_smul, ← sub_eq_add_neg]
    exact eq_sub_of_add_eq this

theorem unip_le_stabP (W : Spc F E d) (H' : Plane E d d₁) : unip σ W H' ≤ stabilizer₂ σ W H' := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro u ⟨hx, hz⟩
  exact ⟨⟨1, by rw [hx, Units.val_one, one_smul]⟩, hz⟩

end GlobalTheory.UnipEv
