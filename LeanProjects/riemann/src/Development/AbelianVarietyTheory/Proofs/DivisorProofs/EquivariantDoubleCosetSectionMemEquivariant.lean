import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPtHomApply
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TraceBlocks

def secMemLeftMul {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (g : H) : Module.End ℂ V ≃+ Module.End ℂ V where
  toFun f := ρ g * f
  invFun f := ρ g⁻¹ * f
  left_inv f := by
    simp only [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  right_inv f := by
    simp only [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  map_add' a b := mul_add _ a b

theorem secM_mem_eqvM : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (ι : H →* G) (ρ : Representation ℂ H V) (K' : Subgroup G) (x : G) (v : V),
    secM ι ρ K' x v ∈ eqvM ι ρ K' := by
  intro G H V _ _ _ _ ι ρ K' x v
  refine ⟨fun g y => ?_, fun k hk y => ?_⟩
  · change ((stabCard ι K' x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * (ι g * y) ∈ K' then ρ h else 0) v
      = ρ g (((stabCard ι K' x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K' then ρ h else 0) v)
    have hsum : (∑ᶠ h : H, if (ι h * x)⁻¹ * (ι g * y) ∈ K' then ρ h else 0)
        = ρ g * (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K' then ρ h else 0) := by
      rw [← finsum_comp_equiv (Equiv.mulLeft g)]
      have hpt : ∀ h' : H, (fun h : H => if (ι h * x)⁻¹ * (ι g * y) ∈ K' then ρ h else 0)
          ((Equiv.mulLeft g) h') = secMemLeftMul ρ g (if (ι h' * x)⁻¹ * y ∈ K' then ρ h' else 0) := by
        intro h'
        have he : (ι (g * h') * x)⁻¹ * (ι g * y) = (ι h' * x)⁻¹ * y := by
          rw [map_mul]; group
        simp only [Equiv.coe_mulLeft, he]
        change _ = ρ g * _
        split_ifs
        · exact map_mul ρ g h'
        · exact (mul_zero _).symm
      simp_rw [hpt]
      exact (AddEquiv.map_finsum (secMemLeftMul ρ g) _).symm
    rw [hsum, map_smul]
    rfl
  · change ((stabCard ι K' x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * (y * k) ∈ K' then ρ h else 0) v
      = ((stabCard ι K' x : ℂ))⁻¹ • (∑ᶠ h : H, if (ι h * x)⁻¹ * y ∈ K' then ρ h else 0) v
    have hc : ∀ h : H, ((ι h * x)⁻¹ * (y * k) ∈ K' ↔ (ι h * x)⁻¹ * y ∈ K') := by
      intro h
      rw [← mul_assoc]
      exact Subgroup.mul_mem_cancel_right K' hk
    simp_rw [hc]

end GlobalTheory.BCT.TraceBlocks
