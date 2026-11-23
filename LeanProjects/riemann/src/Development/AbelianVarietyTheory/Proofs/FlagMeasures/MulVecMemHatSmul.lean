import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.HermitianPerpSubgroup
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.ColumnDimensionRational

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped TensorProduct ENNReal Pointwise
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.ColCmp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

variable {n r k : ℕ}

def zPerp (σ : E →+* E) {m : ℕ} (Jb : Matrix (Fin m) (Fin m) E) (z : Fin m → E) :
    Submodule (𝓞 E) (Fin m → E) where
  carrier := {x | form σ Jb x z = 0}
  zero_mem' := by simp [form]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, form, Matrix.mulVec_add, dotProduct_add] at *
    rw [ha, hb, add_zero]
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, form] at *
    rw [Matrix.mulVec_smul, dotProduct_smul, ha, smul_zero]

def levelJoin (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E)
    (f : Matrix (Fin n) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin n → E)) (g₁ g₂ : ℕ)
    (w : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E))
    (ε : HeightOneSpectrum (𝓞 F) → Fin k → Fin n → E) : Subgroup (HA (Af F) σ J) :=
  (ParabolicSubgroups.Np (Af F) σ J P ⊓ ParabolicSubgroups.Kmax σ J Λ) ⊔
    (ParabolicSubgroups.Hp (Af F) σ J P f ⊓ ParabolicSubgroups.Kmax σ J Λ ⊓
      ⨅ p ∈ ParabolicSubgroups.Typed F g₁ g₂, ParabolicSubgroups.uniAt σ J Λ (w p).asIdeal (ε p)) ⊔
    FlagUnipotentStabilizers.Kprin σ J Λ (g₁ * g₂)

end GlobalTheory.ColCmp
