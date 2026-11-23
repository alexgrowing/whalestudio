import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.AEConst

noncomputable section

open NumberField Matrix UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.SpectralGap

variable (L : Type) [Field L] [NumberField L] (N : ℕ)

def dg (π : 𝓞 L) (r : ℕ) : Matrix (Fin N) (Fin N) L := diagonal fun i => if (i : ℕ) < r then (π : L) else 1

def mt : Matrix.SpecialLinearGroup (Fin N) L →* Matrix (Fin N) (Fin N) L := Matrix.SpecialLinearGroup.coeMonoidHom

def mo : Matrix.SpecialLinearGroup (Fin N) (𝓞 L) →* Matrix (Fin N) (Fin N) L :=
  (mt L N).comp (Matrix.SpecialLinearGroup.map (algebraMap (𝓞 L) L))

def Kg (π : 𝓞 L) (r : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin N) L) where
  carrier := {g | ∃ γ, dg L N π r * mt L N g = mo L N γ * dg L N π r}
  one_mem' := ⟨1, by rw [map_one, map_one, mul_one, one_mul]⟩
  mul_mem' := by
    rintro g g' ⟨γ, h⟩ ⟨γ', h'⟩
    exact ⟨γ * γ', by rw [map_mul, map_mul, ← mul_assoc, h, mul_assoc, h', mul_assoc]⟩
  inv_mem' := by
    rintro g ⟨γ, h⟩
    refine ⟨γ⁻¹, ?_⟩
    have h1 : mo L N γ⁻¹ * mo L N γ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have h2 : mt L N g * mt L N g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    calc dg L N π r * mt L N g⁻¹ = mo L N γ⁻¹ * (mo L N γ * dg L N π r) * mt L N g⁻¹ := by
          rw [← mul_assoc, h1, one_mul]
      _ = _ := by rw [← h, mul_assoc, mul_assoc, h2, mul_one]

def jS : Matrix.SpecialLinearGroup (Fin N) L →* Sp L N :=
  MonoidHom.pi fun w : InfinitePlace L => Matrix.SpecialLinearGroup.map (n := Fin N) w.embedding

def Arith : Prop := ∀ (L : Type) [Field L] [NumberField L] (π : 𝓞 L), Prime π →
  25 ≤ Ideal.absNorm (Ideal.span {π}) → ∀ N : ℕ, 3 ≤ N → Tri (Kg L N π 0) (Kg L N π 1) (Kg L N π 2)

def Dens : Prop := ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ (π : 𝓞 L), Prime π → ∀ N : ℕ, 3 ≤ N →
  Dense (((Kg L N π 0 ⊔ Kg L N π 1).map (jS L N) : Subgroup (Sp L N)) : Set (Sp L N))

end PositivityTheory.KB.SpectralGap

end
