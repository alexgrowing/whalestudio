import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.LengthDet

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.lift :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (R : ℕ) (g : Module.End ℤ_[l] X), GenBy l R X →
      ∃ S : Matrix (Fin R) (Fin R) ℤ_[l], ∀ c : ℤ_[l], cokLen (c • g - 1) ≤ vl l (c • S - 1).det := by
  intro l _ X _ _ R g hgen
  obtain ⟨π, hπ⟩ := hgen
  choose s hs using fun j : Fin R => hπ (g (π (Pi.single j 1)))
  refine ⟨Matrix.of fun i j => s j i, fun c => ?_⟩
  have hcomm : ∀ v : Fin R → ℤ_[l], π (Matrix.mulVec (Matrix.of fun i j => s j i) v) = g (π v) := by
    have h : π ∘ₗ (Matrix.of fun i j => s j i).mulVecLin = g ∘ₗ π := by
      ext j
      simp [Matrix.mulVec_single_one]
      rw [← hs j]
      rfl
    intro v
    simpa using LinearMap.congr_fun h v
  set A : Matrix (Fin R) (Fin R) ℤ_[l] := c • (Matrix.of fun i j => s j i) - 1 with hA
  have hcommA : ∀ v, π (A.mulVecLin v) = (c • g - 1) (π v) := by
    intro v
    simp only [hA, Matrix.mulVecLin_apply, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, map_sub, map_smul, hcomm, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply]
  let φ : (Fin R → ℤ_[l]) →ₗ[ℤ_[l]] X ⧸ LinearMap.range (c • g - 1) :=
    (LinearMap.range (c • g - 1)).mkQ ∘ₗ π
  have hker : LinearMap.range A.mulVecLin ≤ LinearMap.ker φ := by
    rintro _ ⟨v, rfl⟩
    simp only [LinearMap.mem_ker, φ, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    rw [hcommA]
    exact LinearMap.mem_range_self _ _
  have hsurj : Function.Surjective ((LinearMap.range A.mulVecLin).liftQ φ hker) := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨v, rfl⟩ := hπ y
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  have hlen := Module.length_le_of_surjective _ hsurj
  have hdet := KStar.Selmer.length_cokernel_eq_addVal_det A
  unfold cokLen
  exact hlen.trans_eq hdet
