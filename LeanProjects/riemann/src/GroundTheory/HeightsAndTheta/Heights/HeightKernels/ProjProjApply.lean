import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix NumberField

noncomputable section

variable {K : Type} [Field K] [NumberField K] {i : ℕ}

def projProj : (((k : Unit) → projBlocks K i k) → ℂ) →ₗ[ℂ] (Fin i → ℂ) where
  toFun s := ∑ σ : K →+* ℂ, embComp σ (fun q => s fun _ => q)
  map_add' s s' := by
    funext j
    simp only [Finset.sum_apply, Pi.add_apply, embComp, mul_add, Finset.sum_add_distrib]
  map_smul' c s := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, embComp, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun m _ => by ring

theorem projProj_apply (s : ((k : Unit) → projBlocks K i k) → ℂ) :
    projProj s = ∑ σ : K →+* ℂ, embComp σ (fun q => s fun _ => q) := rfl

def projPlanePt (σ : K →+* ℂ) (v : Fin i → ℂ) : (Σ _ : Unit, ProjIdx K i) → ℂ :=
  fun p => σ (integralBasis K p.2.1) * v p.2.2

def ProjPtsOnPlane.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ), ∀ z ∈ mcPts (projSpaceIdeal K i),
    ∃ σ : K →+* ℂ, ∀ τ : K →+* ℂ, τ ≠ σ → embComp τ (fun q => z ⟨(), q⟩) = 0

def ProjPtsOfPlane.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (σ : K →+* ℂ) (v : Fin i → ℂ),
    v ≠ 0 → projPlanePt σ v ∈ mcPts (projSpaceIdeal K i)

def ProjStdMassAt.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (D : ℕ) (F : HermLattice K (D + 1)),
    (∀ σ, F.metric σ = 1) →
    ptsIntegralAt (e := D) (projSpaceIdeal K (D + 1)) projProj
      (fun _ z => Real.log ((latticeLine F).h z)) (fun _ => 1) = Fintype.card (K →+* ℂ)

example : (((k : Unit) → projBlocks ℚ 1 k) → ℂ) →ₗ[ℂ] (Fin 1 → ℂ) := projProj

example : (Σ _ : Unit, ProjIdx ℚ 1) → ℂ := projPlanePt (Rat.castHom ℂ) fun _ => 1

example : ∃ (_ : ℚ →+* ℂ) (v : Fin 1 → ℂ), v ≠ 0 :=
  ⟨Rat.castHom ℂ, fun _ => 1, fun h => one_ne_zero (congrFun h 0)⟩

example : ∀ σ, (HermLattice.standard ℚ (0 + 1)).metric σ = 1 := fun _ => rfl

end

end GroundTheory.Heights₂.Heights
