import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType

noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix Filter
open scoped Topology

namespace GlobalTheory.SmoothGlob

variable {n : ℕ}

def lieSet (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) := {X | inG ε X}

section Target

variable {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

def HasDRep (π : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)) (X : Matrix (Fin n) (Fin n) ℂ) (v w : E) : Prop :=
  Tendsto (fun t : ℝ => ((t : ℂ)⁻¹) • (π (NormedSpace.exp (t • X)) v - v)) (𝓝[≠] 0) (𝓝 w)

structure IsSmoothModRep (ε : Fin n → Bool) (p : ℕ → Seminorm ℂ E)
    (π dπ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)) : Prop where
  withSeminorms : WithSeminorms p
  map_one : π 1 = 1
  map_mul : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, π (a * b) = (π a).comp (π b)
  continuousOn : ∀ v : E, ContinuousOn (fun g => π g v) (UJset ε)
  hasDRep : ∀ X ∈ lieSet ε, ∀ v : E, HasDRep π X v (dπ X v)
  growth : ∀ i, ∃ (q : Seminorm ℂ E) (N : ℕ), Continuous q ∧
    ∀ g ∈ UJset ε, ∀ v : E, p i (π g v) ≤ (1 + hs g) ^ N * q v

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def sobNorm (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (w : H) : ℝ :=
  (S.map fun l => ‖l.foldr (dRep σ) w‖).sum

def IsGKMap (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (π dπ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)) (T : H →ₗ[ℂ] E) : Prop :=
  (∀ k ∈ Kset ε, ∀ v, IsKFin ε σ v → T (σ k v) = π k (T v)) ∧
    ∀ X ∈ lieSet ε, ∀ v, IsKFin ε σ v → T (dRep σ X v) = dπ X (T v)

def IsSmoothGMap (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (p : ℕ → Seminorm ℂ E)
    (π : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)) (T : H →ₗ[ℂ] E) : Prop :=
  (∀ g ∈ UJset ε, ∀ w, SmoothVec (lieSet ε) σ w → T (σ g w) = π g (T w)) ∧
    ∀ i, ∃ (S : List (List (Matrix (Fin n) (Fin n) ℂ))) (C : ℝ), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) ∧
      ∀ w, SmoothVec (lieSet ε) σ w → p i (T w) ≤ C * sobNorm σ S w

end Target

def stdOp (g : Matrix (Fin n) (Fin n) ℂ) : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' g)

@[simp] theorem stdOp_apply (g : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : stdOp g v = g *ᵥ v := rfl

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem hasDerivAt_exp_mulVec (X : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) *ᵥ v) (X *ᵥ v) 0 := by

  have hE := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at hE
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Fin n → ℂ) :=
    { toFun := fun M => M *ᵥ v
      map_add' := fun A B => Matrix.add_mulVec A B v
      map_smul' := fun c A => by simp [Matrix.smul_mulVec] }
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hE

theorem norm_mulVec_le (g : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    ‖g *ᵥ v‖ ≤ (1 + hs g) * (n * ‖v‖) := by
  have hs0 : 0 ≤ hs g := by
    change 0 ≤ ∑ a, ∑ b, ‖g a b‖ ^ 2
    positivity

  have hent : ∀ i j, ‖g i j‖ ≤ 1 + hs g := by
    intro i j
    have hsq : ‖g i j‖ ^ 2 ≤ hs g := by
      change ‖g i j‖ ^ 2 ≤ ∑ a, ∑ b, ‖g a b‖ ^ 2
      have hrow : ‖g i j‖ ^ 2 ≤ ∑ b, ‖g i b‖ ^ 2 :=
        Finset.single_le_sum (f := fun b => ‖g i b‖ ^ 2) (fun b _ => by positivity) (Finset.mem_univ j)
      exact hrow.trans (Finset.single_le_sum (f := fun a => ∑ b, ‖g a b‖ ^ 2)
        (fun a _ => by positivity) (Finset.mem_univ i))
    nlinarith [sq_nonneg (‖g i j‖ - 1), norm_nonneg (g i j)]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  change ‖∑ j, g i j * v j‖ ≤ _
  calc ‖∑ j, g i j * v j‖ ≤ ∑ j, ‖g i j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, (1 + hs g) * ‖v‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]
        exact mul_le_mul (hent i j) (norm_le_pi_norm v j) (norm_nonneg _) (by linarith)
    _ = (1 + hs g) * (n * ‖v‖) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end GlobalTheory.SmoothGlob

namespace GlobalTheory.Published

open GlobalTheory.SmoothGlob

def CasselmanWallach : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    ∀ (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E]
      (p : ℕ → Seminorm ℂ E) (π dπ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)), IsSmoothModRep ε p π dπ →
      ∀ T₀ : H →ₗ[ℂ] E, IsGKMap ε σ π dπ T₀ →
        ∃ T : H →ₗ[ℂ] E, (∀ v, IsKFin ε σ v → T v = T₀ v) ∧ IsSmoothGMap ε σ p π T ∧
          (∀ T' : H →ₗ[ℂ] E, (∀ v, IsKFin ε σ v → T' v = T₀ v) → IsSmoothGMap ε σ p π T' →
            ∀ w, SmoothVec (lieSet ε) σ w → T' w = T w) ∧
          IsClosed (T '' {w | SmoothVec (lieSet ε) σ w}) ∧
          ((∃ v, IsKFin ε σ v ∧ T₀ v ≠ 0) →
            ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) →
              ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, SmoothVec (lieSet ε) σ w → sobNorm σ S w ≤ q (T w))

end GlobalTheory.Published

end
