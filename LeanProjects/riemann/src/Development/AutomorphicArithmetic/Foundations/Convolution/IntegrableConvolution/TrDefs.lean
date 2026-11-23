import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

noncomputable section

open GroundTheory.Automorphic UpperTheory.ConvolutionTheory.C

namespace UpperTheory.ConvolutionTheory.L1

def MatImage : Prop :=
  ∀ (A W : Type) [Ring A] [Algebra ℂ A] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    (ρ : A →ₐ[ℂ] Module.End ℂ W) (B : Set (Module.End ℂ W)), (∀ a, ∀ b ∈ B, Commute (ρ a) b) →
    (∀ P : Submodule ℂ W, (∀ a, ∀ w ∈ P, ρ a w ∈ P) → (∀ b ∈ B, ∀ w ∈ P, b w ∈ P) → P = ⊥ ∨ P = ⊤) →
    ∃ d : ℕ, 0 < d ∧ Nonempty (ρ.range ≃ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)

def UnitsTrace : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (m d : ℕ)
    (r : Fin (m + 1) → (Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ W)), (∀ i j, i ≠ j → ∀ a b, Commute (r i a) (r j b)) →
    (∀ P : Submodule ℂ W, (∀ i a, ∀ w ∈ P, r i a w ∈ P) → P = ⊥ ∨ P = ⊤) →
    ∀ U : W ≃ₗ[ℂ] W, (∀ i a w, U (r (i + 1) a w) = r i a (U w)) →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (i₀ : Fin (m + 1)) (S : Module.End ℂ W), (∀ j, j ≠ i₀ → ∀ a, Commute S (r j a)) →
      LinearMap.trace ℂ W (S ∘ₗ (U : W →ₗ[ℂ] W)) = c * LinearMap.trace ℂ W S

def AlgTrace : Prop :=
  ∀ (W X : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (m : ℕ) (T : Fin (m + 1) → X → Module.End ℂ W),
    (∀ i j, i ≠ j → ∀ x y, Commute (T i x) (T j y)) →
    (∀ P : Submodule ℂ W, (∀ i x, ∀ w ∈ P, T i x w ∈ P) → P = ⊥ ∨ P = ⊤) →
    ∀ U : W ≃ₗ[ℂ] W, (∀ i x w, U (T (i + 1) x w) = T i x (U w)) →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (i₀ : Fin (m + 1)) (S : Module.End ℂ W), (∀ j, j ≠ i₀ → ∀ x, Commute S (T j x)) →
      LinearMap.trace ℂ W (S ∘ₗ (U : W →ₗ[ℂ] W)) = c * LinearMap.trace ℂ W S

structure Slots {Γ G H : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (π : UnitaryRep Γ H) (V : Submodule ℂ H) (m : ℕ) (ι : Fin (m + 1) → G →* Γ) (E : H →L[ℂ] H)
    (A : Fin (m + 1) → H →L[ℂ] H) (U : H ≃ₗᵢ[ℂ] H) : Prop where
  summand : IsSummandOf π ⊤ V
  ι_comm : ∀ i j, i ≠ j → ∀ g h, Commute (ι i g) (ι j h)
  rest : ∀ γ : Γ, ∃ (g : Fin (m + 1) → G) (γ' : Γ) (c : ℂ), γ = (List.ofFn fun i => ι i (g i)).prod * γ' ∧
    ∀ v ∈ V, E (π γ' (E v)) = c • E v
  E_sa : IsSelfAdjoint E
  E_idem : ∀ v, E (E v) = E v
  E_mem : ∀ v ∈ V, E v ∈ V
  E_ι : ∀ i g v, E (π (ι i g) v) = π (ι i g) (E v)
  A_pos : ∀ i, 0 ≤ A i
  A_mem : ∀ i, ∀ v ∈ V, A i v ∈ V
  A_E : ∀ i v, A i (E v) = E (A i v)
  A_A : ∀ i j v, A i (A j v) = A j (A i v)
  A_ι : ∀ i j, i ≠ j → ∀ g v, A i (π (ι j g) v) = π (ι j g) (A i v)
  U_mem : V.map (U : H →ₗ[ℂ] H) = V
  U_E : ∀ v, U (E v) = E (U v)
  U_A : ∀ i v, U (A (i + 1) v) = A i (U v)
  U_ι : ∀ i g v, U (π (ι (i + 1) g) v) = π (ι i g) (U v)

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {m : ℕ}

def prodEig (V : Submodule ℂ H) (E : H →L[ℂ] H) (A : Fin (m + 1) → H →L[ℂ] H) (x : ℝ) : Submodule ℂ H :=
  eigIn (eigIn V E 1) (List.ofFn A).prod x

def jointEig (V : Submodule ℂ H) (E : H →L[ℂ] H) (A : Fin (m + 1) → H →L[ℂ] H) (y : ℝ) : Submodule ℂ H :=
  ⨅ i, eigIn (eigIn V E 1) (A i) y
end

def PositionsEx : Prop := ∀ m : ℕ, ∃ π : UnitaryRep PUnit.{1} ℂ,
  Slots π ⊤ m (fun _ => (1 : PUnit.{1} →* PUnit.{1})) 1 (fun _ => 1) (LinearIsometryEquiv.refl ℂ ℂ)

def CutIrr : Prop :=
  ∀ (Γ G H : Type) [Group Γ] [TopologicalSpace Γ] [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep Γ H) (V : Submodule ℂ H) (m : ℕ) (ι : Fin (m + 1) → G →* Γ) (E : H →L[ℂ] H) (A : Fin (m + 1) → H →L[ℂ] H)
    (U : H ≃ₗᵢ[ℂ] H), Slots π V m ι E A U →
    IsClosed (eigIn V E 1 : Set H) ∧ (∀ i g, ∀ v ∈ eigIn V E 1, π (ι i g) v ∈ eigIn V E 1) ∧
      ∀ P ≤ eigIn V E 1, IsClosed (P : Set H) → (∀ i g, ∀ v ∈ P, π (ι i g) v ∈ P) → P = ⊥ ∨ P = eigIn V E 1

def JointNe : Prop :=
  ∀ (Γ G H : Type) [Group Γ] [TopologicalSpace Γ] [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep Γ H) (V : Submodule ℂ H) (m : ℕ) (ι : Fin (m + 1) → G →* Γ) (E : H →L[ℂ] H) (A : Fin (m + 1) → H →L[ℂ] H)
    (U : H ≃ₗᵢ[ℂ] H), Slots π V m ι E A U → ∀ (i : Fin (m + 1)) (y : ℝ), eigIn (eigIn V E 1) (A i) y ≠ ⊥ → jointEig V E A y ≠ ⊥

def JointEx : Prop :=
  ∀ (Γ G H : Type) [Group Γ] [TopologicalSpace Γ] [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep Γ H) (V : Submodule ℂ H) (m : ℕ) (ι : Fin (m + 1) → G →* Γ) (E : H →L[ℂ] H) (A : Fin (m + 1) → H →L[ℂ] H)
    (U : H ≃ₗᵢ[ℂ] H), Slots π V m ι E A U → IsCompactOperator ((List.ofFn A).prod ∘L prj (eigIn V E 1)) →
    (∀ x : ℝ, 0 < x → FiniteDimensional ℂ (prodEig V E A x)) ∧
      ((∃ i, ∃ v ∈ eigIn V E 1, A i v ≠ 0) → ∃ y : ℝ, 0 < y ∧ jointEig V E A y ≠ ⊥)

def DiagOnly : Prop :=
  ∀ (Γ G H : Type) [Group Γ] [TopologicalSpace Γ] [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep Γ H) (V : Submodule ℂ H) (m : ℕ) (ι : Fin (m + 1) → G →* Γ) (E : H →L[ℂ] H) (A : Fin (m + 1) → H →L[ℂ] H)
    (U : H ≃ₗᵢ[ℂ] H), Slots π V m ι E A U → ∀ y : ℝ, 0 < y → FiniteDimensional ℂ (prodEig V E A (y ^ (m + 1))) →
    jointEig V E A y ≤ prodEig V E A (y ^ (m + 1)) ∧
    ∀ (i₀ : Fin (m + 1)) (S : H →L[ℂ] H), (∀ j, j ≠ i₀ → ∀ v, S (A j v) = A j (S v)) →
      trOn (prodEig V E A (y ^ (m + 1))) (S ∘L (U : H →L[ℂ] H)) = trOn (jointEig V E A y) (S ∘L (U : H →L[ℂ] H))

def JointTrace : Prop :=
  ∀ (Γ G H : Type) [Group Γ] [TopologicalSpace Γ] [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep Γ H) (V : Submodule ℂ H) (m : ℕ) (ι : Fin (m + 1) → G →* Γ) (E : H →L[ℂ] H) (A : Fin (m + 1) → H →L[ℂ] H)
    (U : H ≃ₗᵢ[ℂ] H), Slots π V m ι E A U → ∀ y : ℝ, FiniteDimensional ℂ (jointEig V E A y) →
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (i₀ : Fin (m + 1)) (S : H →L[ℂ] H), (∀ j, j ≠ i₀ → ∀ v, S (A j v) = A j (S v)) →
      (∀ j, j ≠ i₀ → ∀ g v, S (π (ι j g) v) = π (ι j g) (S v)) →
      trOn (jointEig V E A y) (S ∘L (U : H →L[ℂ] H)) = c * trOn (jointEig V E A y) S

def TwTrace : Prop :=
  ∀ (Γ G H : Type) [Group Γ] [TopologicalSpace Γ] [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRep Γ H) (V : Submodule ℂ H) (m : ℕ) (ι : Fin (m + 1) → G →* Γ) (E : H →L[ℂ] H) (A : Fin (m + 1) → H →L[ℂ] H)
    (U : H ≃ₗᵢ[ℂ] H), Slots π V m ι E A U → ∀ y : ℝ, 0 < y → FiniteDimensional ℂ (prodEig V E A (y ^ (m + 1))) →
    ∃ c : ℂ, c ≠ 0 ∧
      trOn (prodEig V E A (y ^ (m + 1))) (U : H →L[ℂ] H) = c * Module.finrank ℂ (jointEig V E A y) ∧
      ∀ (i₀ : Fin (m + 1)) (S : H →L[ℂ] H), (∀ j, j ≠ i₀ → ∀ v, S (A j v) = A j (S v)) →
        (∀ j, j ≠ i₀ → ∀ g v, S (π (ι j g) v) = π (ι j g) (S v)) →
        trOn (prodEig V E A (y ^ (m + 1))) (S ∘L (U : H →L[ℂ] H)) = c * trOn (jointEig V E A y) S

end UpperTheory.ConvolutionTheory.L1
