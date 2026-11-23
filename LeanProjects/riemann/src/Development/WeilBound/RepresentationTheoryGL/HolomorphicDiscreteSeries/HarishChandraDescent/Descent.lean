import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.KUnitB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep

noncomputable section

open Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

section

variable {n : ℕ} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

def qf (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (x : M) : ℝ :=
  ∑ a, ∑ b, ‖E a b x - (if a = b then (μ a : ℂ) else 0) • x‖ ^ 2

def KFin (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (x : M) : Prop :=
  ∃ F : Submodule ℂ M, FiniteDimensional ℂ F ∧ IsKStableSub ε E F ∧ x ∈ F

def IsWt (E : Fin n → Fin n → Module.End ℂ M) (ν : Fin n → ℝ) (x : M) : Prop := ∀ a, E a a x = (ν a : ℂ) • x

structure Good (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (ν : Fin n → ℝ) (κ : ℝ) (y : M) : Prop where
  ne : y ≠ 0
  fin : KFin ε E y
  wt : IsWt E ν y
  cas : casimirK ε E y = (κ : ℂ) • y

def Stab (E : Fin n → Fin n → Module.End ℂ M) (N : Submodule ℂ M) : Prop := ∀ a b, ∀ v ∈ N, E a b v ∈ N

def NoDown (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (L : Fin n → ℝ) (V : Submodule ℂ M) : Prop :=
  ∀ a b : Fin n, a < b → ε a ≠ ε b → ∀ w ∈ layer ε E V 1, IsKHWVec ε E (L - root a b) w → w = 0

end

def ForAlg (Q : ∀ {n : ℕ} (_ : Fin n → Bool) {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M],
    (Fin n → Fin n → Module.End ℂ M) → Prop) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (E : Fin n → Fin n → Module.End ℂ M), IsGlRep E → IsInfUnitary ε E → Q ε E

def SqId : Prop := ForAlg fun ε M _ _ E => ∀ x : M,
  (⟪casimirK ε E x, x⟫_ℂ).re = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), ‖E a b x‖ ^ 2 ∧
  (⟪casimirK ε E x, x⟫_ℂ).re - (⟪casimir E x, x⟫_ℂ).re = ∑ a, ∑ b ∈ univ.filter (fun b => ε b ≠ ε a), ‖E a b x‖ ^ 2 ∧
  (∀ y : M, ⟪casimir E x, y⟫_ℂ = ⟪x, casimir E y⟫_ℂ)

def Approx : Prop := ForAlg fun ε M _ _ E => ∀ c : ℝ, (∀ x : M, casimir E x = (c : ℂ) • x) →
  ∀ F : Submodule ℂ M, FiniteDimensional ℂ F → IsKStableSub ε E F → ∀ (η : M), ∀ f ∈ F, ∃ η' ∈ F,
    ‖η - η'‖ ≤ ‖η - f‖ ∧
      ∑ a, ∑ b, ‖E a b (η - η')‖ ^ 2 ≤ ‖(2 : ℂ) • casimirK ε E η - (c : ℂ) • η‖ * ‖η - f‖

def RootBd : Prop := ForAlg fun {n} ε M _ _ E => ∀ (Λ : Fin n → ℝ) (c : ℝ) (v : M), IsKHWVec ε E Λ v →
  casimir E v = (c : ℂ) • v → ∀ a b, a ≠ b → ‖E a b v‖ ^ 2 ≤ (|Λ a - Λ b| + |casValK ε Λ - c|) * ‖v‖ ^ 2

def MatBd : Prop := ForAlg fun {n} _ M _ _ E => ∀ (Λ : Fin n → ℝ) (A : ℝ) (v : M), IsWt E Λ v → 0 ≤ A →
  (∀ a b, a ≠ b → ‖E a b v‖ ≤ A * ‖v‖) → ∀ Y : Matrix (Fin n) (Fin n) ℂ,
    ‖actM E Y v - (∑ c, Y c c * (Λ c : ℂ)) • v‖ ≤ (∑ a, ∑ b, ‖Y a b‖) * A * ‖v‖

def Comp : Prop := ForAlg fun {n} ε M _ _ E => ∀ (μ : Fin n → ℝ) (S : ℝ) (x : M), x ≠ 0 → KFin ε E x →
  qf E μ x ≤ S * ‖x‖ ^ 2 → ∃ (y : M) (ν : Fin n → ℝ) (κ : ℝ), Good ε E ν κ y ∧ qf E μ y ≤ S * ‖y‖ ^ 2

def Parts : Prop := ForAlg fun {n} ε M _ _ E => ∀ (μ ν : Fin n → ℝ) (κ S : ℝ) (y : M), Good ε E ν κ y →
  qf E μ y ≤ S * ‖y‖ ^ 2 → nsq (ν - μ) ≤ S ∧ κ - nsq ν ≤ S ∧ κ * ‖y‖ ^ 2 - (⟪casimir E y, y⟫_ℂ).re ≤ S * ‖y‖ ^ 2

def Ascent : Prop := ForAlg fun {n} ε M _ _ E => ∀ (N : Submodule ℂ M), Stab E N → ∀ (μ ν : Fin n → ℝ) (κ S : ℝ), ∀ y ∈ N,
  Good ε E ν κ y → Antitone μ → nsq (ν - μ) ≤ S → κ - nsq ν ≤ S →
    ∃ y' ∈ N, ∃ L : Fin n → ℝ, y' ≠ 0 ∧ KFin ε E y' ∧ IsKHWVec ε E L y' ∧ casValK ε L = κ ∧ nsq (L - μ) ≤ 2 * S

def KIrrEx : Prop := ForAlg fun {n} ε M _ _ E => ∀ (N : Submodule ℂ M), Stab E N → ∀ (L : Fin n → ℝ), ∀ y ∈ N,
  y ≠ 0 → KFin ε E y → IsKHWVec ε E L y → ∃ V : Submodule ℂ M, V ≤ N ∧ IsKIrrHW ε E L V

def Drop : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (L : Fin n → ℝ) (a b : Fin n), a ≠ b →
  casValK ε (L - root a b) ≤ casValK ε L - 2 * (L a - L b) + 2 * n + 2

def Descent : Prop := ForAlg fun {n} ε M _ _ E => ∀ (N : Submodule ℂ M), Stab E N → ∀ (μ L : Fin n → ℝ) (R τ s : ℝ) (J : ℕ),
  (∀ y ∈ N, (casValK ε L - R) * ‖y‖ ^ 2 ≤ (⟪casimir E y, y⟫_ℂ).re) → (∀ a b, a < b → τ ≤ μ a - μ b) →
  (∀ a, |L a - μ a| ≤ s) → R < J * (2 * (τ - 2 * (s + J)) - 2 * n - 2) → ∀ y ∈ N, y ≠ 0 → KFin ε E y → IsKHWVec ε E L y →
    ∃ (L' : Fin n → ℝ) (V : Submodule ℂ M), (∀ a, |L' a - μ a| ≤ s + J) ∧ IsKIrrHW ε E L' V ∧ NoDown ε E L' V

def Markov : Prop := ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (u : Module.End ℂ M) (Z : Submodule ℂ M) (R : ℝ),
  u.IsSymmetric → 0 < R → (∀ z ∈ Z, u z ∈ Z) → (∀ z ∈ Z, 0 ≤ (⟪u z, z⟫_ℂ).re) → ∀ x ∈ Z,
    (⟪(x + ((R ^ 2)⁻¹ : ℝ) • u (u x)) - x, x + ((R ^ 2)⁻¹ : ℝ) • u (u x)⟫_ℂ).re ≤
      (⟪u (x + ((R ^ 2)⁻¹ : ℝ) • u (u x)), x + ((R ^ 2)⁻¹ : ℝ) • u (u x)⟫_ℂ).re / (2 * R)

def PosNeg : Prop := ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (a : H →L[ℂ] H),
  IsSelfAdjoint a → ∃ p m : H →L[ℂ] H, a = p - m ∧ m * p = 0 ∧ (∀ x, 0 ≤ (⟪p x, x⟫_ℂ).re) ∧ (∀ x, 0 ≤ (⟪m x, x⟫_ℂ).re) ∧
    ∀ S : H →L[ℂ] H, Commute a S → Commute p S ∧ Commute m S

def Inv : Prop := ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (D : Submodule ℂ H)
  (B : Module.End ℂ D) (ι : Type) (U : ι → H →L[ℂ] H), Dense (D : Set H) → B.IsSymmetric → (∀ x, ‖x‖ ≤ ‖B x‖) →
  (∀ i, ∃ j, ContinuousLinearMap.adjoint (U i) = U j) →
  (∀ i, ∀ x : D, ∃ y : D, (y : H) = U i x ∧ (B y : H) = U i (B x)) →
  (∀ T : H →L[ℂ] H, (∀ i, Commute T (U i)) → ∀ x : D, ∃ y : D, (y : H) = T x ∧ (B y : H) = T (B x)) →
    ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧ (∀ i, Commute T (U i)) ∧ ∀ x : D, T (B x) = x

end PositivityTheory.RgHe3
