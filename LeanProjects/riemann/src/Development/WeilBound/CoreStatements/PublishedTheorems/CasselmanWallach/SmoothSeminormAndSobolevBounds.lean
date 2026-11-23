import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open ReciprocityTheory.ChartRestriction.DS (actM casimirK IsGlRep IsInfUnitary IsKHWVec IsKStableSub)
open scoped InnerProductSpace

namespace PositivityTheory.CW

variable {n : ℕ}

section Abs

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def LocFin (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) : Prop :=
  ∀ v : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ v ∈ S ∧ IsKStableSub ε E S

end Abs

section Rep

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def KDer (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) (E : Fin n → Fin n → Module.End ℂ (kfin ε σ)) : Prop :=
  ∀ X ∈ lieSet ε, ∀ v : kfin ε σ, ((actM E X v : kfin ε σ) : H) = dRep σ X v

def Dens (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) : Prop :=
  (∀ v, IsKFin ε σ v → Sm ε σ v) ∧ (∀ v, IsKFin ε σ v → ∀ X ∈ lieSet ε, IsKFin ε σ (dRep σ X v)) ∧
    ∀ w, Sm ε σ w → ∀ S, Words (lieSet ε) S → ∀ δ : ℝ, 0 < δ → ∃ v, IsKFin ε σ v ∧ sobNorm σ S (w - v) < δ

def SobDiff (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) : Prop :=
  ∀ l : List (Mx n), (∀ X ∈ l, X ∈ lieSet ε) → ∀ w, Sm ε σ w → ∀ X ∈ lieSet ε,
    HasDerivAt (fun t : ℝ => Dw σ l (σ (NormedSpace.exp (t • X)) w)) (Dw σ l (dRep σ X w)) 0

def CoreH (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) : Prop :=
  ∀ N : ℕ, ∃ (S : List (List (Mx n))) (C : ℝ) (I₀ : Finset H), Words (lieSet ε) S ∧ 0 ≤ C ∧
    (∀ e ∈ I₀, IsKFin ε σ e) ∧ ∀ F : H →ₗ[ℂ] (Mx n → ℂ), (∀ v, IsKFin ε σ v → ContinuousOn (F v) (UJset ε)) →
      (∀ X ∈ lieSet ε, ∀ v, IsKFin ε σ v → ∀ g ∈ UJset ε,
        HasDerivAt (fun t : ℝ => F v (g * NormedSpace.exp (t • X))) (F (dRep σ X v) g) 0) →
      (∀ v, IsKFin ε σ v → ∃ C : ℝ, ∀ g ∈ UJset ε, ‖F v g‖ ≤ C * (1 + hs g) ^ N) →
      ∀ B : ℝ, 0 ≤ B → (∀ e ∈ I₀, ∀ g ∈ UJset ε, ‖F e g‖ ≤ B * (1 + hs g) ^ N) →
        ∀ v, IsKFin ε σ v → ‖F v 1‖ ≤ C * B * sobNorm σ S v

def KInv (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) (B : kfin ε σ →ₗ⋆[ℂ] kfin ε σ →ₗ[ℂ] ℂ) : Prop :=
  ∀ k ∈ Kset ε, ∀ v y v' y' : kfin ε σ, (v' : H) = σ k v → (y' : H) = σ k y → B v' y' = B v y

variable {E : Type} [AddCommGroup E] [Module ℂ E]

def SobBdOn (ε : Fin n → Bool) (σ : Mx n → (H →L[ℂ] H)) (P : H → Prop) (p : ℕ → Seminorm ℂ E) (T : H →ₗ[ℂ] E) : Prop :=
  ∀ i, ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ ∀ w, P w → p i (T w) ≤ C * sobNorm σ S w

end Rep

def AllIrr (P : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H],
    (Mx n → (H →L[ℂ] H)) → Prop) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → P n ε H σ

def AllTgt (P : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (_ : Mx n → (H →L[ℂ] H)) (E : Type) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (_ : ℕ → Seminorm ℂ E)
    (_ _ : Mx n → (E →L[ℂ] E)), Prop) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    ∀ (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E]
      (p : ℕ → Seminorm ℂ E) (π dπ : Mx n → (E →L[ℂ] E)), IsSmoothModRep ε p π dπ → P n ε H σ E p π dπ

def AllMod (P : ∀ (n : ℕ) (_ : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V],
    (Fin n → Fin n → Module.End ℂ V) → Prop) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V), IsGlRep E → IsInfUnitary ε E → P n ε V E

def C1 : Prop := AllIrr fun n ε _ _ _ σ => ∃ E : Fin n → Fin n → Module.End ℂ (kfin ε σ), KDer ε σ E ∧ IsGlRep E ∧
  IsInfUnitary ε E ∧ ∀ N : Submodule ℂ (kfin ε σ), (∀ a b, ∀ v ∈ N, E a b v ∈ N) → N = ⊥ ∨ N = ⊤

def CardSubmodulesOfIndexLePow : Prop := AllIrr fun _ ε _ _ _ σ => ∀ E, KDer ε σ E → LocFin ε E

def CardSubmodulesAndLinearEquivBounds : Prop := AllMod fun _ ε _ _ _ E => LocFin ε E → Submodule.span ℂ {v | ∃ μ : ℝ, Eig ε E μ v} = ⊤

def HighestWeightSpaceFinite : Prop := AllIrr fun n ε _ _ _ σ => ∀ E, KDer ε σ E → ∀ μ : Fin n → ℝ,
  FiniteDimensional ℂ (Submodule.span ℂ {v : kfin ε σ | IsKHWVec ε E μ v})

def HighestWeightIntegral : Prop := AllIrr fun n ε _ _ _ σ => ∀ E, KDer ε σ E → ∀ (v : kfin ε σ) (a : Fin n) (x : ℝ), v ≠ 0 →
  E a a v = (x : ℂ) • v → ∃ z : ℤ, x = z

def KStableHighestWeightVector : Prop := AllMod fun n ε V _ _ E => ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → IsKStableSub ε E S → S ≠ ⊥ →
  ∃ (w : V) (μ : Fin n → ℝ), w ∈ S ∧ w ≠ 0 ∧ IsKHWVec ε E μ w

def KTypesBoundedFinite : Prop := AllMod fun n ε V _ _ E => LocFin ε E →
  (∀ μ : Fin n → ℝ, FiniteDimensional ℂ (Submodule.span ℂ {v : V | IsKHWVec ε E μ v})) →
  (∀ (v : V) (a : Fin n) (x : ℝ), v ≠ 0 → E a a v = (x : ℂ) • v → ∃ z : ℤ, x = z) →
  ∀ R : ℝ, FiniteDimensional ℂ (Submodule.span ℂ {v | ∃ μ : ℝ, μ ≤ R ∧ Eig ε E μ v})

def C4 : Prop := AllIrr fun n ε H _ _ σ => Dens ε σ → ∀ E, KDer ε σ E → ∀ m : ℕ,
  ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧
    ∀ v : kfin ε σ, ‖((1 + casimirK ε E) ^ m) v‖ ≤ C * sobNorm σ S (v : H)

def C5 : Prop := AllIrr fun _ ε _ _ _ σ => Dens ε σ

def C6 : Prop := AllIrr fun _ ε _ _ _ σ => SobDiff ε σ

def C7 : Prop := MaxPr → C4 → AllIrr fun _ ε _ _ _ σ => Dens ε σ → ∀ E, KDer ε σ E → Mod ε E → CoreH ε σ

def D0 : Prop := AllTgt fun _ ε H _ _ σ E _ _ _ p _ _ => Dens ε σ → ∀ T : H →ₗ[ℂ] E, SobBdOn ε σ (Sm ε σ) p T →
  (∀ v, IsKFin ε σ v → T v = 0) → ∀ w, Sm ε σ w → T w = 0

def D1 : Prop := AllTgt fun _ ε H _ _ σ E _ _ _ p π dπ => CoreH ε σ → ∀ T₀ : H →ₗ[ℂ] E, IsGKMap ε σ π dπ T₀ →
  SobBdOn ε σ (IsKFin ε σ) p T₀

def D2 : Prop := AllTgt fun _ ε H _ _ σ E _ _ _ p _ _ => Dens ε σ → ∀ T₀ : H →ₗ[ℂ] E, SobBdOn ε σ (IsKFin ε σ) p T₀ →
  ∃ T : H →ₗ[ℂ] E, (∀ v, IsKFin ε σ v → T v = T₀ v) ∧ SobBdOn ε σ (Sm ε σ) p T

def D3 : Prop := D0 → AllTgt fun _ ε H _ _ σ E _ _ _ p π dπ => Dens ε σ → ∀ T : H →ₗ[ℂ] E, IsGKMap ε σ π dπ T →
  SobBdOn ε σ (Sm ε σ) p T → ∀ w, Sm ε σ w →
    (∀ k ∈ Kset ε, T (σ k w) = π k (T w)) ∧ ∀ X ∈ lieSet ε, T (dRep σ X w) = dπ X (T w)

def D4 : Prop := AllTgt fun _ ε H _ _ σ E _ _ _ p π dπ => SobDiff ε σ → ∀ T : H →ₗ[ℂ] E, SobBdOn ε σ (Sm ε σ) p T →
  ∀ X ∈ lieSet ε, (∀ w, Sm ε σ w → T (dRep σ X w) = dπ X (T w)) →
    ∀ w, Sm ε σ w → T (σ (NormedSpace.exp X) w) = π (NormedSpace.exp X) (T w)

def D5 : Prop := ∀ (n : ℕ) (ε : Fin n → Bool), ∀ g ∈ UJset ε, ∃ k ∈ Kset ε, ∃ X ∈ lieSet ε, g = k * NormedSpace.exp X

def SmoothSeminormGrowth : Prop := AllTgt fun _ ε _ _ _ _ E _ _ _ p π _ => ∀ i, ∃ (Q : Seminorm ℂ E) (N : ℕ), Continuous Q ∧
  (∀ g ∈ UJset ε, ∀ x, p i (π g x) ≤ (1 + hs g) ^ N * Q x) ∧
  (∀ g ∈ UJset ε, ∀ x, Q (π g x) ≤ (1 + hs g) ^ N * Q x) ∧ ∀ k ∈ Kset ε, ∀ x, Q (π k x) = Q x

def faceMap_comp_succAbove_castSucc : Prop := AllTgt fun _ ε H _ _ σ E _ _ _ p π _ => ∀ T : H →ₗ[ℂ] E, IsSmoothGMap ε σ p π T →
  ∀ i w₀, Sm ε σ w₀ → p i (T w₀) ≠ 0 → ∀ u, Sm ε σ u → u ≠ 0 → ∃ g ∈ UJset ε, p i (π g (T u)) ≠ 0

def E2a : Prop := AllIrr fun _ ε _ _ _ σ => Dens ε σ → ∀ E, KDer ε σ E → ∀ B, KInv ε σ B →
  ∀ v y, B (casimirK ε E v) y = B v (casimirK ε E y)

def E2b : Prop := AllIrr fun _ ε H _ _ σ => ∀ (Q : Seminorm ℂ (kfin ε σ)),
  (∀ k ∈ Kset ε, ∀ v v' : kfin ε σ, (v' : H) = σ k v → Q v' = Q v) → ∀ v₀, Q v₀ ≠ 0 →
    ∃ B, KInv ε σ B ∧ (∀ v y, ‖B v y‖ ≤ Q v * Q y) ∧ B v₀ v₀ ≠ 0

def CasimirPairingBound : Prop := AllMod fun _ ε V _ _ E => Mod ε E → ∀ Q : Seminorm ℂ V,
  (∀ v₀ : V, v₀ ≠ 0 → ∃ B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ, (∀ v y, B (casimirK ε E v) y = B v (casimirK ε E y)) ∧
    (∀ v y, ‖B v y‖ ≤ Q v * Q y) ∧ B v₀ v₀ ≠ 0) →
  ∀ η : V, ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖⟪η, y⟫_ℂ‖ ≤ C * Q y

def SobolevBoundedPairing : Prop := AllTgt fun _ ε H _ _ σ E _ _ _ p _ _ => Dens ε σ → ∀ T : H →ₗ[ℂ] E, SobBdOn ε σ (Sm ε σ) p T →
  ∀ Q : Seminorm ℂ E, Continuous Q → ∀ (l : List _) (η : H) (C : ℝ), (∀ X ∈ l, X ∈ lieSet ε) →
    ((∀ y, IsKFin ε σ y → ‖⟪η, y⟫_ℂ‖ ≤ C * Q (T y)) → ∀ y, Sm ε σ y → ‖⟪η, y⟫_ℂ‖ ≤ C * Q (T y)) ∧
    ((∀ y, IsKFin ε σ y → ‖Dw σ l y‖ ≤ Q (T y)) → ∀ y, Sm ε σ y → ‖Dw σ l y‖ ≤ Q (T y))

def CasimirPowerSurjectiveSymmetric : Prop := AllMod fun _ ε V _ _ E => Mod ε E → ∀ m : ℕ,
  Function.Surjective ((1 + casimirK ε E) ^ m : Module.End ℂ V) ∧
    ∀ x y : V, ⟪((1 + casimirK ε E) ^ m) x, y⟫_ℂ = ⟪x, ((1 + casimirK ε E) ^ m) y⟫_ℂ

def faceMap_castSucc_comp_eq_succ : Prop := AllTgt fun _ ε H _ _ σ E _ _ _ _ _ dπ => ∀ A, KDer ε σ A → ∀ T : H →ₗ[ℂ] E,
  (∀ X ∈ lieSet ε, ∀ v, IsKFin ε σ v → T (dRep σ X v) = dπ X (T v)) → ∀ m : ℕ,
    ∃ D : E →L[ℂ] E, ∀ v : kfin ε σ, T (((1 + casimirK ε A) ^ m) v : kfin ε σ) = D (T v)

def SmoothMapSeminormBound : Prop := MaxPr → CasimirPowerSurjectiveSymmetric → faceMap_castSucc_comp_eq_succ → AllTgt fun _ ε H _ _ σ E _ _ _ p π dπ => Dens ε σ → ∀ A, KDer ε σ A → Mod ε A →
  ∀ T : H →ₗ[ℂ] E, IsSmoothGMap ε σ p π T → (∀ X ∈ lieSet ε, ∀ v, IsKFin ε σ v → T (dRep σ X v) = dπ X (T v)) →
  ∀ (Q : Seminorm ℂ E) (N : ℕ), Continuous Q → (∀ g ∈ UJset ε, ∀ x, Q (π g x) ≤ (1 + hs g) ^ N * Q x) →
    (∀ η, IsKFin ε σ η → ∃ C : ℝ, 0 ≤ C ∧ ∀ y, Sm ε σ y → ‖⟪η, y⟫_ℂ‖ ≤ C * Q (T y)) →
    ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ v, IsKFin ε σ v → ‖v‖ ≤ q (T v)

def SobolevNormDomination : Prop := SobolevBoundedPairing → AllTgt fun n ε H _ _ σ E _ _ _ p _ dπ => Dens ε σ → ∀ T : H →ₗ[ℂ] E, SobBdOn ε σ (Sm ε σ) p T →
  (∀ X ∈ lieSet ε, ∀ v, IsKFin ε σ v → T (dRep σ X v) = dπ X (T v)) →
  ∀ q : Seminorm ℂ E, Continuous q → (∀ v, IsKFin ε σ v → ‖v‖ ≤ q (T v)) →
    ∀ S : List (List (Mx n)), Words (lieSet ε) S →
      ∃ q' : Seminorm ℂ E, Continuous q' ∧ ∀ w, Sm ε σ w → sobNorm σ S w ≤ q' (T w)

end PositivityTheory.CW

end
