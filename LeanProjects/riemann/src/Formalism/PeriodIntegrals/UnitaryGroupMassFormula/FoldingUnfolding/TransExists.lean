import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.FoldBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareSeriesSquareIntegrable

open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable

namespace PI.FoldDCUnfold.W

universe u

def TransExists : Prop :=
  ∀ (G : Type u) [Group G] (K H : Subgroup G), H ≤ K → ∃ E : Set G, IsRightTransversal K H E

def TransIndep : Prop :=
  ∀ (G : Type u) [Group G] (Γ H : Subgroup G) (T T' : Set G),
    IsRightTransversal Γ H T → IsRightTransversal Γ H T' →
    ∀ c ∈ Γ, ∀ f : G → ℝ≥0∞, (∀ s ∈ H, ∀ y : G, f (s * y) = f y) →
      ∑' η : T, f ((η : G) * c) = ∑' η : T', f (η : G)

def TransProd : Prop :=
  ∀ (G : Type u) [Group G] (Γ S H : Subgroup G) (E D : Set G), H ≤ S → S ≤ Γ →
    IsRightTransversal S H E → IsRightTransversal Γ S D →
    Function.Injective (fun p : E × D => (p.1 : G) * (p.2 : G)) ∧
      IsRightTransversal Γ H (Set.range (fun p : E × D => (p.1 : G) * (p.2 : G)))

def DCTrans : Prop :=
  ∀ (G : Type u) [Group G] (Γ S S' : Subgroup G), S ≤ Γ → S' ≤ Γ →
    ∀ (R : Set G), IsDoubleTransversal Γ S S' R →
    ∀ (E : G → Set G), (∀ r ∈ R, IsRightTransversal S (stab S S' r) (E r)) →
      Function.Injective (fun p : (Σ r : R, E (r : G)) => (p.1 : G)⁻¹ * (p.2 : G)) ∧
        IsRightTransversal Γ S'
          (Set.range (fun p : (Σ r : R, E (r : G)) => (p.1 : G)⁻¹ * (p.2 : G)))

end PI.FoldDCUnfold.W
