import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect

section Abstract

variable {F Y : Type} [Field F] [AddCommGroup Y] [Module F Y] {c : ℕ}

def IsFrame (X : Submodule F Y) (a : Fin c → Y) : Prop :=
  LinearIndependent F a ∧ IsCompl X (Submodule.span F (Set.range a))

def flag (X : Submodule F Y) (a : Fin c → Y) (i : Fin c) : Submodule F Y :=
  X ⊔ Submodule.span F (a '' {l | l < i})

def IsUnip (X : Submodule F Y) (a : Fin c → Y) (n : Y ≃ₗ[F] Y) : Prop :=
  (∀ x ∈ X, n x = x) ∧ (∀ i : Fin c, i.1 = 0 → n (a i) = a i) ∧ ∀ i : Fin c, n (a i) - a i ∈ flag X a i

def IsExtOf (X : Submodule F Y) (a : Fin c → Y) (γ : X ≃ₗ[F] X) (g : Y ≃ₗ[F] Y) : Prop :=
  (∀ x : X, g x = (γ x : Y)) ∧ ∀ i, g (a i) = a i

def IsSemidirect (X : Submodule F Y) (a : Fin c → Y) (r : Y ≃ₗ[F] Y) : Prop :=
  ∃ (γ : X ≃ₗ[F] X) (g n : Y ≃ₗ[F] Y), IsExtOf X a γ g ∧ IsUnip X a n ∧ r = g * n

variable {O : Type} [CommRing O] [Algebra O F] [Module O Y] [IsScalarTower O F Y]

def moveBy (r : Y ≃ₗ[F] Y) (Λ : Submodule O Y) : Submodule O Y :=
  Λ.map (r.toLinearMap.restrictScalars O)

def normalForm (F : Type) [Field F] [Module F Y] [Algebra O F] (q : O) (M : Submodule O Y) (a : Fin c → Y)
    (e : Fin c → ℤ) (z : Y) : Submodule O Y :=
  M ⊔ ⨆ i : Fin c, Submodule.span O {(algebraMap O F q) ^ (e i) • (a i + if i.1 = 0 then z else 0)}

def inY (X : Submodule F Y) (L : Submodule O X) : Submodule O Y :=
  L.map (X.subtype.restrictScalars O)

end Abstract

def LatticeNormalForm : Prop :=
  ∀ (O F Y : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F] [IsFractionRing O F]
    [AddCommGroup Y] [Module F Y] [Module O Y] [IsScalarTower O F Y]
    (q : O), Irreducible q →
    ∀ (c : ℕ) (X : Submodule F Y) (a : Fin c → Y), IsFrame X a →
    ∀ (L : Submodule O X), Submodule.IsLattice F L →
    ∀ (Λ : Submodule O Y), Submodule.IsLattice F Λ →
      ∃ (r : Y ≃ₗ[F] Y) (e : Fin c → ℤ) (z : Y), IsSemidirect X a r ∧ z ∈ X ∧
        moveBy r Λ = normalForm F q (inY X L) a e z

def LatticeNormalFormUnip : Prop :=
  ∀ (O F Y : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F] [IsFractionRing O F]
    [AddCommGroup Y] [Module F Y] [Module O Y] [IsScalarTower O F Y]
    (q : O), Irreducible q →
    ∀ (c : ℕ) (X : Submodule F Y) (a : Fin c → Y), IsFrame X a →
    ∀ (Λ : Submodule O Y), Submodule.IsLattice F Λ →
      ∃ (n : Y ≃ₗ[F] Y) (e : Fin c → ℤ) (z : Y), IsUnip X a n ∧ z ∈ X ∧
        moveBy n Λ = normalForm F q (Λ ⊓ X.restrictScalars O) a e z

open Formalism.L2.Col in

def LatticeNormalFormCoord : Prop :=
  ∀ (O F : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F] [Algebra O F] [IsFractionRing O F]
    (q : O), Irreducible q →
    ∀ (n c : ℕ) (L : Submodule O (Fin n → F)), Submodule.IsLattice F L →
    ∀ (Λ : Submodule O (Fin (n + c) → F)), Submodule.IsLattice F Λ →
      ∃ r ∈ Loc.R1 F n c, ∃ (e : Fin c → ℤ) (z : Fin n → F),
        moveBy r Λ = normalForm F q (L.map ((Loc.inX F n c).restrictScalars O))
          (fun i : Fin c => Loc.eN F (n + c) (n + i.1)) e (Loc.inX F n c z)

section Basic₂

variable {F Y : Type} [Field F] [AddCommGroup Y] [Module F Y] {c : ℕ}

theorem isUnip_one (X : Submodule F Y) (a : Fin c → Y) : IsUnip X a 1 :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun i => by
    show a i - a i ∈ _
    rw [sub_self]
    exact zero_mem _⟩

example {O : Type} [CommRing O] [Algebra O F] [Module O Y] (q : O) (M : Submodule O Y) (a : Fin (c + 1) → Y)
    (e : Fin (c + 1) → ℤ) (z : Y) : (algebraMap O F q) ^ (e 0) • (a 0 + z) ∈ normalForm F q M a e z := by
  refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem 0 (Submodule.subset_span ?_))
  simp

example : IsFrame (F := ℚ) (LinearMap.range (LinearMap.inl ℚ ℚ ℚ)) (fun _ : Fin 1 => ((0, 1) : ℚ × ℚ)) := by
  refine ⟨by simp [linearIndependent_unique_iff], ?_⟩
  have h : Submodule.span ℚ (Set.range (fun _ : Fin 1 => ((0, 1) : ℚ × ℚ))) = LinearMap.range (LinearMap.inr ℚ ℚ ℚ) := by
    ext x
    simp only [Set.range_const, Submodule.mem_span_singleton, LinearMap.mem_range, LinearMap.coe_inr]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, by simp⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, by simp⟩
  rw [h]
  exact LinearMap.isCompl_range_inl_inr

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect
