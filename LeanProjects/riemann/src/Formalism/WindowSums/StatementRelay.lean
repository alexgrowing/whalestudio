import Formalism.WachModuleLifts.StatementW

noncomputable section

namespace Formalism.WindowSums

open Formalism.CL.W

def PM {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A] {B : Base p A} {η : ℕ}
    {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
    (W : WachMod B η D) (M : ℕ) : Set D :=
  {x | ∃ n ∈ W.N, x = B.π₀ ^ M • n}

def RelayExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra ℤ_[p] A] (B : Base p A) (η : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
    (W : WachMod B η D) (M : ℕ),
    Set.BijOn (fun x => x - W.φ x) (PM W M) (PM W M) →
    ∀ y : D, W.γ y - y ∈ PM W M →
      ∃ z ∈ PM W M, W.d1 y z = 0 ∧ ∀ z' ∈ PM W M, W.d1 y z' = 0 → z' = z

def RelayWD : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra ℤ_[p] A] (B : Base p A) (η : ℕ)
    (D : Type) [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
    (W : WachMod B η D) (M : ℕ),
    Set.BijOn (fun x => x - W.φ x) (PM W M) (PM W M) →
    (∀ x ∈ PM W M, W.γ x ∈ PM W M) →
    ∀ y y' z z' : D, y' - y ∈ PM W M → z ∈ PM W M → z' ∈ PM W M →
      W.d1 y z = 0 → W.d1 y' z' = 0 →
      ∃ x ∈ PM W M, y' - y = W.φ x - x ∧ z' - z = W.γ x - x

def RelayFun : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra ℤ_[p] A] (B : Base p A) (η : ℕ)
    (D D' : Type) [AddCommGroup D] [Module A D] [Module ℤ_[p] D] [IsScalarTower ℤ_[p] A D]
    [AddCommGroup D'] [Module A D'] [Module ℤ_[p] D'] [IsScalarTower ℤ_[p] A D']
    (W : WachMod B η D) (W' : WachMod B η D') (f : Hom W W') (M : ℕ),
    Set.BijOn (fun x => x - W'.φ x) (PM W' M) (PM W' M) →
    ∀ y z : D, z ∈ PM W M → W.d1 y z = 0 →
      f.f z ∈ PM W' M ∧ W'.d1 (f.f y) (f.f z) = 0 ∧
      ∀ z' ∈ PM W' M, W'.d1 (f.f y) z' = 0 → z' = f.f z

end Formalism.WindowSums
