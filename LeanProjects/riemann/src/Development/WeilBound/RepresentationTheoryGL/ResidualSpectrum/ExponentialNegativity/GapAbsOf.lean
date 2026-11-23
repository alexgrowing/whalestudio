import Mathlib

noncomputable section

open Matrix Classical

namespace PositivityTheory.Rg.Rs

def e0 (k : Type) [Field k] (n : ℕ) : Fin (n + 1) → k := Pi.single 0 1

def H0 (k : Type) [Field k] (n : ℕ) : Submodule k (Fin (n + 1) → k) := LinearMap.ker (LinearMap.proj 0)

def gmap {k : Type} [Field k] {N : ℕ} (g : GL (Fin N) k) (M : Submodule k (Fin N → k)) : Submodule k (Fin N → k) :=
  M.map (Matrix.toLin' g.val)

structure LatData (k : Type) [Field k] (n : ℕ) {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (red : Γ →* GL (Fin (n + 1)) k) (ρ : Γ →* Module.End ℂ V) (t : Module.End ℂ V)
    (v : Submodule k (Fin (n + 1) → k) → V) : Prop where
  herm : ∀ x y, B y x = starRingEnd ℂ (B x y)
  pos : ∀ x, x ≠ 0 → 0 < (B x x).re
  surj : Function.Surjective red
  unit : ∀ γ x y, B (ρ γ x) (ρ γ y) = B x y
  isom : ∀ x y, B (t x) (t y) = B x y
  ne : v ⊤ ≠ 0
  equiv : ∀ γ M, ρ γ (v M) = v (gmap (red γ) M)
  fix : ∀ y, (∀ γ, gmap (red γ) (Submodule.span k {e0 k n}) = Submodule.span k {e0 k n} → ρ γ y = y) →
    ∀ γ, gmap (red γ) (H0 k n) = H0 k n → ρ γ (t y) = t y
  step : ∀ M, e0 k n ∈ M → t (v M) = v (M ⊓ H0 k n)

def LatEig (k : Type) [Field k] [Fintype k] (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (v : Submodule k (Fin (n + 1) → k) → V) (S : Multiset ℂ) : Prop :=
  S.card = n + 1 ∧ ∀ j ≤ n + 1, ∑ᶠ (M : Submodule k (Fin (n + 1) → k)) (_ : Module.finrank k M + j = n + 1), v M =
    ((Fintype.card k : ℂ) ^ (((j : ℂ) * (((n + 1 : ℕ) : ℂ) - j)) / 2) * S.esymm j) • v ⊤

def GapAbs : Prop := ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (V Γ : Type) [AddCommGroup V] [Module ℂ V] [Group Γ]
  (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (red : Γ →* GL (Fin (n + 1)) k) (ρ : Γ →* Module.End ℂ V) (t : Module.End ℂ V)
  (v : Submodule k (Fin (n + 1) → k) → V) (S : Multiset ℂ), LatData k n B red ρ t v → LatEig k n v S → 0 ∉ S →
  ∀ z : ℂ, ‖z‖ < (Fintype.card k : ℝ) ^ (-(1 / 2) : ℝ) → S.count z ≤ S.count ((Fintype.card k : ℂ) * z)

def GapOp : Prop := ∀ (k : Type) [Field k] [Fintype k] (n : ℕ) (V Γ : Type) [AddCommGroup V] [Module ℂ V] [Group Γ]
  (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (red : Γ →* GL (Fin (n + 1)) k) (ρ : Γ →* Module.End ℂ V) (t : Module.End ℂ V)
  (v : Submodule k (Fin (n + 1) → k) → V) (lam : ℕ → ℂ), LatData k n B red ρ t v →
  (∀ j ≤ n + 1, ∑ᶠ (M : Submodule k (Fin (n + 1) → k)) (_ : Module.finrank k M + j = n + 1), v M = lam j • v ⊤) →
  ∃ (W : Submodule ℂ V) (U : Module.End ℂ V) (Z : ℕ → V), (∀ y ∈ W, U y ∈ W) ∧ (∀ j, Z j ∈ W) ∧
    (∀ y ∈ W, (Fintype.card k : ℝ) ^ ((n : ℝ) - 1) * (B y y).re ≤ (B (U y) (U y)).re) ∧
    Z 0 = v ⊤ ∧ Z (n + 1) = 0 ∧
    (∀ j ≤ n, U (Z j) = (Fintype.card k : ℂ) ^ j • (lam (j + 1) • v ⊤ - Z (j + 1))) ∧
    ∀ j ≤ n + 1, ((Fintype.card k : ℂ) ^ (n + 1) - 1) * B (Z j) (v ⊤) =
      ((Fintype.card k : ℂ) ^ (n + 1 - j) - 1) * lam j * B (v ⊤) (v ⊤)

def GapPoly : Prop := ∀ (q n : ℕ), 2 ≤ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
  (W : Submodule ℂ V) (U : Module.End ℂ V) (Z : ℕ → V) (S : Multiset ℂ), (∀ x, x ≠ 0 → 0 < (B x x).re) →
  S.card = n + 1 → 0 ∉ S → Z 0 ≠ 0 → (∀ y ∈ W, U y ∈ W) → (∀ j, Z j ∈ W) →
  (∀ y ∈ W, (q : ℝ) ^ ((n : ℝ) - 1) * (B y y).re ≤ (B (U y) (U y)).re) → Z (n + 1) = 0 →
  (∀ j ≤ n, U (Z j) = (q : ℂ) ^ j •
    (((q : ℂ) ^ ((((j + 1 : ℕ) : ℂ) * (((n + 1 : ℕ) : ℂ) - ((j + 1 : ℕ) : ℂ))) / 2) * S.esymm (j + 1)) • Z 0 - Z (j + 1))) →
  (∀ j ≤ n + 1, ((q : ℂ) ^ (n + 1) - 1) * B (Z j) (Z 0) =
    ((q : ℂ) ^ (n + 1 - j) - 1) * ((q : ℂ) ^ (((j : ℂ) * (((n + 1 : ℕ) : ℂ) - j)) / 2) * S.esymm j) * B (Z 0) (Z 0)) →
  ∀ z : ℂ, ‖z‖ < (q : ℝ) ^ (-(1 / 2) : ℝ) → S.count z ≤ S.count ((q : ℂ) * z)

theorem gapAbs_of (h1 : GapOp) (h2 : GapPoly) : GapAbs := by
  intro k _ _ n V Γ _ _ _ B red ρ t v S hD hE h0 z hz
  obtain ⟨W, U, Z, a1, a2, a3, a4, a5, a6, a7⟩ := h1 k n V Γ B red ρ t v _ hD hE.2
  exact h2 (Fintype.card k) n Fintype.one_lt_card V B W U Z S hD.pos hE.1 h0 (a4 ▸ hD.ne) a1 a2 a3 a5
    (fun j hj => by rw [a4]; exact a6 j hj) (fun j hj => by rw [a4]; exact a7 j hj) z hz

end PositivityTheory.Rg.Rs

end
