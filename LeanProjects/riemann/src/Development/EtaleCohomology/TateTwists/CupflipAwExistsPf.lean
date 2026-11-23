import Development.EtaleCohomology.TateTwists.CupGradedCommOfFlip

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def cupflip_aw_cochain : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m),
    ∃ γ : Cochain ((chains R).obj E) K k, μ.IsAW hk α β γ

def cupflip_aw_leibniz : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k)
    (γ₁ γ₂ : Cochain ((chains R).obj E) K (k + 1)),
    μ.IsAW hk α β γ → μ.IsAW (by omega) (δ n (n + 1) α) β γ₁ → μ.IsAW (by omega) α (δ m (m + 1) β) γ₂ →
      δ k (k + 1) γ = γ₁ + n.negOnePow • γ₂

theorem ev_zero_cochain {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  simp [ev]

theorem isAW_zero_left {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ}
    (hk : n + m = k) (β : Cochain ((chains R).obj E) J m) : μ.IsAW hk 0 β 0 := by
  intro N w h U x
  simp [ev_zero_cochain]

theorem isAW_zero_right {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ}
    (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) : μ.IsAW hk α 0 0 := by
  intro N w h U x
  simp [ev_zero_cochain]

theorem cupflip_aw_exists_of (hc : cupflip_aw_cochain) (hl : cupflip_aw_leibniz) : cupflip_aw_exists := by
  intro R _ I J K μ E n m k hk α β
  obtain ⟨γ, hγ⟩ := hc R μ E hk α.1 β.1
  have hα : δ n (n + 1) α.1 = 0 := Cocycle.δ_eq_zero α (n + 1)
  have hβ : δ m (m + 1) β.1 = 0 := Cocycle.δ_eq_zero β (m + 1)
  have h1 : μ.IsAW (by omega) (δ n (n + 1) α.1) β.1 (0 : Cochain ((chains R).obj E) K (k + 1)) := by
    rw [hα]; exact isAW_zero_left μ _ β.1
  have h2 : μ.IsAW (by omega) α.1 (δ m (m + 1) β.1) (0 : Cochain ((chains R).obj E) K (k + 1)) := by
    rw [hβ]; exact isAW_zero_right μ _ α.1
  have hδ : δ k (k + 1) γ = 0 := by
    rw [hl R μ hk α.1 β.1 γ 0 0 hγ h1 h2]; simp
  exact ⟨Cocycle.mk γ (k + 1) rfl hδ, hγ⟩

end LateralTheory.EtaleFoundations
