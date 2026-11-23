import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug

noncomputable section

open GlobalTheory.SplitWeil GlobalTheory.ThetaGLSub

namespace GlobalTheory.ThetaGLRank

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n m : ℕ}

variable (k n m) in

def rkSub (ρ : ℕ) : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ) where
  carrier := {Φ | Φ ∈ SB (Matrix (Fin n) (Fin m) k) ∧ ∀ x : Matrix (Fin n) (Fin m) k, x.rank < ρ → Φ x = 0}
  add_mem' := by
    rintro Φ Ψ ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨Submodule.add_mem _ h1 h3, fun x hx => by simp [h2 x hx, h4 x hx]⟩
  zero_mem' := ⟨Submodule.zero_mem _, fun _ _ => rfl⟩
  smul_mem' := by
    rintro c Φ ⟨h1, h2⟩
    exact ⟨Submodule.smul_mem _ c h1, fun x hx => by simp [h2 x hx]⟩

theorem rkSub_le_SB (ρ : ℕ) : rkSub k n m ρ ≤ SB (Matrix (Fin n) (Fin m) k) := fun _ h => h.1

theorem rkSub_zero : rkSub k n m 0 = SB (Matrix (Fin n) (Fin m) k) :=
  le_antisymm (rkSub_le_SB 0) fun _ h => ⟨h, fun _ hx => absurd hx (Nat.not_lt_zero _)⟩

theorem rkSub_succ_n : rkSub k n m (n + 1) = ⊥ := by
  refine eq_bot_iff.2 fun Φ h => ?_
  refine funext fun x => h.2 x ?_
  have : x.rank ≤ n := by simpa using Matrix.rank_le_height x
  omega

theorem rkSub_succ_le (ρ : ℕ) : rkSub k n m (ρ + 1) ≤ rkSub k n m ρ :=
  fun _ h => ⟨h.1, fun x hx => h.2 x (Nat.lt_succ_of_lt hx)⟩

theorem om_mem_rkSub (ρ : ℕ) (g : GL (Fin m) k) {Φ : Matrix (Fin n) (Fin m) k → ℂ}
    (h : Φ ∈ rkSub k n m ρ) : om 1 g (1 : GL (Fin n) k) Φ ∈ rkSub k n m ρ := by
  refine ⟨Model.om_mem_SB 1 g 1 h.1, fun x hx => ?_⟩
  have hr : ((1 : GL (Fin n) k)⁻¹.val * x * g.val).rank = x.rank := by
    simp only [inv_one, Units.val_one, Matrix.one_mul]
    exact Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units g)
  simp only [om]
  rw [h.2 _ (hr ▸ hx), mul_zero]

theorem isSub_aug_sup (χ : GL (Fin n) k →* ℂˣ) (ρ : ℕ) : IsSub χ (aug m χ ⊔ rkSub k n m ρ) := by
  refine ⟨le_sup_left, sup_le (aug_le_SB χ) (rkSub_le_SB ρ), fun g Φ hΦ => ?_⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hΦ
  rw [om_add]
  exact Submodule.add_mem_sup ((isSub_aug χ).2.2 g y hy) (om_mem_rkSub ρ g hz)

theorem IsSub.inf {χ : GL (Fin n) k →* ℂˣ} {N N' : Submodule ℂ (Matrix (Fin n) (Fin m) k → ℂ)} (h : IsSub χ N)
    (h' : IsSub χ N') : IsSub χ (N ⊓ N') :=
  ⟨le_inf h.1 h'.1, inf_le_left.trans h.2.1, fun g Φ hΦ => ⟨h.2.2 g Φ hΦ.1, h'.2.2 g Φ hΦ.2⟩⟩

end GlobalTheory.ThetaGLRank
