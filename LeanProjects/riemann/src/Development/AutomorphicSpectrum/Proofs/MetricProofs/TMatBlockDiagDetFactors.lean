import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetMemSubring
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm

variable {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω]

theorem tMat_blockEquiv (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) (a b : Fin q ⊕ Fin p) :
    tMat Ts τ (blockEquiv p q a) (blockEquiv p q b) =
      (Matrix.fromBlocks (Ts (.inr τ)) 0 0 (Ts (.inl τ)) : Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) Ω) a b := by
  simp [tMat]
  rfl

theorem omBlock_tMat (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    omBlock (tMat Ts τ) = Ts (.inr τ) := by
  ext a b
  exact tMat_blockEquiv Ts τ (.inl a) (.inl b)

theorem wBlock_tMat (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    wBlock (tMat Ts τ) = Ts (.inl τ) := by
  ext a b
  exact tMat_blockEquiv Ts τ (.inr a) (.inr b)

theorem isBlockDiag_tMat (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    IsBlockDiag p (tMat Ts τ) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := (blockEquiv p q).surjective a
  obtain ⟨b, rfl⟩ := (blockEquiv p q).surjective b
  rw [tMat_blockEquiv]
  rcases a with a | a <;> rcases b with b | b
  · exact absurd (by
      have h1 := a.2
      have h2 := b.2
      show ((a : ℕ) < p + q - p ↔ (b : ℕ) < p + q - p)
      omega) hab
  · rfl
  · rfl
  · exact absurd (by
      show (q + (a : ℕ) < p + q - p ↔ q + (b : ℕ) < p + q - p)
      omega) hab

theorem tMat_main {Ψ : Type} {p q : ℕ} {Ω : Type} [Field Ω]
    (Ts : ∀ s, Matrix (Fin (rk Ψ p q s)) (Fin (rk Ψ p q s)) Ω) (τ : Ψ) :
    IsBlockDiag p (tMat Ts τ) ∧ (tMat Ts τ).det = (Ts (.inr τ)).det * (Ts (.inl τ)).det ∧
      ∀ i : Fin (p + q), detFac p i (tMat Ts τ) =
        (if p ≤ (i : ℕ) + 1 then (Ts (.inl τ)).det else 1) * (if (i : ℕ) + 1 = p + q then (Ts (.inr τ)).det else 1) := by
  refine ⟨isBlockDiag_tMat Ts τ, ?_, fun i => ?_⟩
  · have h := (isBlockDiag_tMat Ts τ).det_eq_blocks
    rw [omBlock_tMat, wBlock_tMat] at h
    exact h
  · have h1 : minorIJ (tMat Ts τ) (wIdx (p + q) p) (wIdx (p + q) p) = (Ts (.inl τ)).det := by
      rw [minorIJ_wIdx, wBlock_tMat]
      rfl
    have h2 : minorIJ (tMat Ts τ) (omIdx (p + q) p) (omIdx (p + q) p) = (Ts (.inr τ)).det := by
      rw [minorIJ_omIdx, omBlock_tMat]
      rfl
    rw [detFac, h1, h2]

end GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
