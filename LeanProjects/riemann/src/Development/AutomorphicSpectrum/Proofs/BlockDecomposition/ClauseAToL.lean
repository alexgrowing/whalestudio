import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColumnRecursion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowToColumnReduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardJPat

open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFinAL

open ReciprocityTheory.Ty.Fin.Lq

theorem lt_isPat (N : ℕ) : IsPat (fun i j : Fin N => i < j) :=
  ⟨fun i => lt_irrefl i, fun _ _ _ h h' => lt_trans h h'⟩

theorem colPat_isPat (N k : ℕ) : IsPat (colPat N k) :=
  ⟨fun i h => lt_irrefl i h.1, fun _ _ _ h h' => ⟨lt_trans h.1 h'.1, h'.2⟩⟩

theorem cutE_ne (K : Type) [Field K] [Fintype K] [DecidableEq K] {N k : ℕ} {i j : Fin N}
    (h : cutE K N k i j ≠ 0) : (j : ℕ) = i + 1 ∧ (j : ℕ) ≠ k := by
  by_contra hc
  exact h (by simp only [cutE]; rw [if_neg hc])

theorem cutE_lt (K : Type) [Field K] [Fintype K] [DecidableEq K] (N k : ℕ) :
    IsPatChar (fun i j : Fin N => i < j) (cutE K N k) := by
  refine ⟨fun i j h => ?_, fun i j l h h' => ?_⟩
  · have := (cutE_ne K h).1
    exact Fin.lt_def.2 (by omega)
  · by_contra hc
    have := (cutE_ne K hc).1
    have h1 := Fin.lt_def.1 h
    have h2 := Fin.lt_def.1 h'
    omega

theorem cutE_col (K : Type) [Field K] [Fintype K] [DecidableEq K] (N k : ℕ) :
    IsPatChar (colPat N k) (cutE K N k) := by
  refine ⟨fun i j h => ?_, fun i j l h h' => (cutE_lt K N k).2 i j l h.1 h'.1⟩
  exact ⟨(cutE_lt K N k).1 i j h, (cutE_ne K h).2⟩

theorem wh_nat {K : Type} [Field K] [Fintype K] [DecidableEq K] {N : ℕ} {Φ : Fin N → Fin N → Prop}
    (hΦ : IsPat Φ) {E : Fin N → Fin N → K} (hE : IsPatChar Φ E) (ψ₀ : AddChar K ℂ)
    (τ : FDRep ℂ (GL (Fin N) K)) : ∃ m : ℕ, wh Φ E ψ₀ τ.character = m :=
  (GlobalTheory.CompanionTheory.PatGrp.patGroup K (Fin N) Φ hΦ).2.2 E ψ₀ hE |>.2.2.2 τ τ.ρ

theorem exists_rec {K : Type} [Field K] [Fintype K] [DecidableEq K] (N : ℕ) (ψ₀ : AddChar K ℂ)
    (hψ : ψ₀ ≠ 1) (τ : FDRep ℂ (GL (Fin N) K)) :
    ∃ D n : ℕ → ℕ, (∀ i, wh (fun i j : Fin N => i < j) (cutE K N i) ψ₀ τ.character = D i) ∧
      (∀ k, wh (colPat N k) (cutE K N k) ψ₀ τ.character = n k) ∧
      ∀ k, k < N → (n k : ℝ) = D k + ((Fintype.card K : ℝ) - 1) *
        ∑ a ∈ Finset.range k, (n (k - 1 - a) : ℝ) := by
  choose D hD using fun i => wh_nat (lt_isPat N) (cutE_lt K N i) ψ₀ τ
  choose n hn using fun k => wh_nat (colPat_isPat N k) (cutE_col K N k) ψ₀ τ
  refine ⟨D, n, hD, hn, fun k hk => ?_⟩
  have hcl : ∀ x y, τ.character (x * y * x⁻¹) = τ.character y := fun x y => by
    simpa using FDRep.char_conj τ y x
  have h1 := GlobalTheory.CompanionTheory.TyFin.colRec K N k ψ₀ τ.character hψ hcl hk
  have h2 := (GlobalTheory.CompanionTheory.TyFinRow.rowToCol K N ψ₀ τ.character hψ hcl).1
  have h3 : ∑ a ∈ Finset.range k, wh (rowPat N k a) (rowE K N k a) ψ₀ τ.character =
      ∑ a ∈ Finset.range k, (n (k - 1 - a) : ℂ) :=
    Finset.sum_congr rfl fun a ha => by rw [h2 k a (Finset.mem_range.1 ha) hk, hn]
  rw [h3, hn, hD] at h1
  apply Complex.ofReal_injective
  push_cast
  exact h1

end GlobalTheory.CompanionTheory.TyFinAL
