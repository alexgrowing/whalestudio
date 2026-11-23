import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
open scoped ComplexOrder

namespace GlobalTheory.Mem.Col2.ClassSumPos

theorem ipVal_pos {E K ι : Type} [Field E] [Field K] [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (σ : K →+* ℂ)
    (lam : ι → DomWeight n) (f : Fr emb σ n → ℂ) (hf : f ∈ ValC (Gr emb σ n) lam) (h0 : f ≠ 0) :
    0 < ipVal emb σ lam f f := by
  obtain ⟨P, -, rfl⟩ := hf
  have hP : P ≠ 0 := by
    rintro rfl
    exact h0 (map_zero _)
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = (1 : ι → Matrix (Fin n) (Fin n) ℂ) := by
    funext τ
    show (1 : Matrix (Fin n) (Fin n) ℂ)⁻¹ = 1
    exact inv_one
  have h1 := polOf_fnOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n) P
  rw [e] at h1
  unfold ipVal
  rw [ipFr_apply, h1, ← nfL_apply]
  exact ps_nfL_pos lam P hP

theorem ipVal_herm {E K ι : Type} [Field E] [Field K] [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (σ : K →+* ℂ)
    (lam : ι → DomWeight n) (φ ψ : Fr emb σ n → ℂ) :
    ipVal emb σ lam φ ψ = starRingEnd ℂ (ipVal emb σ lam ψ φ) := by
  unfold ipVal
  rw [ipFr_apply, ipFr_apply, ← nfL_apply, ← nfL_apply, starRingEnd_apply, ps_nfL_symm]

theorem classSum_pos_herm : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ [Fintype S.Cl], (∀ φ ∈ S.Fi emb σ lam, φ ≠ 0 → 0 < (∑ c : S.Cl, ((Nat.card (S.Stab c) : ℕ) : ℂ)⁻¹ * ipVal emb σ lam (φ c) (φ c)).re) ∧ ∀ φ ψ : Fr emb σ n → ℂ, ipVal emb σ lam φ ψ = starRingEnd ℂ (ipVal emb σ lam ψ φ) := by
  intro E K ι _ _ _ _ _ _ _ n S emb σ lam _ hS _
  refine ⟨fun φ hφ h0 => ?_, ipVal_herm emb σ lam⟩
  have hw : ∀ c : S.Cl, (0 : ℂ) < ((Nat.card (S.Stab c) : ℕ) : ℂ)⁻¹ := fun c => by
    haveI := hS.fin_stab c.1 (S.rep c)
    have hc : (0 : ℝ) < ((Nat.card (S.Stab c) : ℕ) : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
    have := Complex.zero_lt_real.2 hc
    simpa using this
  have hpos : (0 : ℂ) < ∑ c : S.Cl, ((Nat.card (S.Stab c) : ℕ) : ℂ)⁻¹ * ipVal emb σ lam (φ c) (φ c) := by
    obtain ⟨c0, hc0⟩ := Function.ne_iff.1 h0
    refine Finset.sum_pos' (fun c _ => ?_) ⟨c0, Finset.mem_univ _, mul_pos (hw c0) (ipVal_pos emb σ lam _ (hφ c0).1 hc0)⟩
    by_cases h : φ c = 0
    · rw [h, map_zero, mul_zero]
    · exact (mul_pos (hw c) (ipVal_pos emb σ lam _ (hφ c).1 h)).le
  exact (Complex.lt_def.1 hpos).1

end GlobalTheory.Mem.Col2.ClassSumPos
