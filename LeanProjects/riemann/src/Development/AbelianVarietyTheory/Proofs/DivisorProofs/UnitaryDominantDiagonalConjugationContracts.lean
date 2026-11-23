import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
open Formalism.UG GlobalTheory.SatakeWeyl

noncomputable section

namespace GlobalTheory.SatakeWeyl.ContractProof

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {r : ℕ}

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_inv_diag {ϖ : L} (h0 : ϖ ≠ 0) (c : Fin r → ℤ) (s : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) :
    mat s⁻¹ = Matrix.diagonal (fun i => ϖ ^ (-c i)) := by
  have h1 : mat s * Matrix.diagonal (fun i => ϖ ^ (-c i)) = 1 := by
    rw [hs, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ h0]; simp
  calc mat s⁻¹ = mat s⁻¹ * (mat s * Matrix.diagonal (fun i => ϖ ^ (-c i))) := by rw [h1, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_conj {ϖ : L} (h0 : ϖ ≠ 0) (c : Fin r → ℤ) (s g : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (i l : Fin r) :
    mat (s * g * s⁻¹) i l = ϖ ^ (c i - c l) * mat g i l := by
  rw [mat_mul, mat_mul, mat_inv_diag h0 c s hs, hs, Matrix.mul_diagonal, Matrix.diagonal_mul, sub_eq_add_neg,
    zpow_add₀ h0]
  ring

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_pow_diag {ϖ : L} (h0 : ϖ ≠ 0) (c : Fin r → ℤ) (s : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (j : ℕ) :
    mat (s ^ j) = Matrix.diagonal (fun i => ϖ ^ ((j : ℤ) * c i)) := by
  induction j with
  | zero => simp [mat_one]
  | succ j ih =>
    rw [pow_succ, mat_mul, ih, hs, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← zpow_add₀ h0]; congr 1; push_cast; ring

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem conj_mem_root {ϖ : L} (h0 : ϖ ≠ 0) (γ : Fin r → ℕ) (c : Fin r → ℤ) (s g : GU σ r)
    (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (hg : g ∈ rootU σ γ) : s * g * s⁻¹ ∈ rootU σ γ := by
  refine ⟨fun i l h => ?_, fun i l h => ?_⟩
  · rw [mat_conj h0 c s g hs, hg.1 i l h]
    by_cases e : i = l
    · subst e; simp
    · rw [Matrix.one_apply_ne e, mul_zero]
  · rw [mat_conj h0 c s g hs, hg.2 i l h, mul_zero]

theorem conj_mem_K {ϖ : L} (h0 : ϖ ≠ 0) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (γ : Fin r → ℕ) (c : Fin r → ℤ)
    (s g : GU σ r) (hs : mat s = Matrix.diagonal (fun i => ϖ ^ c i)) (hg : g ∈ rootU σ γ)
    (H : ∀ i l, i < l → γ i = γ l → ϖ ^ (c i - c l) * mat g i l ∈ intL L) : s * g * s⁻¹ ∈ KU σ r := by
  rw [mem_KU_iff hσ]
  intro i l
  have hr := conj_mem_root h0 γ c s g hs hg
  by_cases h1 : i < l
  · by_cases h2 : γ i = γ l
    · rw [mat_conj h0 c s g hs]; exact H i l h1 h2
    · rw [hr.2 i l h2]; exact zero_mem _
  · rw [hr.1 i l (not_lt.1 h1), Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem zpow_mul_int {ϖ : L} (hv : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (x : L) :
    ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) ≤ m → ϖ ^ m * x ∈ intL L := by
  by_cases hx : x = 0
  · exact ⟨0, fun m _ => by rw [hx, mul_zero]; exact zero_mem _⟩
  have hx' : Valued.v x ≠ (0 : WithZero (Multiplicative ℤ)) := by simpa using hx
  refine ⟨(WithZero.log (Valued.v x : WithZero (Multiplicative ℤ))).toNat, fun m hm => ?_⟩
  show Valued.v (ϖ ^ m * x) ≤ (1 : WithZero (Multiplicative ℤ))
  rw [map_mul, map_zpow₀, hv, ← WithZero.exp_log hx', ← WithZero.exp_zsmul, ← WithZero.exp_add,
    ← WithZero.exp_zero, WithZero.exp_le_exp]
  have := Int.self_le_toNat (WithZero.log (Valued.v x : WithZero (Multiplicative ℤ)))
  simp only [smul_eq_mul]
  omega

theorem contract : GlobalTheory.SatakeWeyl.Contract := by
  intro L _ _ ϖ σ q r γ b s g hU hb hs hg
  obtain ⟨-, hσ, -, hv, -⟩ := hU
  have hv' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hv
  have h0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv'
    exact WithZero.exp_ne_zero hv'.symm
  refine ⟨conj_mem_root h0 γ b s g hs hg, ?_, fun hK => ?_, ?_⟩
  · have := conj_mem_root h0 γ _ s⁻¹ g (mat_inv_diag h0 b s hs) hg
    rwa [inv_inv] at this
  · refine conj_mem_K h0 hσ γ b s g hs hg fun i l h1 h2 => ?_
    refine mul_mem ?_ ((mem_KU_iff hσ g).1 hK i l)
    show Valued.v (ϖ ^ (b i - b l)) ≤ (1 : WithZero (Multiplicative ℤ))
    have := hb i l h1 h2
    rw [map_zpow₀, hv', ← WithZero.exp_zsmul, ← WithZero.exp_zero, WithZero.exp_le_exp]
    simp only [smul_eq_mul]
    omega
  · choose N hN using fun p : Fin r × Fin r => zpow_mul_int hv' (mat g p.1 p.2)
    refine ⟨Finset.univ.sup N, conj_mem_K h0 hσ γ _ _ g (mat_pow_diag h0 b s hs _) hg fun i l h1 h2 => ?_⟩
    refine hN (i, l) _ ?_
    have h3 := hb i l h1 h2
    have h4 : (N (i, l) : ℤ) ≤ (Finset.univ.sup N : ℕ) := by
      exact_mod_cast Finset.le_sup (f := N) (Finset.mem_univ _)
    have h5 : (0 : ℤ) ≤ (Finset.univ.sup N : ℕ) := Int.natCast_nonneg _
    nlinarith

end GlobalTheory.SatakeWeyl.ContractProof

end
