import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqDiscriminantPowMulEvalJInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSlTwoPermutedModularFamilyOfLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PermutedModularFamilyMonicPolyCoeffInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularDiscriminantPowMulSlashTwelveMulStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section
namespace GlobalTheory.FN

theorem gact_one_bij (N : ℕ) : ActBij (gact N 1) := by
  intro γ
  simp only [gact, one_mul, inv_one, mul_one]
  exact (Group.mulRight_bijective _)

theorem redGL_one (N : ℕ) : redGL N 1 = 1 := by
  ext i j; simp [redGL]

theorem rel_div (w n : ℕ) (D x J : ℂ) (hD : D ≠ 0) (s : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (hs : ∀ j : Fin n, s j = D ^ (w * (n - j)) * (P j).eval J)
    (h : (D ^ w * x) ^ n + ∑ j, s j * (D ^ w * x) ^ (j : ℕ) = 0) :
    x ^ n + ∑ j, (P j).eval J * x ^ (j : ℕ) = 0 := by
  have hD' : D ^ (w * n) ≠ 0 := pow_ne_zero _ hD
  refine (mul_eq_zero.mp ?_).resolve_left hD'
  rw [← h, mul_add, Finset.mul_sum]
  congr 1
  · rw [mul_pow, pow_mul]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have hj : (j : ℕ) ≤ n := j.2.le
    have e : w * n = w * (n - j) + w * j := by rw [← mul_add, Nat.sub_add_cancel hj]
    rw [hs, e, mul_pow, pow_add, ← pow_mul]
    ring

theorem integral_over_jT : ∀ (E : Subring ℂ) (f : ℍ → ℂ), InR E f → ∃ (n : ℕ) (c : Fin n → Polynomial ℂ), (∀ i k, (c i).coeff k ∈ E) ∧ ∀ τ, f τ ^ n + ∑ i, (c i).eval (jT τ) * f τ ^ (i : ℕ) = 0 := by
  intro E f ⟨N, w, hN, hinv, hq⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  have hslash : ∀ γ : SL(2, ℤ), (fun τ => DD τ ^ w * f τ) ∣[((12 * w : ℕ) : ℤ)] γ = fun τ => DD τ ^ w * f (γ • τ) :=
    fun γ => GlobalTheory.T.modularDiscriminant_pow_mul_slash_twelve_mul w f γ
  have hΓ : ∀ γ ∈ CongruenceSubgroup.Gamma N, (fun τ => DD τ ^ w * f τ) ∣[((12 * w : ℕ) : ℤ)] γ = (fun τ => DD τ ^ w * f τ) := by
    intro γ hγ
    rw [hslash]; funext τ; rw [hinv γ hγ τ]
  obtain ⟨F, hFam, hFγ, hF0⟩ := GlobalTheory.T.exists_slTwoPermutedModularFamily_of_level N ((12 * w : ℕ) : ℤ) _ hΓ
  have hQ : ∀ α, QAll (· ∈ E) N (F α) := by
    intro α
    rcases hF0 α with ⟨γ, rfl⟩ | h0
    · rw [hFγ, hslash]; exact hq γ
    · rw [h0]
      refine ⟨fun _ => 0, fun τ => ?_, fun _ => E.zero_mem⟩
      simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  have h1 : F 1 = fun τ => DD τ ^ w * f τ := by
    rw [← redGL_one N, hFγ]; exact SlashAction.slash_one _ _
  obtain ⟨s, hs, hpoly⟩ := GlobalTheory.T.permutedModularFamily_monic_poly_coeff_invariant (GL (Fin 2) (ZMod N)) (gact N 1) (12 * w) N F E hN
    (gact_one_bij N) hFam hQ
  have key := hpoly 1
  rw [h1] at key
  clear hpoly hFam hF0 hFγ hQ h1 hslash hΓ
  revert s
  generalize Fintype.card (GL (Fin 2) (ZMod N)) = n
  intro s hs key
  have hP : ∀ j : Fin n, ∃ P : Polynomial ℂ, (∀ i, P.coeff i ∈ E) ∧
      ∀ τ, s j τ = DD τ ^ (w * (n - j)) * P.eval (jT τ) := by
    intro j
    refine GlobalTheory.QFam.exists_eq_DD_pow_mul_eval_jT E N (w * (n - j)) (s j) hN (fun γ => ?_) (hs j).2
    have := (hs j).1 γ
    convert this using 3
    push_cast; ring
  choose P hPc hPe using hP
  exact ⟨n, P, hPc, fun τ => rel_div w n (DD τ) (f τ) (jT τ) (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
    (fun j => s j τ) P (fun j => hPe j τ) (key τ)⟩

end GlobalTheory.FN
