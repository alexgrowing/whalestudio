import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUnique
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspExpansionDiscriminantIntegerLeadingOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHahnSeriesOfHasQStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHahnSeriesScaleTwistRingHomStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exp_conj : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω →+* Ω) (g : ℂ ≃+* ℂ) (N w : ℕ) (f f' : ℍ → ℂ)
    (h h' : HahnSeries ℚ Ω), (∀ x, g (ε x) = ε (s x)) → 0 < N →
    QAll (· ∈ ε.range) N (fun τ => DD τ ^ w * f τ) →
    QConj g N (fun τ => DD τ ^ w * f τ) (fun τ => DD τ ^ w * f' τ) →
    IsExp ε f h → IsExp ε f' h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  intro Ω _ ε s g N w f f' h h' hg hN hA hC hf hf' r
  obtain ⟨a, ha, haE⟩ := hA
  obtain ⟨c, hc, hc'⟩ := hC
  have hac : a = c := HasQ.coeff_unique hN ha hc
  subst hac
  choose b hb using fun n => RingHom.mem_range.mp (haE n)
  have ha' : HasQ N (fun τ => DD τ ^ w * f τ) (fun n => ε (b n)) := by
    have e : (fun n => ε (b n)) = a := funext hb
    rw [e]; exact ha
  have hc2 : HasQ N (fun τ => DD τ ^ w * f' τ) (fun n => ε (s (b n))) := by
    have e : (fun n => ε (s (b n))) = fun n => g (a n) := funext fun n => by rw [← hg, hb]
    rw [e]; exact hc'
  obtain ⟨H, hH, hHk, hH0⟩ := GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ Ω ε N _ b hN ha'
  obtain ⟨H', hH', hHk', hH0'⟩ := GlobalTheory.T.exists_hahnSeries_isExp_of_hasQ Ω ε N _ (fun n => s (b n)) hN hc2
  obtain ⟨hD, hDe, hD0, -, hDZ⟩ := GlobalTheory.T.exists_cuspExpansion_discriminant_integer_leading_one Ω ε
  obtain ⟨hops, huniq, -, -, -⟩ := GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_hahnSeries_scale_twist_ringHom Ω Ω s 1 (fun _ => 1) one_pos rfl (fun _ _ => (one_mul 1).symm)
  have hΦc : ∀ x r, (Φ x).coeff r = s (x.coeff r) := fun x r => by simpa using hΦ x r
  have hpow : ∀ (u : ℍ → ℂ) (k : HahnSeries ℚ Ω), IsExp ε u k → ∀ m : ℕ,
      IsExp ε (fun τ => DD τ ^ m * u τ) (hD ^ m * k) := by
    intro u k hu m
    induction m with
    | zero => simpa using hu
    | succ m ih =>
      have hm := (hops _ _ _ _ hDe ih).2.2
      have e1 : (fun τ => DD τ ^ (m + 1) * u τ) = DD * fun τ => DD τ ^ m * u τ := by
        funext τ; simp only [Pi.mul_apply, pow_succ]; ring
      have e2 : hD ^ (m + 1) * k = hD * (hD ^ m * k) := by ring
      rw [e1, e2]; exact hm
  have e1 : hD ^ w * h = H := huniq _ _ _ (hpow f h hf w) hH
  have e2 : hD ^ w * h' = H' := huniq _ _ _ (hpow f' h' hf' w) hH'
  have hΦD : Φ hD = hD := by
    ext r; rw [hΦc]; obtain ⟨n, hn⟩ := hDZ r; rw [hn, map_intCast]
  have hΦH : Φ H = H' := by
    ext r; rw [hΦc]
    by_cases hr : ∃ k : ℕ, r = (k : ℚ) / N
    · obtain ⟨k, rfl⟩ := hr; rw [hHk, hHk']
    · push_neg at hr; rw [hH0 r hr, hH0' r hr, map_zero]
  have key : hD ^ w * Φ h = hD ^ w * h' := by
    rw [e2, ← hΦH, ← e1, map_mul, map_pow, hΦD]
  have hne : hD ^ w ≠ 0 := pow_ne_zero _ hD0
  have hh := mul_left_cancel₀ hne key
  rw [← hh, hΦc]

end GlobalTheory.FN
