import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormalisedPullbackMulNReadsThetaStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SymmetricLiftOddOrderActsAsTranslationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnVal

private theorem AnFr.exp_nsmul_eq_pow_vt {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ}
    (Φ : AnFr A L x0 g) (z : Fin g → ℂ) (n : ℕ) : Φ.e (n • z) = Φ.e z ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero]; exact (Φ.e_ker 0).2 Φ.lat.zero_mem
  | succ n ih => rw [succ_nsmul, Φ.e_add, ih, pow_succ]

theorem rd_vt_and_uu : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) (Φ : AnFr A L x0 g), (∀ a ∈ Φ.lat, Φ.χ a ^ 2 = 1) → ∀ (N : ℕ), Odd N → ∀ (s : LB.Sec (LPow A L.L 1 (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ), Φ.Rd 1 s θ → (∀ (ok : (Over.mk x0 ⟶ A) → Prop) (t : Over.mk x0 ⟶ A) (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) (Over.mk x0))), IsVtOver A L N ok s t F → (∀ t', ok t' → t' ^ N = t → t' ^ (N ^ 2) = 1) → ∃ x δ : Fin g → ℂ, δ ∈ Φ.lat ∧ ((N : ℂ) ^ 2) • x = (2 : ℂ) • δ ∧ ok (Φ.e x) ∧ Φ.e x ^ N = t ∧ Φ.Rd ((N : ℤ) ^ 2) F (fock Φ.Hm ((N : ℤ) ^ 2) x fun z => θ ((N : ℂ) • z))) ∧ ∀ (x₁ δ₁ x₂ δ₂ : Fin g → ℂ) (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) (Over.mk x0))), δ₁ ∈ Φ.lat → ((N : ℂ) ^ 2) • x₁ = (2 : ℂ) • δ₁ → δ₂ ∈ Φ.lat → ((N : ℂ) ^ 2) • x₂ = (2 : ℂ) • δ₂ → IsUUOver A L N s (Φ.e x₁) (Φ.e x₂) F → Φ.Rd ((N : ℤ) ^ 2) F (fock Φ.Hm ((N : ℤ) ^ 2) x₂ (fock Φ.Hm ((N : ℤ) ^ 2) x₁ fun z => θ ((N : ℂ) • z))) := by
  intro S A _ _ L x0 g Φ hχ N hN s θ hs
  have hN2 : Odd (N ^ 2) := hN.pow
  refine ⟨?_, ?_⟩
  · rintro ok t F ⟨t', α₀, α, s₁, U, ht, hok, h1, h2, h3, h4, h5, h6⟩ hkill
    obtain ⟨x', rfl⟩ := Φ.e_onto t'
    have hl : (N ^ 2) • x' ∈ Φ.lat := by
      rw [← Φ.e_ker, Φ.exp_nsmul_eq_pow_vt]; exact hkill _ hok ht
    obtain ⟨m, hm⟩ := hN2
    have he : Φ.e (x' + (N ^ 2) • x') = Φ.e x' := by
      rw [Φ.e_add, (Φ.e_ker _).2 hl, _root_.mul_one]
    have hx : ((N ^ 2 : ℕ) : ℂ) • (x' + (N ^ 2) • x') = (2 : ℂ) • ((m + 1) • (N ^ 2) • x') := by
      rw [hm]
      ext i
      simp only [Pi.smul_apply, Pi.add_apply]
      simp only [smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
    refine ⟨x' + (N ^ 2) • x', (m + 1) • (N ^ 2) • x', Φ.lat.nsmul_mem hl _, ?_, ?_, ?_, ?_⟩
    · simpa only [Nat.cast_pow] using hx
    · rw [he]; exact hok
    · rw [he]; exact ht
    · refine GlobalTheory.T.symmetric_lift_odd_order_acts_as_translation S A L x0 g Φ hχ _ (N ^ 2) U _ _ s₁ F _ ⟨m, hm⟩ (Φ.lat.nsmul_mem hl _) hx ?_ h6
        (GlobalTheory.T.normalisedPullbackMulN_reads_theta S A L x0 g Φ N α₀ α s s₁ θ h1 h2 h3 h4 hs)
      rw [he]; exact h5
  · rintro x₁ δ₁ x₂ δ₂ F hδ₁ hx₁ hδ₂ hx₂ ⟨α₀, α, s₁, s₂, U₁, U₂, h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine GlobalTheory.T.symmetric_lift_odd_order_acts_as_translation S A L x0 g Φ hχ _ (N ^ 2) U₂ x₂ δ₂ s₂ F _ hN2 hδ₂ (by simpa only [Nat.cast_pow] using hx₂) h7 h8 ?_
    exact GlobalTheory.T.symmetric_lift_odd_order_acts_as_translation S A L x0 g Φ hχ _ (N ^ 2) U₁ x₁ δ₁ s₁ s₂ _ hN2 hδ₁ (by simpa only [Nat.cast_pow] using hx₁) h5 h6
      (GlobalTheory.T.normalisedPullbackMulN_reads_theta S A L x0 g Φ N α₀ α s s₁ θ h1 h2 h3 h4 hs)

end GlobalTheory.AnVal
