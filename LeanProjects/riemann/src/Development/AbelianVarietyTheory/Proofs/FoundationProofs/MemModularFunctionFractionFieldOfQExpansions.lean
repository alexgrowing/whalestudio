import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrictStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDeltaPowQExpansionIffLaurentSeriesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UniformPoleOrderStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusUpperHalfPlanePropertiesStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_of_qexp : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs, a (mob (ofSL γ) z) = a z) → (∀ γ : SL(2, ℤ), ∃ (c : ℤ → Ω) (n0 : ℤ), (∀ n < n0, c n = 0) ∧ ∀ z ∈ Hs, HasSum (fun n : ℤ => ε (c n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z / M)) (a (mob (ofSL γ) z))) → ∃ f : T.K, T.an f = (a : Mero) := by
  intro Ω _ _ _ ε T a M hM _ hinv hexp
  have hHs : ∀ τ : ℍ, (τ : ℂ) ∈ Hs := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict.2.2.2.2
  have hmob : ∀ (γ : SL(2, ℤ)) (τ : ℍ), mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ) := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties.2.2.2.1
  set f : ℍ → ℂ := fun τ => a τ with hf
  have hinvf : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, f (γ • τ) = f τ := by
    intro γ hγ τ
    simp only [hf]
    rw [← hmob γ τ]
    exact hinv γ hγ τ (hHs τ)
  have hw : ∀ γ : SL(2, ℤ), ∃ w : ℕ, QAll (· ∈ ε.range) M fun τ => DD τ ^ w * f (γ • τ) := by
    intro γ
    obtain ⟨c, n0, hc0, hs⟩ := hexp γ
    refine (GlobalTheory.T.exists_deltaPow_qExpansion_iff_laurentSeries ε.range M (fun τ => f (γ • τ)) hM).2 ⟨fun n => ε (c n), n0, fun n => ⟨c n, rfl⟩, ?_, ?_⟩
    · intro n hn
      simp [hc0 n hn]
    · intro τ
      have := hs τ (hHs τ)
      simp only [hf]
      rw [← hmob γ τ]
      exact this
  obtain ⟨w, hLv⟩ := GlobalTheory.T.exists_Lv_of_invariant_Gamma_of_forall_QAll ε.range M f hM hinvf hw
  have hmem : f ∈ ring ε.range := mem_ring_of_inR ⟨M, w, hM, hLv⟩
  refine ⟨T.io ⟨f, hmem⟩, ?_⟩
  rw [T.an_io]
  exact GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict.2.2.2.1 a

end GlobalTheory.FN
