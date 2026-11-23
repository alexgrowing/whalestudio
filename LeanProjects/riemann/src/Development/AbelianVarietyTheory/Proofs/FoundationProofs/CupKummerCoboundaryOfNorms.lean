import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCarryCocycleCoboundaryOfNormsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCarryCoboundaryTwistCochainStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZmodCocycleEqCoboundaryOfUnitTwistedCocycleStatement

open GlobalTheory.NeedB Polynomial

theorem GlobalTheory.cup_kummer_coboundary_of_norms : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  (∀ (L : IntermediateField K Ω), FiniteDimensional K L → ∀ c : K, c ≠ 0 → ∃ x : L, Algebra.norm K x = c) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∃ η : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant η ∧ ∀ g h, kum ζ α g * kum ζ β h = η h - η (g * h) + η g := by
  intro K Ω _ _ _ _ _ N ζ hN hζ hfix hnorm a b α β ha hb hα hβ
  have : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  obtain ⟨w, hwc, hw⟩ := GlobalTheory.T.kummer_carry_cocycle_coboundary_of_norms K Ω N ζ hN hζ hfix hnorm a b α β ha hb hα hβ
  obtain ⟨v, hvc, hv⟩ := GlobalTheory.T.kummer_carry_coboundary_twist_cochain K Ω N ζ hN hζ hfix a b α β ha hb hα hβ w hwc hw
  exact GlobalTheory.T.exists_locallyConstant_zmod_coboundary_of_mu_cocycle K Ω N ζ hN hζ hfix (fun g h => kum ζ α g * kum ζ β h) v hvc hv
