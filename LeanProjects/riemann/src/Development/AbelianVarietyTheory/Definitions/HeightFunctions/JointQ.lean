import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2

structure HostSz {R : Ranks} (H : Formalism.BasicNotions.Host R) (L : ℝ) : Prop where
  rank : 62 ≤ R.r
  len : 4 ≤ L
  deg : Real.log R.f ≤ L
  g : ∀ i, Real.log (H.g i) ≤ 9 * L + 1
  p : Real.log H.pde ≤ L ∧ Real.log H.pde' ≤ L
  rd : Real.log |((discr H.E : ℤ) : ℝ)| / (2 * R.f) ≤ 2 * L

def poR (R : Ranks) (L : ℝ) : ℝ := 19 * (R.f : ℝ) * (R.r : ℝ) ^ 2 * L + 198 * (R.f : ℝ) ^ 2 * L

def xiOrd {R : Ranks} (H : Formalism.BasicNotions.Host R) (N : ℕ) : ℕ :=
  2 * classNumber H.E * Nat.card (𝓞 H.E ⧸ Ideal.span {(N : 𝓞 H.E)})ˣ

structure Rich (P : Pre) (F : IntermediateField ℚ ℂ) : Prop where
  host : ∀ x : P.host.E, P.host.φ₀ x ∈ F
  roots : ∀ N ∈ [P.restRowsFiniteGroupCard, P.host.g 0 * (P.host.g 0 - 1), P.host.g 1 * (P.host.g 1 - 1), 3 ^ 4, 5 ^ 4, P.host.pde, P.host.pde',
      classNumber P.host.E, xiOrd P.host (P.host.g 0 * P.host.g 1 * P.host.pde),
      xiOrd P.host (P.host.g 0 * P.host.g 1 * P.host.pde')], Complex.exp (2 * Real.pi * Complex.I / (N : ℕ)) ∈ F
  capit : ∀ 𝔞 : Ideal (𝓞 P.host.E), ∃ β : F,
    Submodule.span (𝓞 F) {β} = Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = P.host.φ₀ (a : P.host.E)}
  kPsi : ∀ j, 1 ≤ j → j ≤ P.R.m → ∀ 𝔞 : Ideal (𝓞 P.host.E), 𝔞 ≠ ⊥ → ∃ β : F, β ≠ 0 ∧
    Submodule.span (𝓞 F) {β} =
      ∏ g : Tau P.R,
        (Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = P.host.φ₀ (P.host.sigmaOf g (a : P.host.E))} ^ (P.R.sigW j).1 *
          Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = P.host.φ₀ (P.host.sigmaOf g (P.host.conj (a : P.host.E)))} ^
            (P.R.sigW j).2) ∧
    ∀ σ : F →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ ((P.R.sigW j).1 + (P.R.sigW j).2)
  weber : ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + P.host.φ₀ P.host.sqrtMinusD) / 2)) →
    ∀ p ∈ [P.host.pde, P.host.pde'], weberSet L (P.host.g 0 * P.host.g 1 * p) ⊆ F

def JointQ (D : D7) : Prop :=
  FieldOK0 D D.host.pde ∧ FieldOK0 D D.host.pde' ∧ (∃ xi, XiOK D D.host.pde xi) ∧ (∃ xi, XiOK D D.host.pde' xi) ∧
    ∀ L : ℝ, HostSz D.host L → Sz (FO D) (poR D.R L) (poR D.R L)

end GlobalTheory.FieldSize
