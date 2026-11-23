import Formalism.PieriBlockIdeals.TailInequalityEventually
import Formalism.QuotientMetricDivisors.ClassSumDualLe
import Formalism.MirabolicMackeyTheory.StatementT

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.CohomologicalDescent.JD

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling

def JointPlace : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
    Hᴴ = H → IsUnit H.det →
    ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
    ∀ A B : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K A →
    ∀ DG : ℕ, 0 < DG → (∀ y ∈ B, (DG : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) A) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (J : ℕ),
    (∀ z ∈ cutLat E A, (((plc w : ℕ) : 𝓞 K) ^ J) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E B)) →
      (jw (Eᴴ * H * E) w (matLat Pr A) : ℝ) ≤
        ((J : ℝ) * (ramw w : ℝ) + (vw w (DG : K) : ℝ)) * (d : ℝ) +
          (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr A) (cutLat E A) : ℝ)

def JointSum : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (J : ℕ → ℕ) (DG : ℕ), 0 < DG → ∀ Bd : ℝ,
    (∀ Q : Finset ℕ, (∀ l ∈ Q, l.Prime) → ∑ l ∈ Q, (J l : ℝ) * Real.log (l : ℝ) ≤ Bd) →
      ∑ w ∈ S, lw w * ((J (plc w) : ℝ) * (ramw w : ℝ) + (vw w (DG : K) : ℝ)) ≤ Bd + Real.log (DG : ℝ)

def JointSize : Prop :=
  ∀ (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (T : ℕ) (ε xe Nc : ℝ), P.Hyp → T ≤ P.f → 0 < ε → P.x ^ ε ≤ xe → 0 ≤ Nc →
    30 * (T : ℝ) * (P.m : ℝ) * P.b * P.x ^ (2 * ε) + 2 * (P.m : ℝ) * P.b ≤
        32 * P.x ^ ε * ((P.f : ℝ) * (P.m : ℝ) * P.b * P.x ^ ε) ∧
      32 * P.x ^ ε * ((P.f : ℝ) * (P.m : ℝ) * P.b * P.x ^ ε) ≤
        32 * xe * ((P.f : ℝ) * (P.m : ℝ) * P.b * P.x ^ ε + Nc)

section Record

open TensorProduct MvPolynomial
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds
  Formalism.CohomologicalDescent.LargeParameterEstimates

def JointRecord : Prop :=
  LA.LemmaAZ → ∀ ε C : ℝ, 0 < ε → ∃ x0 : ℝ, ∀ P : Par, P.Hyp → x0 ≤ P.x → P.L = P.x ^ ε →
    Rows P (Real.exp (P.x ^ (ε / 3))) (P.x ^ C) → P.b ^ ((4 : ℝ) / 5) ≤ P.w'' / P.S →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (W : Wts ι), W.Ok P → Fintype.card ι = P.f →
    W.Sp.card ≤ 5 →
    ∀ X : ℕ → HidaSetting ι P.Nr W.lam, (∀ l : ℕ, l.Prime → ¬ IsUnit ((l : ℕ) : (X l).O)) →
    (∀ l : ℕ, l.Prime → W.WRange P l → (X l).WInputs l (kc P) W.j W.T2 (W.iW P l)) →
    (∀ l : ℕ, l.Prime → (X l).Incl l (W.Jrec7 P l)) ∧
    (∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : Finset (HeightOneSpectrum (𝓞 K)))
      (DG : ℕ), 0 < DG →
      ∑ w ∈ S, lw w * ((W.Jrec7 P (plc w) : ℝ) * (ramw w : ℝ) + (vw w (DG : K) : ℝ)) ≤
          30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.x ^ (2 * ε) + 2 * (P.m : ℝ) * P.b +
            Real.log (DG : ℝ) ∧
      30 * (W.T2.card : ℝ) * (P.m : ℝ) * P.b * P.x ^ (2 * ε) + 2 * (P.m : ℝ) * P.b ≤
          32 * P.x ^ ε * ((P.f : ℝ) * (P.m : ℝ) * P.b * P.x ^ ε)) ∧
    (∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n d : ℕ) (H : Matrix (Fin n) (Fin n) K),
      Hᴴ = H → IsUnit H.det →
      ∀ (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K), IsOrthProj H E Pr →
      ∀ A B : Submodule (𝓞 K) (Fin n → K), Submodule.IsLattice K A →
      ∀ DG : ℕ, 0 < DG → (∀ y ∈ B, (DG : 𝓞 K) • y ∈ Formalism.HermitianLatticesTheory.dual (hform H) A) →
      ∀ w : HeightOneSpectrum (𝓞 K),
      (∀ z ∈ cutLat E A,
        (((plc w : ℕ) : 𝓞 K) ^ W.Jrec7 P (plc w)) • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (cutLat E B)) →
        (jw (Eᴴ * H * E) w (matLat Pr A) : ℝ) ≤
          ((W.Jrec7 P (plc w) : ℝ) * (ramw w : ℝ) + (vw w (DG : K) : ℝ)) * (d : ℝ) +
            (Formalism.HermitianLatticesTheory.locLen w.asIdeal (matLat Pr A) (cutLat E A) : ℝ))

end Record

end Formalism.CohomologicalDescent.JD
