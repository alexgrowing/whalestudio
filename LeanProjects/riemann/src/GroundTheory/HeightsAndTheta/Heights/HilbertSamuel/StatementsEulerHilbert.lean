import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedModOfSubsingleton
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedHilbertPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEventualPolynomial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

def EulerHilbert.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Q : Ideal (MRingOver F ι)) (p : MvPolynomial K ℚ) (a₀ : ℕ),
    NumbersDVR.IsMultiProjPrime Q →
    (∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      (hilbFn Q (fun k => (a k : ℤ)) : ℚ) = MvPolynomial.eval (fun k => (a k : ℚ)) p) →
    ∀ b : K → ℤ, (∀ i : ℕ, 1 ≤ i → Subsingleton (KH.cechHc ι (KH.quotPart F Q) b i)) →
      (Module.finrank F (KH.cechHc ι (KH.quotPart F Q) b 0) : ℚ) = MvPolynomial.eval (fun k => (b k : ℚ)) p

theorem ringKrullDim_point :
    ringKrullDim (MRingOver ℚ pointIdx ⧸ (⊥ : Ideal (MRingOver ℚ pointIdx))) =
      ((0 + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

theorem cechHc_point_subsingleton {M : Type} [AddCommGroup M] [Module (MRingOver ℚ pointIdx) M] [Module ℚ M]
    [IsScalarTower ℚ (MRingOver ℚ pointIdx) M] (𝓜 : (Unit → ℤ) → Submodule ℚ M) (b : Unit → ℤ) (i : ℕ)
    (hi : 1 ≤ i) : Subsingleton (KH.cechHc pointIdx 𝓜 b i) := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have := cell_succ_isEmpty (K := Unit) (ι := pointIdx) n
  have : Subsingleton (KH.CechC ℚ pointIdx M (n + 1)) :=
    ⟨fun f g => funext fun I => (IsEmpty.false I).elim⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Subsingleton.elim x y]

theorem EulerHilbert.hyps_inhabited :
    ∃ (p : MvPolynomial Unit ℚ) (a₀ : ℕ), NumbersDVR.IsMultiProjPrime (⊥ : Ideal (MRingOver ℚ pointIdx)) ∧
      (∀ a : Unit → ℕ, (∀ k, a₀ ≤ a k) →
        (hilbFn (⊥ : Ideal (MRingOver ℚ pointIdx)) (fun k => (a k : ℤ)) : ℚ) =
          MvPolynomial.eval (fun k => (a k : ℚ)) p) ∧
      ∀ i : ℕ, 1 ≤ i → Subsingleton (KH.cechHc pointIdx (KH.quotPart ℚ (⊥ : Ideal (MRingOver ℚ pointIdx))) 0 i) := by
  obtain ⟨p, a₀, -, hp⟩ := MultigradedHilbertPolynomial.proof EventualPolynomial.proof ℚ Unit pointIdx ⊥ 0
    NumbersDVR.isMultiProjPrime_bot ringKrullDim_point
  exact ⟨p, a₀, NumbersDVR.isMultiProjPrime_bot, hp, fun i hi => cechHc_point_subsingleton _ _ i hi⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
