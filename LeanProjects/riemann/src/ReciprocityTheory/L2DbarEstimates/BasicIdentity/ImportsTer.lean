import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.BasicIdentityStatement
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportDTw
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.WIbpLeft
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.ImportsBis

namespace ReciprocityTheory.L2DbarEstimates.E

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

theorem pair (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (hph : CkR n z 2 ph) (a b : M → ℂ) (ha : Ck n z 2 a) (_hac : HasCompactSupport a)
    (hb : Ck n z 2 b) (hbc : HasCompactSupport b) (j k : Fin n) :
    (∫ x, dTw n z ph j a x * conj (dTw n z ph k b x) * (Real.exp (-ph x) : ℂ) ∂vol n z) =
      (∫ x, d n z j (db n z k (fun y => (ph y : ℂ))) x * a x * conj (b x) *
          (Real.exp (-ph x) : ℂ) ∂vol n z) +
        ∫ x, db n z k a x * conj (db n z j b x) * (Real.exp (-ph x) : ℂ) ∂vol n z := by
  have hph1 : CkR n z 1 ph := Ck.mono n z 1 2 (by norm_num) _ hph
  have ha1 : Ck n z 1 a := Ck.mono n z 1 2 (by norm_num) a ha
  have hb1 : Ck n z 1 b := Ck.mono n z 1 2 (by norm_num) b hb
  have hE := ck_expNeg n z 1 ph hph1
  have hdTa : Ck n z 1 (dTw n z ph j a) := ck_dTw n z 1 ph j a hph ha
  have hdba : Ck n z 1 (db n z k a) := Ck.db n z 1 k a ha
  have s1 := wIbp_left n z hz ph k (dTw n z ph j a) b hph1 hdTa hb1 (Or.inr hbc)
  have s3 := ((wIbp n M) z hz ph j (db n z k a) b hph1 hdba hb1 (Or.inr hbc)).2
  have hcomm : ∀ x, db n z k (dTw n z ph j a) x = dTw n z ph j (db n z k a) x -
      d n z j (db n z k (fun y => (ph y : ℂ))) x * a x := by
    intro x
    have := comm n M z hz ph k j a x hph ha
    linear_combination -this
  have hcb : Continuous (fun x => conj (b x)) := Ck.continuous n z hz 1 _ (Ck.conj n z 1 b hb1)
  have hcE : Continuous (fun x => (Real.exp (-ph x) : ℂ)) := Ck.continuous n z hz 1 _ hE
  have hint1 : Integrable (fun x => dTw n z ph j (db n z k a) x * conj (b x) *
      (Real.exp (-ph x) : ℂ)) (vol n z) := by
    apply integrable_of_continuous n z hz
    · exact ((Ck.continuous n z hz 0 _ (ck_dTw n z 0 ph j (db n z k a) hph1 hdba)).mul hcb).mul hcE
    · apply HasCompactSupport.mono' hbc
      intro x hx
      apply subset_tsupport
      intro h0
      apply hx
      simp [h0]
  have hint2 : Integrable (fun x => d n z j (db n z k (fun y => (ph y : ℂ))) x * a x *
      conj (b x) * (Real.exp (-ph x) : ℂ)) (vol n z) := by
    apply integrable_of_continuous n z hz
    · exact (((Ck.continuous n z hz 0 _ (Ck.d n z 0 j _ (Ck.db n z 1 k _ hph))).mul
        (Ck.continuous n z hz 1 _ ha1)).mul hcb).mul hcE
    · apply HasCompactSupport.mono' hbc
      intro x hx
      apply subset_tsupport
      intro h0
      apply hx
      simp [h0]
  have e2 : ∫ x, db n z k (dTw n z ph j a) x * conj (b x) * (Real.exp (-ph x) : ℂ) ∂vol n z =
      (∫ x, dTw n z ph j (db n z k a) x * conj (b x) * (Real.exp (-ph x) : ℂ) ∂vol n z) -
        ∫ x, d n z j (db n z k (fun y => (ph y : ℂ))) x * a x * conj (b x) *
          (Real.exp (-ph x) : ℂ) ∂vol n z := by
    rw [← integral_sub hint1 hint2]
    congr 1
    funext x
    rw [hcomm x]
    ring
  rw [e2, s3] at s1
  linear_combination s1

end

end ReciprocityTheory.L2DbarEstimates.E
