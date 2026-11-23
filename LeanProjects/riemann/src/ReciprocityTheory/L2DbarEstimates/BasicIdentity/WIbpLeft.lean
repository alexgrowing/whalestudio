import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.BasicIdentityStatement
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportDTw

namespace ReciprocityTheory.L2DbarEstimates.E

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

theorem wIbp_left (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (k : Fin n) (a b : M → ℂ) (hph : CkR n z 1 ph) (ha : Ck n z 1 a) (hb : Ck n z 1 b)
    (hc : HasCompactSupport a ∨ HasCompactSupport b) :
    (∫ x, db n z k a x * conj (b x) * (Real.exp (-ph x) : ℂ) ∂vol n z) =
      -∫ x, a x * conj (dTw n z ph k b x) * (Real.exp (-ph x) : ℂ) ∂vol n z := by
  have hw : Ck n z 1 (fun x => (Real.exp (-ph x) : ℂ)) := ck_expNeg n z 1 ph hph
  have hbc : Ck n z 1 (fun x => conj (b x)) := Ck.conj n z 1 b hb
  set g : M → ℂ := fun x => conj (b x) * (Real.exp (-ph x) : ℂ) with hgdef
  have hg : Ck n z 1 g := Ck.mul n z 1 _ _ hbc hw

  have hdg : ∀ x, a x * db n z k g x =
      a x * conj (dTw n z ph k b x) * (Real.exp (-ph x) : ℂ) := by
    intro x
    have h1 := db_mul n z _ _ hbc hw k x
    beta_reduce at h1
    rw [hgdef, h1, db_conj n z b k x, db_expNeg n z ph hph k x, dTw, db_ofReal n z ph k x]
    simp only [map_sub, map_mul]
    ring
  have hL : (fun x => db n z k a x * conj (b x) * (Real.exp (-ph x) : ℂ)) =
      fun x => db n z k a x * g x := by
    funext x
    simp only [hgdef]
    ring
  have hR : (fun x => a x * conj (dTw n z ph k b x) * (Real.exp (-ph x) : ℂ)) =
      fun x => a x * db n z k g x := by
    funext x
    exact (hdg x).symm
  rw [hL, hR]
  rcases hc with hca | hcb
  · have h := integral_db_mul n z hz k g a hg ha hca
    have e1 : (fun x => db n z k a x * g x) = fun x => g x * db n z k a x := by
      funext x
      ring
    have e2 : (fun x => a x * db n z k g x) = fun x => db n z k g x * a x := by
      funext x
      ring
    rw [e1, e2, h, neg_neg]
  · have hgc : HasCompactSupport g :=
      (hcb.comp_left (map_zero (starRingEnd ℂ))).mul_right
    exact integral_db_mul n z hz k a g ha hg hgc

theorem wIbp (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] : WIbpStatement n M := by
  intro z hz ph k a b hph ha hb hc
  refine ⟨wIbp_left n z hz ph k a b hph ha hb hc, ?_⟩

  have h := wIbp_left n z hz ph k b a hph hb ha hc.symm
  have h' := congrArg (starRingEnd ℂ) h
  rw [← integral_conj, map_neg, ← integral_conj] at h'
  have e1 : (fun x => dTw n z ph k a x * conj (b x) * (Real.exp (-ph x) : ℂ)) =
      fun x => conj (b x * conj (dTw n z ph k a x) * (Real.exp (-ph x) : ℂ)) := by
    funext x
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  have e2 : (fun x => a x * conj (db n z k b x) * (Real.exp (-ph x) : ℂ)) =
      fun x => conj (db n z k b x * conj (a x) * (Real.exp (-ph x) : ℂ)) := by
    funext x
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  rw [e1, e2, h', neg_neg]

end

end ReciprocityTheory.L2DbarEstimates.E
