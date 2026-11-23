import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.QlenEqZeroOfLe
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Thm0ConclOf
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.T0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem thm0Concl : Thm0Concl (D := D) (B := B) (P := P) (j := j) := thm0Concl_of thm0Local

theorem concl_of_hyp (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR Bx CT : ℝ) (S : Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (β : ℝ)
    (r : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hH : Hyp large₂ X H C2 A2 CR Bx CT S ka wL wF T nP nW h0 nus)
    (hc : 0 ≤ cc D large₂ H.Cc H.Ac H.CRc wL)
    (hr0 : ∀ la, 0 ≤ r la) (hrs : Summable (fun la => r la * X.lN la)) (hrb : (∑' la, r la * X.lN la) ≤ β)
    (hloc : ∀ la (e : ℕ), (T : ℝ) * nus la ≤ (e : ℝ) →
      ∃ L : LocDat X ka la, L.Ok S wL wF T e ∧ L.err T (cc D large₂ H.Cc H.Ac H.CRc wL) ≤ r la) :
    Concl X S ka wL wF T nus β := by
  have hT : 1 ≤ T := by
    obtain ⟨_, hS, _⟩ := hH
    exact (hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 : 0 < T)
  exact thm0Concl large₂ X H S ka wL wF T nus β r hH.2.2.2.1 hT hc
    (theta_le_msup_of_hyp X S hH) hr0 hrs hrb hloc

end Formalism.MainNotions.Gaps.T0
