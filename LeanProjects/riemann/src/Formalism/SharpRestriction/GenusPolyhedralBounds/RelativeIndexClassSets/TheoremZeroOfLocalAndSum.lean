import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LenAtEqZeroOfSubsingleton

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

theorem concl_of_nat {j : ℕ} (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (β : ℝ) (r : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (hnu : ∀ la, 0 ≤ nus la) (hr0 : ∀ la, 0 ≤ r la) (hrs : Summable (fun la => r la * X.lN la))
    (hrb : (∑' la, r la * X.lN la) ≤ β)
    (hloc : ∀ la (e : ℕ), (T : ℝ) * nus la ≤ (e : ℝ) →
      ∀ V' : Submodule (X.Kl la) (X.Vl la), V' ≤ X.locK la (X.Msup ka) →
        X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V') (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V') ≠ ⊤ ∧
        ((X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
            (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V')).toNat : ℝ) ≤
          (e : ℝ) * (Module.finrank (X.Kl la) V' : ℝ) + r la) :
    Concl X S ka wL wF T nus β := by
  unfold Concl
  refine ⟨r, hr0, hrs, hrb, ?_⟩
  intro la e he V' hV'
  have hT : (0 : ℝ) ≤ (T : ℝ) * nus la := mul_nonneg (Nat.cast_nonneg _) (hnu la)
  have he0 : (0 : ℤ) ≤ e := by
    have h := hT.trans he
    exact_mod_cast h
  lift e to ℕ using he0 with n
  have h := hloc la n (by exact_mod_cast he) V' hV'
  simpa only [Int.cast_natCast] using h

theorem theorem_zero_of_local_and_sum (hL : LocalBoundHypothesis D B P) (hS : SumBoundHypothesis D B P) : Conclusion1Of2 (D := D) (B := B) (P := P) := by
  unfold Conclusion1Of2
  intro large₂ X K H Ch Ah Cq Aq C2 A2 CR CT hA hB hEx j h1 h2 S ka wL wF T nP nW h0 nus hH
  obtain ⟨G, Gc, PH, Prw, Pet, Pd, hT, hD, hSh, hP, Qf, hOk, hHt⟩ := hEx j h1 h2 S ka wL wF T nP nW h0 nus hH
  have hsum := hS large₂ X K H Ch Ah Cq Aq C2 A2 CR CT hA hB j h1 h2 S ka wL wF T nP nW h0 nus hH G Gc PH Prw Pet Pd
    hT hD hSh hP Qf hOk hHt
  have hloc := hL large₂ X K H Ch Ah Cq Aq C2 A2 CR CT hA hB j h1 h2 S ka wL wF T nP nW h0 nus hH G Gc PH Prw Pet Pd
    hT hD hSh hP
  exact concl_of_nat (X j h1 h2) S ka wL wF T nus _ (fun la => rLa (Qf la) K.CRm T (cc D large₂ C2 A2 CR wL))
    hH.2.2.2.1.1 hsum.1 hsum.2.1 hsum.2.2
    (fun la e he V' hV' => hloc la (Qf la) (hOk la) (hHt.1 la) e he V' hV')

end Formalism.MainNotions.Gaps.EtaleWeightGaps
