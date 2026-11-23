import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyBezoutSeparableDerivativeAdicIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjEtaleMemCentralizerMulIntegralGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralTwistedConjugatesTwistedCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalUnitAlmostAll

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.LocGoodP

theorem nrmL_mem {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (z : GLw n w) (hz : z ∈ GlobalTheory.LFun.KGL w n) : nrmL n w z ∈ GlobalTheory.LFun.KGL w n := by
  obtain ⟨-, -, hKθ, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU n w
  unfold nrmL
  split_ifs with hs
  · exact hz
  · have : thetaGL n (cj w) z = thL n w z := by unfold thL; rw [if_neg hs]
    rw [this]
    exact (GlobalTheory.LFun.KGL w n).mul_mem hz (hKθ _ hz)

theorem commute_nrmL {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (z t : GLw n w) (ht : t ∈ twCent (thL n w) z) : t * nrmL n w z = nrmL n w z * t := by
  obtain ⟨-, hinv, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU n w
  have ht' : t * z = z * thL n w t := ht
  by_cases hs : IsSplitAt w
  · have hθ1 : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
    have hn1 : nrmL n w z = z := by unfold nrmL; rw [if_pos hs]
    rw [hn1]; rw [hθ1] at ht'; simpa using ht'
  · have hn1 : nrmL n w z = z * thL n w z := by
      unfold nrmL; rw [if_neg hs]; unfold thL; rw [if_neg hs]
    rw [hn1]
    calc t * (z * thL n w z) = z * thL n w t * thL n w z := by rw [← mul_assoc, ht']
      _ = z * thL n w (t * z) := by simp only [map_mul, mul_assoc]
      _ = z * thL n w (z * thL n w t) := by rw [ht']
      _ = z * thL n w z * t := by simp only [map_mul, hinv, mul_assoc]

end PositivityTheory.Rg.BcB.G3.LocGoodP

open PositivityTheory.Rg.BcB.G3.LocGoodP in
theorem PositivityTheory.Rg.BcB.G3.locGood_pf : LocGood := by
  intro E _ _ _ hU n P hP
  filter_upwards [GlobalTheory.BCT.SepBezout.bezout_eventually E P hP.2.2.1,
    GlobalTheory.BCT.UnitStable.eventually_separable (E := E) P hP.2.2.1] with w hgood hsep
  intro z hzK hz
  have hgood₀ : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w z).val.charpoly + v * derivative (nrmL n w z).val.charpoly = 1 := by
    rw [hz]; exact hgood
  have hNK := nrmL_mem hU n w z hzK
  refine ⟨fun g hg => ?_, fun t ht hc => ?_, fun y hyK hy => ?_⟩
  · by_cases hs : IsSplitAt w
    · have hθ1 : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
      have hn1 : nrmL n w z = z := by unfold nrmL; rw [if_pos hs]
      rw [hn1] at hgood₀
      rw [hθ1] at hg
      obtain ⟨t, ht, k, hk, rfl⟩ := GlobalTheory.SplitUniq.splitUniq E n w z g hzK hgood₀ hg
      refine ⟨t, ?_, k, hk, rfl⟩
      show t * z = z * thL n w t
      rw [hθ1]; exact ht
    · exact GlobalTheory.InertUniq.eq_twCent_mul_KGL E hU n w hs z g hzK hgood₀ hg
  · exact GlobalTheory.StabInt.mem_KGL_of_commute E n w (nrmL n w z) t hNK hgood₀ (commute_nrmL hU n w z t ht) hc
  · exact GlobalTheory.BCT.UnitStable.twConj_of_mem hU n w (atPl w P) hsep z y hz hy hzK hyK
