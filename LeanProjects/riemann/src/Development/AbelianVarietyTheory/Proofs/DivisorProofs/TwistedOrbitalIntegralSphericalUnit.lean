import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyBezoutSeparableDerivativeAdicIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjEtaleMemCentralizerMulIntegralGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralTwistedConjugatesTwistedCentralizerStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitOrb

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hR : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
  unfold avg
  rw [hR, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  rw [finsum_eq_single _ (1 : H ⧸ (⊤ : Subgroup H)) (fun q hq => absurd (Subsingleton.elim q 1) hq)]
  simp

theorem twOrb_unit_eventually : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ∀ y : GLw n w, (nrmL n w y).val.charpoly = atPl w P → twOrb (thL n w) (GlobalTheory.LFun.KGL w n) y ((GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1) = if ∃ g : GLw n w, g⁻¹ * y * thL n w g ∈ GlobalTheory.LFun.KGL w n then 1 else 0 := by
  intro E _ _ _ hU n S _ P hP
  filter_upwards [GlobalTheory.T.eventually_bezout_separable_derivative_adicIntegers E P hP.2.2.1] with w hgood
  intro y hy
  obtain ⟨-, hinv, hKθ, hnrm, -⟩ := GlobalTheory.T.localTwist_continuous_involution_integral_properties E hU n w
  set K := GlobalTheory.LFun.KGL w n with hKdef
  set θ := thL n w with hθdef

  have hsumm : ∀ x : GLw n w, GlobalTheory.TwOrbConj.summand θ K y ((K : Set (GLw n w)).indicator 1) x =
      if x⁻¹ * y * θ x ∈ K then
        (((twCent θ y ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ y)) : ℕ) : ℂ) else 0 := by
    intro x
    unfold GlobalTheory.TwOrbConj.summand
    have hc : (fun k : K => (K : Set (GLw n w)).indicator (1 : GLw n w → ℂ) ((x * k)⁻¹ * y * θ (x * k))) =
        fun _ => (K : Set (GLw n w)).indicator (1 : GLw n w → ℂ) (x⁻¹ * y * θ x) := by
      funext k
      have e : (x * (k : GLw n w))⁻¹ * y * θ (x * k) = (k : GLw n w)⁻¹ * (x⁻¹ * y * θ x) * θ k := by
        simp only [map_mul, _root_.mul_inv_rev]; group
      rw [e]
      by_cases hm : x⁻¹ * y * θ x ∈ K
      · rw [Set.indicator_of_mem (show _ ∈ (K : Set (GLw n w)) from
          K.mul_mem (K.mul_mem (K.inv_mem k.2) hm) (hKθ _ k.2)), Set.indicator_of_mem (show _ ∈ (K : Set (GLw n w)) from hm)]
        rfl
      · rw [Set.indicator_of_notMem (show _ ∉ (K : Set (GLw n w)) from hm), Set.indicator_of_notMem]
        intro h
        apply hm
        have := K.mul_mem (K.mul_mem k.2 h) (K.inv_mem (hKθ _ k.2))
        simpa [mul_assoc] using this
    rw [hc, avg_const]
    by_cases hm : x⁻¹ * y * θ x ∈ K
    · rw [Set.indicator_of_mem (show _ ∈ (K : Set (GLw n w)) from hm), if_pos hm]; simp
    · rw [Set.indicator_of_notMem (show _ ∉ (K : Set (GLw n w)) from hm), if_neg hm]; simp
  rw [GlobalTheory.TwOrbConj.twOrb_eq]
  by_cases hex : ∃ g : GLw n w, g⁻¹ * y * θ g ∈ K
  swap
  · rw [if_neg hex]
    refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
    rw [hsumm, if_neg (fun h => hex ⟨_, h⟩)]
  rw [if_pos hex]
  obtain ⟨g₀, hg₀⟩ := hex
  set y₀ := g₀⁻¹ * y * θ g₀ with hy₀

  have hN₀ : nrmL n w y₀ = g₀⁻¹ * nrmL n w y * g₀ := hnrm g₀ y
  have hQ₀ : (nrmL n w y₀).val.charpoly = atPl w P := by
    rw [hN₀, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj', hy]
  have hgood₀ : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w y₀).val.charpoly + v * derivative (nrmL n w y₀).val.charpoly = 1 := by
    rw [hQ₀]; exact hgood
  have hNK : nrmL n w y₀ ∈ K := by
    unfold nrmL
    split_ifs with hs
    · exact hg₀
    · have : thetaGL n (cj w) y₀ = θ y₀ := by rw [hθdef]; unfold thL; rw [if_neg hs]
      rw [this]; exact K.mul_mem hg₀ (hKθ _ hg₀)

  have huniq : ∀ g : GLw n w, g⁻¹ * y₀ * θ g ∈ K → ∃ t ∈ twCent θ y₀, ∃ k ∈ K, g = t * k := by
    intro g hg
    by_cases hs : IsSplitAt w
    · have hθ1 : θ = MonoidHom.id _ := by rw [hθdef]; unfold thL; rw [if_pos hs]
      have hn1 : nrmL n w y₀ = y₀ := by unfold nrmL; rw [if_pos hs]
      rw [hn1] at hgood₀
      rw [hθ1] at hg ⊢
      obtain ⟨t, ht, k, hk, rfl⟩ := GlobalTheory.T.integral_conj_etale_mem_centralizer_mul_integralGL E n w y₀ g hg₀ hgood₀ hg
      exact ⟨t, ht, k, hk, rfl⟩
    · exact GlobalTheory.T.inert_integral_twistedConjugates_twistedCentralizer_mul_maxCompact E hU n w hs y₀ g hg₀ hgood₀ hg

  have hcomm : ∀ t ∈ twCent θ y₀, t * nrmL n w y₀ = nrmL n w y₀ * t := by
    intro t ht
    have ht' : t * y₀ = y₀ * θ t := ht
    by_cases hs : IsSplitAt w
    · have hθ1 : θ = MonoidHom.id _ := by rw [hθdef]; unfold thL; rw [if_pos hs]
      have hn1 : nrmL n w y₀ = y₀ := by unfold nrmL; rw [if_pos hs]
      rw [hn1]; rw [hθ1] at ht'; simpa using ht'
    · have hn1 : nrmL n w y₀ = y₀ * θ y₀ := by
        unfold nrmL; rw [if_neg hs, hθdef]; unfold thL; rw [if_neg hs]
      rw [hn1]
      calc t * (y₀ * θ y₀) = y₀ * θ t * θ y₀ := by rw [← mul_assoc, ht']
        _ = y₀ * θ (t * y₀) := by simp only [map_mul, mul_assoc]
        _ = y₀ * θ (y₀ * θ t) := by rw [ht']
        _ = y₀ * θ y₀ * t := by simp only [map_mul, hinv, mul_assoc]
  have hcpt : cptPart (twCent θ y₀) ≤ twCent θ y₀ ⊓ K := by
    refine le_inf ((Subgroup.closure_le _).2 fun t ht => ht.1) ((Subgroup.closure_le _).2 fun t ht => ?_)
    exact GlobalTheory.T.mem_maxCompactGL_of_commute_etale_charpoly_bounded E n w (nrmL n w y₀) t hNK hgood₀ (hcomm t ht.1) ht.2

  have hT : twCent θ y = (twCent θ y₀).map (MulAut.conj g₀).toMonoidHom := by
    rw [hy₀, GlobalTheory.TwOrbConj.twCent_conj, ← GlobalTheory.TwOrbConj.map_conj_mul, mul_inv_cancel,
      GlobalTheory.TwOrbConj.map_conj_self _ (Subgroup.one_mem _)]
  have hval : GlobalTheory.TwOrbConj.summand θ K y ((K : Set (GLw n w)).indicator 1) g₀ = 1 := by
    rw [hsumm, if_pos hg₀, GlobalTheory.TwOrbConj.relIndex_conj g₀ (twCent θ y₀) (twCent θ y) K _ hT rfl,
      (Subgroup.relIndex_eq_one).2 hcpt]
    simp
  rw [finsum_eq_single _ (DoubleCoset.mk (twCent θ y) K g₀)]
  · obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1
      (DoubleCoset.out_eq' (twCent θ y) K (DoubleCoset.mk (twCent θ y) K g₀)).symm
    rw [he, GlobalTheory.TwOrbConj.summand_rep θ K y _ g₀ ht hk, hval]
  · intro q hq
    rw [hsumm]
    split_ifs with hm
    · exfalso
      apply hq
      have hm' : (g₀⁻¹ * Quotient.out q)⁻¹ * y₀ * θ (g₀⁻¹ * Quotient.out q) ∈ K := by
        have e : (g₀⁻¹ * Quotient.out q)⁻¹ * y₀ * θ (g₀⁻¹ * Quotient.out q) = (Quotient.out q)⁻¹ * y * θ (Quotient.out q) := by
          rw [hy₀]; simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv]; group
        rw [e]; exact hm
      obtain ⟨t, ht, k, hk, he⟩ := huniq _ hm'
      have ht2 : g₀ * t * g₀⁻¹ ∈ twCent θ y := by
        rw [hT]; exact ⟨t, ht, by simp [MulAut.conj_apply]⟩
      symm
      conv_rhs => rw [← DoubleCoset.out_eq' (twCent θ y) K q]
      rw [DoubleCoset.eq]
      refine ⟨g₀ * t * g₀⁻¹, ht2, k, hk, ?_⟩
      calc Quotient.out q = g₀ * (g₀⁻¹ * Quotient.out q) := by group
        _ = g₀ * t * g₀⁻¹ * g₀ * k := by rw [he]; group
    · rfl

end GlobalTheory.UnitOrb
