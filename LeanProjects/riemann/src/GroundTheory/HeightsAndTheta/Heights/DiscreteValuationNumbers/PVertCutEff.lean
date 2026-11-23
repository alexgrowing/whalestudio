import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivisorIdealBotUniformiser
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRepresentative
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleFiniteSupport
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimStrictDrop
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialQuotDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealCorresp
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialDimBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Helpers

variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]

theorem exists_form_pair_left {P H : Ideal (MRing ι R)} [hP : P.IsPrime]
    (hPm : IsMultiHomogIdeal P) (hPH : P ≤ H) {f g u v : MRing ι R} {bf bg : K → ℕ}
    (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg) (hfP : f ∉ P) (hu : u ∉ H)
    (h : u * f - v * g ∈ P) :
    ∃ (u' v' : MRing ι R) (e d : K → ℕ), IsMultiHomog u' e ∧ IsMultiHomog v' d ∧
      d + bg = e + bf ∧ u' ∉ H ∧ u' * f - v' * g ∈ P := by
  classical
  obtain ⟨e, he⟩ := exists_component_not_mem hu
  set u' := weightedHomogeneousComponent (blockWeight ι) e u with hu'
  have hc := hPm _ h (e + bf)
  rw [map_sub, weightedHomogeneousComponent_mul_form hf, weightedHomogeneousComponent_mul_form hg,
    if_pos le_add_self, add_tsub_cancel_right, ← hu'] at hc
  by_cases hle : bg ≤ e + bf
  · rw [if_pos hle] at hc
    exact ⟨u', _, e, e + bf - bg, weightedHomogeneousComponent_isWeightedHomogeneous _ _,
      weightedHomogeneousComponent_isWeightedHomogeneous _ _, tsub_add_cancel_of_le hle, he, hc⟩
  · rw [if_neg hle, sub_zero] at hc
    exact ((hP.mem_or_mem hc).elim (fun h' => he (hPH h')) hfP).elim

end Helpers

theorem VertCutEff.proof (h1 : VNumCut.Statement.{u}) (h2 : DivisorIdealCycle.Statement.{u})
    (h3 : IntNumAddFirst.Statement.{u}) : VertCutEff.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P n hmodel b f g hE W x hxP hWmin hrel hWmh hϖW hcyc L
  have hP : P.IsPrime := hmodel.multiProj.isPrime
  have hWp : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  obtain ⟨hV, hreg⟩ := hE
  obtain ⟨bf, bg, hf, hg, hb⟩ := hV.degrees
  obtain ⟨u₀, v₀, hu₀, h₀⟩ := hreg W hWp hPW hrel
  obtain ⟨u, v, e, d, hu, hv, hde, huW, huv⟩ :=
    exists_form_pair_left hmodel.multiProj.multiHomog hPW hf hg hV.num_not_mem hu₀ h₀
  have huP : u ∉ P := fun h => huW (hPW h)

  have hvW : v ∉ W := by
    intro hvW
    have hvP : v ∉ P := by
      intro hvP
      have hufP : u * f ∈ P := by
        have h' := P.add_mem huv (P.mul_mem_right g hvP)
        rwa [sub_add_cancel] at h'
      exact (hP.mem_or_mem hufP).elim huP hV.num_not_mem
    have hmul := mem_minimalPrimes_sup_span_mul (P := P) (x := x) (y := v) hvP hWmin
    have hWv : W ∈ (P ⊔ Ideal.span {v}).minimalPrimes :=
      ⟨⟨hWp, sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hvW)⟩, fun Q hQ hQW =>
        hmul.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2) ((Ideal.span_singleton_le_iff_mem _).mpr
          (Q.mul_mem_left x (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self v)))))⟩ hQW⟩
    have hpos : divCycle P v W ≠ 0 := by
      unfold divCycle
      rw [dif_pos ⟨hWv, hrel⟩]
      have hne := length_localizedQuot_ne_top (P ⊔ Ideal.span {v}) W hWv
      have hnz : multAt (P ⊔ Ideal.span {v}) W ≠ 0 := by
        unfold multAt
        rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
        intro hs
        obtain ⟨r, hr, hr0⟩ := hs (Ideal.Quotient.mk _ 1)
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one,
          Ideal.Quotient.eq_zero_iff_mem] at hr0
        exact hr (hWv.1.2 hr0)
      have htn : (multAt (P ⊔ Ideal.span {v}) W).toNat ≠ 0 :=
        fun h0 => (ENat.toNat_eq_zero.mp h0).elim hnz hne
      exact_mod_cast htn
    have hu0 : divCycle P u W = 0 := by
      unfold divCycle
      rw [dif_neg]
      rintro ⟨h, -⟩
      exact huW (h.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self u)))
    have e1 := congrFun (DivCycleMul.proof O K ι P u f hP huP hV.num_not_mem) W
    have e2 := congrFun (DivCycleMul.proof O K ι P v g hP hvP hV.den_not_mem) W
    have e3 := congrFun (divCycle_eq_of_sub_mem huv) W
    simp only [Pi.add_apply] at e1 e2
    unfold ratDiv at hcyc
    omega

  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hmodel.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'
  have hlt : P < W := lt_of_le_of_ne hPW (fun h => hϖP (h ▸ hϖW))
  have hdim : ringKrullDim (MRing ι O ⧸ W) < ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    have h' := DimStrictDrop.proof (MRing ι O) P W hlt
    rw [hmodel.dim, show n + 1 + 1 + Fintype.card K = n + 2 + Fintype.card K by omega] at h'
    exact withBotENat_lt_of_add_one_le h'

  have hcu := h1 O ϖ hϖ K ι W n hWp hWmh hϖW hdim u e hu huW L
  have hcv := h1 O ϖ hϖ K ι W n hWp hWmh hϖW hdim v d hv hvW L
  have hWbar : (specialIdeal W).IsPrime := (SpecialIdealCorresp.proof O ϖ hϖ K ι P W hWp hϖW).1
  have hadd := h3 (IsLocalRing.ResidueField O) K ι n (specialIdeal W) hWbar
    (SpecialIdealMultiHomog.proof O K ι W hWmh)
    (by rw [SpecialQuotDim.proof O ϖ hϖ K ι W hϖW]; exact hdim) b (fun k => (e k : ℤ)) L
  have hdeg : (fun k => (d k : ℤ)) = b + fun k => (e k : ℤ) := by
    rw [← hb]
    funext k
    have hk := congrFun hde k
    simp only [Pi.add_apply] at hk ⊢
    omega
  have key : vNum W (Matrix.vecCons b L) = vNum W (Matrix.vecCons (fun k => (d k : ℤ)) L) -
      vNum W (Matrix.vecCons (fun k => (e k : ℤ)) L) := by
    rw [hdeg]
    unfold vNum
    rw [hadd]
    ring
  rw [key, hcv, hcu, ← h2 O K ι P W f g u v hP hWp hPW hV.den_not_mem
    (fun U hU hWU hUrel => hreg U hU (hPW.trans hWU) hUrel) huW hvW huv]

  unfold cycEval ratDiv
  rw [← finsum_sub_distrib
    ((DivCycleFiniteSupport.proof O K ι W v).subset (Function.support_mul_subset_left _ _))
    ((DivCycleFiniteSupport.proof O K ι W u).subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun U => ?_
  ring

end

end GroundTheory.Heights₂.Heights.NumbersDVR
