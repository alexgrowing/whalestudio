import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.DatDatum
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.UmgOps
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.HkApply
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TsphVec

open private kgl_eq tj_eq hop_apply mem_fixL from Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.TsphVec

open MeasureTheory NumberField IsDedekindDomain GlobalTheory.CuspRep
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp GlobalTheory.LFun Formalism.UG

namespace UpperTheory.ConvolutionTheory.BW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ}
  {μ : Measure (normOneGL E n)} [μ.IsHaarMeasure] {v : LL μ} {φ : Sm E n}

private theorem out_eq (h : Umg φ) :
    (fun y : RightCosetSpace (rationalGLOne E n) => φ.1 ((Quotient.out y : normOneGL E n) : GA E n)) = cuspQuot h.left := by
  funext y
  conv_rhs => rw [← Quotient.out_eq y]
  rfl

private theorem cont_of (h : Rep μ v φ) : IsContRep μ v fun y => φ.1 (y : GA E n) := by
  refine ⟨(((umgOps E) n).2 φ h.umg).1.comp continuous_subtype_val, fun γ hγ y => ?_, ?_⟩
  · obtain ⟨γ', hγ'⟩ := Subgroup.mem_subgroupOf.1 hγ
    change φ.1 ((γ : AdelicGLn.AdelicGL E n) * y) = _
    rw [← hγ']
    exact h.umg.left γ' _
  · have e := h.ae
    rw [out_eq h.umg] at e
    filter_upwards [(quasiMeasurePreserving_mk _ μ).ae_eq e] with y hy
    exact hy.trans (cuspQuot_mk _ y)

private theorem of_cont (hu : Umg φ) (hc : ∀ t g, φ.1 (zt E n t * g) = φ.1 g)
    (h : IsContRep μ v fun y => φ.1 (y : GA E n)) : Rep μ v φ := by
  refine ⟨hu, hc, h.ae_eq_quotFun.trans (Filter.Eventually.of_forall fun y => ?_)⟩
  conv_lhs => rw [← Quotient.out_eq y]
  rfl

private theorem retr (h : Rep μ v φ) (x g : GA E n) : φ.1 (x * g) = φ.1 (x * (retractOne g : GA E n)) := by
  have e1 : g = (retractOne g : AdelicGLn.AdelicGL E n) * centralSection E n (detModule E n g) := by
    rw [coe_retractOne, inv_mul_cancel_right]
  have e2 : centralSection E n (detModule E n g) = zt E n (Real.log (detModule E n g).1) :=
    congrArg (centralSection E n) (Subtype.ext (Real.exp_log (detModule E n g).2).symm)
  conv_lhs => rw [e1, ← mul_assoc, ← centralSection_mul_comm, e2, h.cen]

private theorem rep_comb {v' : LL μ} {ψ : Sm E n} (h : Rep μ v φ) (c : ℂ) (h' : Rep μ v' ψ) :
    Rep μ (c • v + v') (c • φ + ψ) := by
  have hu := (((umgOps E) n).2 φ h.umg).2.2.1 c
  refine of_cont ((((umgOps E) n).2 _ hu).2.1 ψ h'.umg) (fun t g => ?_) (((cont_of h).smul c).add (cont_of h'))
  change c • φ.1 _ + ψ.1 _ = c • φ.1 _ + ψ.1 _
  rw [h.cen, h'.cen]

private theorem rep_zero : Rep μ 0 (0 : Sm E n) := of_cont ((umgOps E) n).1 (fun _ _ => rfl) isContRep_zero

private theorem rep_rt (h : Rep μ v φ) (g : GA E n) : Rep μ (RG μ g v) (rt E n g φ) := by
  refine of_cont ((((umgOps E) n).2 φ h.umg).2.2.2.2.1 g) (fun t x => ?_) ?_
  · change φ.1 (zt E n t * x * g) = φ.1 (x * g)
    rw [mul_assoc, h.cen]
  · have e : (fun y : normOneGL E n => (rt E n g φ).1 (y : GA E n)) =
        fun y : normOneGL E n => φ.1 ((y * retractOne g : normOneGL E n) : GA E n) := funext fun y => retr h y g
    rw [e]
    exact (cont_of h).translate (retractOne g)

private theorem rep_hecke (h : Rep μ v φ) (w : Pl E) {T : GL (Fin n) (w.adicCompletion E) → ℂ} (hT : T ∈ Hecke ℂ (KGL w n)) :
    Rep μ (heckeVec (localRepresentationL2 μ w) (KGL w n) T v) (heckeVec (rw n w) (KGL w n) T φ) := by
  classical
  have hf := Formalism.UG.P.finite_support_cosets (Final.GLintComm E w n) hT.2
  rw [heckeVec, heckeVec, finsum_eq_sum_of_support_subset (s := hf.toFinset) _ fun c hc => by
      rw [Set.Finite.coe_toFinset]; exact fun h0 => hc (by simp [h0]),
    finsum_eq_sum_of_support_subset (s := hf.toFinset) _ fun c hc => by
      rw [Set.Finite.coe_toFinset]; exact fun h0 => hc (by simp [h0])]
  induction hf.toFinset using Finset.induction_on with
  | empty => exact rep_zero
  | insert c s hc ih =>
    rw [Finset.sum_insert hc, Finset.sum_insert hc]
    exact rep_comb (rep_rt h _) _ ih

end UpperTheory.ConvolutionTheory.BW

theorem UpperTheory.ConvolutionTheory.BW.repOps :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.RepOps E := by
  intro E _ _ _ n μ _ _ v φ h
  refine ⟨fun ψ h' => Subtype.ext (funext fun g => ?_), fun v' ψ c h' => rep_comb h c h', fun hc r hr hrn => ?_,
    fun w i hw => ?_⟩
  · have e1 := retr h 1 g
    have e2 := retr h' 1 g
    rw [one_mul, one_mul] at e1 e2
    exact e1.trans ((congrFun ((cont_of h).unique (cont_of h')) (retractOne g)).trans e2.symm)
  · have e := h.ae
    rw [out_eq h.umg] at e
    filter_upwards [ae_ctFun_congr μ r e] with y hy
    rw [constantTermL2, hy]
    exact hc r hr hrn y
  · have hv : v ∈ fixL μ w (KGL w n) := (mem_fixL μ w _ v).2 fun k hk => by
      have h1 := rep_rt h (finGL E n (locGL E n w k))
      have e : rt E n (finGL E n (locGL E n w k)) φ = φ := hw k hk
      rw [e] at h1
      exact Lp.ext (h1.ae.trans h.ae.symm)
    have hϖ := (exists_isUnifV w).choose_spec
    have ht := tj_eq w hϖ (GroundTheory.BlockD.SatakeBound.valued_uniformizer_eq w) (i + 1)
      (Cartan.diagPow (w.adicCompletion E) n fun a => if a ≤ i then 1 else 0) (by
        rw [Cartan.coe_diagPow, diagJ]
        congr 1
        funext a
        by_cases ha : a ≤ i
        · rw [if_pos ha, if_pos (Nat.lt_succ_of_le ha), zpow_one]
        · rw [if_neg ha, if_neg (fun h' => ha (Nat.le_of_lt_succ h')), zpow_zero])
    have hq : (0 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero (qV_ne_zero w))
    have he : (qc w) ^ (((((i : ℕ) + 1 : ℕ) : ℂ) * ((n : ℂ) - (((i : ℕ) + 1 : ℕ) : ℂ))) / 2) =
        ((((Ideal.absNorm w.asIdeal : ℝ) ^ (-((((i : ℕ) + 1) * (n - ((i : ℕ) + 1)) : ℕ) : ℝ) / 2) : ℝ) : ℂ))⁻¹ := by
      rw [← Complex.ofReal_inv, ← Real.rpow_neg hq.le, Complex.ofReal_cpow hq.le, qc, qV]
      congr 1
      push_cast [Nat.cast_sub (Nat.succ_le_of_lt i.2)]
      ring
    rw [Tsph, ContinuousLinearMap.smul_apply, kgl_eq, hop_apply μ w _ _ (Final.GLintComm E w n) hv, ← ht,
      (hkOps E n w (i + 1)).1, he, inv_inv]
    simpa only [add_zero] using rep_comb (rep_hecke h w (Tj_mem_hecke hϖ (i + 1))) _ rep_zero
