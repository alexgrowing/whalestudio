import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondCountableTopologySphere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcExtensionTraceChernForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubquotientCurvatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcEqOfLocalEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcOfValuesEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernAtOneEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfValuesMulOfValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnExtTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernAtTwoEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastMulCoeffCharpolyRev

set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.BcUnique.DdcTrace

variable {M : Type} [TopologicalSpace M] {n r s : ℕ} {A : HolAtlas M n}

def chartDom (T : HermSeq A r s) (a : T.κ) (i : A.ι) : Set (V n) := (A.e i).target ∩ (A.e i).symm ⁻¹' T.U a

theorem isOpen_chartDom (T : HermSeq A r s) (a : T.κ) (i : A.ι) : IsOpen (chartDom T a i) :=
  (A.e i).isOpen_inter_preimage_symm (T.isOpen a)

theorem isPosFrame_mid (T : HermSeq A r s) (a : T.κ) (i : A.ι) :
    IsPosFrame (chartDom T a i) (fun v => T.mid a ((A.e i).symm v)) :=
  ⟨isOpen_chartDom T a i, fun p q => (T.smooth a).2.1 p q i, fun _ hv => (T.posDef a _ hv.2).2.1⟩

theorem extTrace_mid_indep (T : HermSeq A r s) (a b : T.κ) (i : A.ι) {v : V n}
    (hv : v ∈ chartDom T a i ∩ chartDom T b i) :
    extTrace (fun w => T.mid a ((A.e i).symm w)) v = extTrace (fun w => T.mid b ((A.e i).symm w)) v := by
  have ho : IsOpen (chartDom T a i ∩ chartDom T b i) := (isOpen_chartDom T a i).inter (isOpen_chartDom T b i)
  have hs : chartDom T a i ∩ chartDom T b i = (A.e i).target ∩ (A.e i).symm ⁻¹' (T.U a ∩ T.U b) := by
    ext w; simp only [chartDom, mem_inter_iff, mem_preimage]; tauto
  have hd : ∀ p q, DifferentiableOn ℂ (fun w => T.g a b ((A.e i).symm w) p q) (chartDom T a i ∩ chartDom T b i) := by
    intro p q; rw [hs]; exact T.holo a b p q i
  have hA : MContDiffAt 1 (fun w => T.g a b ((A.e i).symm w)) v := fun p q =>
    (((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ ho (hd p q)).restrict_scalars ℝ).contDiffAt
      (ho.mem_nhds hv)).of_le (by norm_cast)
  have hA0 : ∀ η, mdbar (fun w => T.g a b ((A.e i).symm w)) v η = 0 := by
    intro η
    ext p q
    rw [mdbar_apply, dbar_eq_zero ((hd p q).differentiableAt (ho.mem_nhds hv))]
    rfl
  have e : (fun w => T.mid b ((A.e i).symm w)) =ᶠ[𝓝 v]
      fun w => chg (T.g a b ((A.e i).symm w)) (T.mid a ((A.e i).symm w)) :=
    Filter.eventually_of_mem (ho.mem_nhds hv) fun w hw => (T.trans a b _ ⟨hw.1.2, hw.2.2⟩).2.1
  have ht : ∀ᶠ w in 𝓝 v, (T.g a b ((A.e i).symm w)).toBlocks₂₁ = 0 :=
    Filter.eventually_of_mem (ho.mem_nhds hv) fun w hw => T.tri a b _ ⟨hw.1.2, hw.2.2⟩
  have hK : MContDiffAt 1 (fun w => T.mid a ((A.e i).symm w)) v := (isPosFrame_mid T a i).isHermFrame.one hv.1
  have hp : ∀ᶠ w in 𝓝 v, (T.mid a ((A.e i).symm w)).PosDef :=
    Filter.eventually_of_mem ((isOpen_chartDom T a i).mem_nhds hv.1) fun w hw => (isPosFrame_mid T a i).posDef w hw
  have hu : IsUnit (T.g a b ((A.e i).symm v)).det := by
    have ha : (A.e i).symm v ∈ T.U a := hv.1.2
    have hb : (A.e i).symm v ∈ T.U b := hv.2.2
    have h1 : T.g a b ((A.e i).symm v) * T.g b a ((A.e i).symm v) = 1 := by
      rw [T.g_mul a b a _ ⟨⟨ha, hb⟩, ha⟩, T.g_self a _ ha]
    exact Matrix.isUnit_det_of_right_inverse h1
  rw [extTrace_congr e, extTrace_chg hK hp hA hu hA0 ht]

theorem loc_bcFld (T : HermSeq A r s) {a : T.κ} {i : A.ι} {v : V n} (hv : v ∈ chartDom T a i) :
    A.loc (bcFld T) i v = (ofValues (extTrace (fun w => T.mid a ((A.e i).symm w)) v) : Alt n) := by
  rw [HolAtlas.loc, dif_pos hv.1]
  have hc : (A.e i) ((A.e i).symm v) = v := (A.e i).right_inv hv.1
  change (ofValues (extTrace (fun w => T.mid (T.cover ((A.e i).symm v)).choose ((A.e i).symm w))
    ((A.e i) ((A.e i).symm v))) : Alt n) = _
  rw [hc, extTrace_mid_indep T _ a i ⟨⟨hv.1, (T.cover _).choose_spec⟩, hv⟩]

theorem chernAt_congr {q : Type} [Fintype q] [DecidableEq q] {G G' : V n → Matrix q q ℂ} {v : V n}
    (h : G =ᶠ[𝓝 v] G') (j : ℕ) : chernAt G v j = chernAt G' v j := by
  simp only [chernAt, GlobalTheory.GoodMetric.chernPoly, GlobalTheory.GoodMetric.curvPoly, curv_congr h]

theorem two_mul_coeff_two {R : Type} [CommRing R] {q : Type} [Fintype q] [DecidableEq q] (F : Matrix q q R) :
    2 * (Matrix.charpolyRev (-F)).coeff 2 = ∑ a, ∑ b, (F a a * F b b - F a b * F b a) := by
  have e := Fintype.equivFin q
  have h0 : ((-F).submatrix e.symm e.symm).charpolyRev = (-F).charpolyRev := by
    rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Matrix.det_submatrix_equiv_self e.symm]
    congr 1
    ext i j
    simp [Matrix.one_apply]
  have hz : (-F).charpolyRev.coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  have h1 := GlobalTheory.natCast_mul_coeff_charpolyRev ((-F).submatrix e.symm e.symm) 1
  have h2 := GlobalTheory.natCast_mul_coeff_charpolyRev ((-F).submatrix e.symm e.symm) 2
  have t1 : ((-F).submatrix e.symm e.symm).trace = -∑ a, F a a := by
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply, Matrix.neg_apply, Finset.sum_neg_distrib]
    rw [e.symm.sum_comp (fun a => F a a)]
  have t2 : (((-F).submatrix e.symm e.symm) ^ 2).trace = ∑ a, ∑ b, F a b * F b a := by
    rw [pow_two, Matrix.submatrix_mul_equiv, neg_mul_neg]
    simp only [Matrix.trace, Matrix.diag, Matrix.submatrix_apply, Matrix.mul_apply]
    rw [e.symm.sum_comp (fun a => ∑ b, F a b * F b a)]
  rw [h0] at h1 h2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_one, Nat.cast_one, one_mul, Nat.cast_ofNat,
    Nat.reduceAdd, Nat.reduceSub, Nat.sub_zero, hz, mul_one, t1, t2] at h1 h2
  rw [h2, h1]
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul_sum]
  ring

theorem four_sum {ι : Type} (t : Finset ι) (f : ι → Fin n → Fin n → Fin n → Fin n → ℂ) :
    GlobalTheory.SecForm.ChernTwo.four (fun a b c d => ∑ i ∈ t, f i a b c d) = ∑ i ∈ t, GlobalTheory.SecForm.ChernTwo.four (f i) := by
  simp only [GlobalTheory.SecForm.ChernTwo.four_eq, Finset.sum_smul]
  exact Finset.sum_comm

open GlobalTheory.SecForm.ChernTwo in

theorem chernAt_two {q : Type} [Fintype q] [DecidableEq q] (G : V n → Matrix q q ℂ) (v : V n) :
    chernAt G v 2 = GlobalTheory.SecForm.ofValuesTwo (chernTwo G v) := by
  have e : GlobalTheory.SecForm.ofValuesTwo (chernTwo G v) = (1 / 4 : ℂ) • four fun a b c d =>
      kappa ^ 2 * (1 / 2 * ∑ i, ∑ j, curvMinor G v i j (coordVec a) (coordVec b) (coordVec c) (coordVec d)) := rfl
  have h := congrArg (MvPolynomial.aeval (R := ℂ) (sym (n := n))) (two_mul_coeff_two (GlobalTheory.GoodMetric.curvPoly G v))
  simp only [map_mul, map_sum, map_sub, map_ofNat, aeval_curvPoly] at h
  rw [e, four_mul, four_mul, four_sum]
  simp only [four_sum, curvMinor, four_sub, four_wedge, ← smul_sub, ← Finset.smul_sum]
  rw [← h, chernAt, GlobalTheory.GoodMetric.chernPoly, two_mul]
  module

theorem ofValuesTwo_comb (P Q R S : V n → V n → V n → V n → ℂ) :
    GlobalTheory.SecForm.ofValuesTwo (fun a b c d => P a b c d - Q a b c d - R a b c d - S a b c d) =
      GlobalTheory.SecForm.ofValuesTwo P - GlobalTheory.SecForm.ofValuesTwo Q - GlobalTheory.SecForm.ofValuesTwo R -
        GlobalTheory.SecForm.ofValuesTwo S := by
  simp only [GlobalTheory.SecForm.ofValuesTwo, sub_smul, Finset.sum_sub_distrib, smul_sub]

end GlobalTheory.BcUnique.DdcTrace

namespace GlobalTheory.BcUnique.DdcTrace

open GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms GlobalTheory.SecForm in

theorem ddc_extTrace {n : ℕ} {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set (V n)}
    {H : V n → Matrix (m ⊕ l) (m ⊕ l) ℂ} (hP : IsPosFrame U H) {z : V n} (hz : z ∈ U) :
    kappa • delAt (dbarAt fun v => (ofValues (extTrace H v) : Alt n)) z =
      ((-(chernAt (gramS H) z 2 + chernAt (gramS H) z 1 * chernAt (gramQ H) z 1 + chernAt (gramQ H) z 2 -
        chernAt H z 2) : Ev n) : Alt n) := by
  have h2 : ∀ p q, ContDiffAt ℝ 2 (fun w => extTrace H w (coordVec p) (coordVec q)) z := fun p q =>
    ((contDiffOn_extTrace hP _ _).contDiffAt (hP.isOpen.mem_nhds hz)).of_le (by norm_cast)
  have hh := hP.isHermFrame
  have hs : ∀ w ∈ U, IsUnit (subGram (H w)).det := fun w hw =>
    (posDef_subGram (hP.posDef w hw)).det_pos.ne'.isUnit
  have hd : ddcForm (extTrace H) z = fun ξ₁ η₁ ξ₂ η₂ => chernTwo H z ξ₁ η₁ ξ₂ η₂ - chernTwo (gramS H) z ξ₁ η₁ ξ₂ η₂ -
      chernTwo (gramQ H) z ξ₁ η₁ ξ₂ η₂ - wedge (chernOne (gramS H) z) (chernOne (gramQ H) z) ξ₁ η₁ ξ₂ η₂ := by
    funext ξ₁ η₁ ξ₂ η₂
    rw [GlobalTheory.SubQuotChTwo.ddcForm_extTrace_eq hh hs hz (fun w hw => GlobalTheory.SubQuotCurv.extBlocksAt hh hs hw),
      chTwo_eq, chTwo_eq, chTwo_eq]
    simp only [wedge, GlobalTheory.SubQuotCurv.chernOne_add hh hs hz]
    ring
  rw [ddc_ofValues _ _ h2, hd, ofValuesTwo_comb, chernAt_two, chernAt_two, chernAt_two, chernAt_one_eq_ofValues,
    chernAt_one_eq_ofValues, ofValues_mul_ofValues]
  congr 1
  abel

end GlobalTheory.BcUnique.DdcTrace

section Main

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory OnePoint
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real ComplexOrder

open GlobalTheory.BcUnique.DdcTrace in

theorem GlobalTheory.BcUnique.ddc_bcFld : ∀ {M : Type} [TopologicalSpace M] {n r s : ℕ} (A : HolAtlas M n) (T : HermSeq A r s),
    IsInduced T → ∀ (a : T.κ) (x : A.Pt), x.pt ∈ T.U a → A.ddc (bcFld T) x =
      ((-(A.chern (T.sub a) 2 x + A.chern (T.sub a) 1 x * A.chern (T.quot a) 1 x + A.chern (T.quot a) 2 x -
        A.chern (T.mid a) 2 x)) : Ev n) := by
  intro M _ n r s A T hI a x hx
  have hv : x.crd ∈ chartDom T a x.1.1 :=
    ⟨x.ch.map_source x.2, by simp only [mem_preimage]; rw [x.ch.left_inv x.2]; exact hx⟩
  have hP := isPosFrame_mid T a x.1.1
  have hU := (isOpen_chartDom T a x.1.1).mem_nhds hv
  have hev : A.loc (bcFld T) x.1.1 =ᶠ[nhds x.crd]
      fun v => (ofValues (GlobalTheory.HermFrame.extTrace (fun w => T.mid a ((A.e x.1.1).symm w)) v) : Alt n) :=
    Filter.eventually_of_mem hU fun w hw => loc_bcFld T hw
  have eS : (fun w => T.sub a (x.ch.symm w)) =ᶠ[nhds x.crd]
      GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms.gramS (fun w => T.mid a ((A.e x.1.1).symm w)) :=
    Filter.eventually_of_mem hU fun w hw => (hI a _ hw.2).1
  have eQ : (fun w => T.quot a (x.ch.symm w)) =ᶠ[nhds x.crd]
      GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms.gramQ (fun w => T.mid a ((A.e x.1.1).symm w)) :=
    Filter.eventually_of_mem hU fun w hw => (hI a _ hw.2).2
  rw [GlobalTheory.SecForm.DdcGerm.ddc_eq_of_eventuallyEq A _ x _ hev, ddc_extTrace hP hv]
  simp only [HolAtlas.chern, chernAt_congr eS, chernAt_congr eQ]

end Main

end
