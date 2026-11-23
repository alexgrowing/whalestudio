import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineHomSec

variable {X : Scheme.{0}} {F Q : X.Modules} {U V W : X.Opens}

theorem eq_repr_smul (c : Chart F 1) (h : W ≤ c.U) (x : Γ(F, W)) :
    x = (c.isFrame.basis h).repr x 0 • resM F h (c.e 0) := by
  have := (c.isFrame.basis h).sum_repr x
  rw [Fin.sum_univ_one, IsFrame.basis_apply] at this
  exact this.symm

theorem smul_cancel (c : Chart F 1) (h : W ≤ c.U) {a b : Γ(X, W)}
    (e : a • resM F h (c.e 0) = b • resM F h (c.e 0)) : a = b := by
  rw [← c.isFrame.basis_apply h] at e
  have := congrArg (fun x => (c.isFrame.basis h).repr x 0) e
  simpa only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one] using this

theorem resM_frame (c c' : Chart F 1) (h : W ≤ c.U) (h' : W ≤ c'.U) :
    resM F h' (c'.e 0) = resG X (le_inf h h') ((det F 1).g c c').val • resM F h (c.e 0) := by
  have e : ((det F 1).g c c').val = (c.isFrame.basis (inf_le_left : c.U ⊓ c'.U ≤ c.U)).repr
      (resM F inf_le_right (c'.e 0)) 0 := by
    refine (c.isFrame.val_detUnit c'.isFrame inf_le_left inf_le_right).trans ?_
    rw [Module.Basis.det_apply, Matrix.det_fin_one, Module.Basis.toMatrix_apply]
  have := congrArg (resM F (le_inf h h'))
    (eq_repr_smul c (inf_le_left : c.U ⊓ c'.U ≤ c.U) (resM F inf_le_right (c'.e 0)))
  rw [resM_smul, resM_resM, resM_resM] at this
  rw [e]
  exact this

variable (s : F ⟶ Q)

def coef (c' : Chart F 1) (c : Chart Q 1) : Γ(X, c'.U ⊓ c.U) :=
  (c.isFrame.basis inf_le_right).repr (resM Q inf_le_left (s.app c'.U (c'.e 0))) 0

theorem app_frame (c' : Chart F 1) (c : Chart Q 1) (h' : W ≤ c'.U) (h : W ≤ c.U) :
    s.app W (resM F h' (c'.e 0)) = resG X (le_inf h' h) (coef s c' c) • resM Q h (c.e 0) := by
  have := congrArg (resM Q (le_inf h' h))
    (eq_repr_smul c (inf_le_right : c'.U ⊓ c.U ≤ c.U) (resM Q inf_le_left (s.app c'.U (c'.e 0))))
  rw [resM_smul, resM_resM, resM_resM] at this
  rw [app_resM]
  exact this

theorem coef_trans (c' d' : Chart F 1) (c d : Chart Q 1) (h' : W ≤ c'.U) (h : W ≤ c.U)
    (k' : W ≤ d'.U) (k : W ≤ d.U) :
    resG X (le_inf h' k') ((det F 1).g c' d').val * resG X (le_inf h' h) (coef s c' c) =
      resG X (le_inf h k) ((det Q 1).g c d).val * resG X (le_inf k' k) (coef s d' d) := by
  have e := app_frame s d' d k' k
  rw [resM_frame c' d' h' k', resM_frame c d h k, Scheme.Modules.Hom.app_smul,
    app_frame s c' c h' h, smul_smul, smul_smul] at e
  rw [smul_cancel c h e, mul_comm]

def sec : (CechPic.tens (CechPic.dual (det F 1)) (det Q 1)).Sec where
  f i := coef s i.1 i.2
  compat i j := by
    have e := coef_trans s (W := (i.1.U ⊓ i.2.U) ⊓ (j.1.U ⊓ j.2.U)) i.1 j.1 i.2 j.2
      (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
      (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)
    have h : (i.1.U ⊓ i.2.U) ⊓ (j.1.U ⊓ j.2.U) ≤ i.1.U ⊓ j.1.U := inf_le_inf inf_le_left inf_le_left
    exact ((res h ((det F 1).g i.1 j.1)).eq_inv_mul_iff_mul_eq.2 e).trans (mul_assoc _ _ _).symm

theorem eq_zero_of_coef (hF : IsVB F 1) (hQ : IsVB Q 1)
    (H : ∀ (c' : Chart F 1) (c : Chart Q 1) (z : X), z ∈ c'.U ⊓ c.U → coef s c' c = 0) : s = 0 := by
  ext V x
  choose U' e' hU' he' using hF
  choose U e hU he using hQ
  refine TopCat.Sheaf.eq_of_locally_eq' (C := Ab) ⟨Q.presheaf, Q.isSheaf⟩
    (fun z : V => V ⊓ (U' z ⊓ U z)) V (fun z => homOfLE inf_le_left)
    (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hz, hU' z, hU z⟩) (s.app V x) 0 fun z => ?_
  have h' : V ⊓ (U' z ⊓ U z) ≤ U' z := inf_le_right.trans inf_le_left
  have h : V ⊓ (U' z ⊓ U z) ≤ U z := inf_le_right.trans inf_le_right
  change resM Q inf_le_left (s.app V x) = resM Q inf_le_left 0
  rw [map_zero, ← app_resM, eq_repr_smul ⟨_, _, he' z⟩ h' (resM F _ x),
    Scheme.Modules.Hom.app_smul, app_frame s ⟨_, _, he' z⟩ ⟨_, _, he z⟩ h' h,
    H ⟨_, _, he' z⟩ ⟨_, _, he z⟩ z ⟨hU' z, hU z⟩, RingHom.map_zero, zero_smul, smul_zero]

theorem genericPoint_mem [IsIntegral X] (hF : IsVB F 1) (hQ : IsVB Q 1) (hs : s ≠ 0) :
    genericPoint X ∈ nonzeroLocus (sec s) := by
  by_contra hn
  refine hs (eq_zero_of_coef s hF hQ fun c' c z hz => ?_)
  have h := mt (mem_nonzeroLocus_iff (sec s) (c', c) (gen_mem hz)).2 hn
  refine basicOpen_eq_bot_iff (coef s c' c) |>.1 ?_
  by_contra hb
  obtain ⟨w, hw⟩ := (Opens.ne_bot_iff_nonempty _).1 hb
  exact h (gen_mem hw)

theorem vanishesAt (hF : IsVB F 1) {z : X} (hz : z ∉ nonzeroLocus (sec s)) : VanishesAt s z := by
  intro U t e b hU he hb hzb
  obtain ⟨U', e', hU', he'⟩ := hF z
  let c' : Chart F 1 := ⟨_, _, he'⟩
  let c : Chart Q 1 := ⟨_, _, he⟩
  have hm : z ∈ c'.U ⊓ c.U := ⟨hU', hU⟩
  refine hz ((mem_nonzeroLocus_iff (sec s) (c', c) hm).2 ?_)
  have h' : c'.U ⊓ c.U ≤ c'.U := inf_le_left
  have h : c'.U ⊓ c.U ≤ c.U := inf_le_right
  have e₁ := congrArg (resM Q h) hb
  rw [← app_resM, eq_repr_smul c' h' (resM F _ t), Scheme.Modules.Hom.app_smul,
    app_frame s c' c h' h, LB.resG_self, smul_smul, resM_smul] at e₁
  have e₂ := smul_cancel c h e₁
  have : z ∈ X.basicOpen (resG X h b) := by
    have := X.basicOpen_res b (homOfLE h).op
    exact this.ge ⟨hm, hzb⟩
  rw [← e₂, Scheme.basicOpen_mul] at this
  exact this.2

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem form_app (h : Met p σ Q 1) (c' : Chart F 1) (c : Chart Q 1) {y : CxPts p σ}
    (hy' : y ∈ ptsIn p σ c'.U) (hy : y ∈ ptsIn p σ c.U) :
    (h.form (s.app c'.U (c'.e 0)) (s.app c'.U (c'.e 0)) y).re =
      ‖ev p σ _ (coef s c' c) y‖ ^ 2 * (h.G c y).det.re := by
  have hW := mem_ptsIn_inf.2 ⟨hy', hy⟩
  rw [← h.form_resM _ _ inf_le_left hW, ← app_resM, app_frame s c' c inf_le_left inf_le_right,
    LB.resG_self, h.form_smul_left, ← h.conj_form, h.form_smul_left, map_mul, h.conj_form,
    h.form_resM _ _ _ hW, h.form_frame c hy, ← mul_assoc, Complex.mul_conj, Complex.re_ofReal_mul,
    Complex.normSq_eq_norm_sq, Matrix.det_fin_one]

theorem exists_ratSec : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (F Q : X.Modules) (g' : VMetric p F 1) (g : VMetric p Q 1) (H' : g'.IsCInf) (H : g.IsCInf) (s : F ⟶ Q), s ≠ 0 → ∃ (r : ((VMetric.det H').dual.tens (VMetric.det H)).B.ι → X.functionFieldˣ) (hr : IsRatSec ((VMetric.det H').dual.tens (VMetric.det H)).B r), (∀ z ∈ (((VMetric.det H').dual.tens (VMetric.det H)).div hr).supp, VanishesAt s z) ∧ ∀ σ : k →+* ℂ, ∀ y ∈ offSupp p σ (((VMetric.det H').dual.tens (VMetric.det H)).div hr), ∀ (U : X.Opens) (t : Γ(F, U)), IsFrame (fun _ : Fin 1 => t) → y ∈ ptsIn p σ U → 0 < ((g.met σ).form (s.app U t) (s.app U t) y).re ∧ logNorm (((VMetric.det H').dual.tens (VMetric.det H)).φ σ) r y = Real.log (((g.met σ).form (s.app U t) (s.app U t) y).re / ((g'.met σ).form t t y).re) / 2 := by
  intro k _ X p _ F Q g' g H' H s hs
  have hξ := genericPoint_mem s g'.isVB g.isVB hs
  let M := (VMetric.det H').dual.tens (VMetric.det H)
  let u : M.B.Sec := sec s
  refine ⟨ratOfSec u hξ, isRatSec_ratOfSec u hξ,
    fun z hz => vanishesAt s g'.isVB fun h => notMem_supp_divOfSec.2 h hz, ?_⟩
  intro σ y hy U t ht hU
  have hy' : y ∈ ptsIn p σ (nonzeroLocus u) := (offSupp_divOfSec (hL := M.isLB) (hs := hξ)).le hy
  let c' : Chart F 1 := ⟨_, _, ht⟩
  let c := g.isVB.pick y
  have hc : y ∈ ptsIn p σ c.U := g.isVB.mem_pick y
  have hi : y ∈ ptsIn p σ (M.B.U (c', c)) := mem_ptsIn_inf.2 ⟨hU, hc⟩
  have h0 : ev p σ _ (coef s c' c) y ≠ 0 := (secVal_ne_zero_iff u hi).2 hy'
  have hG := det_re_pos ((g.met σ).posDef c y hc)
  have hG' := det_re_pos ((g'.met σ).posDef c' y hU)
  have e : ((g.met σ).form (s.app U t) (s.app U t) y).re = _ := form_app s (g.met σ) c' c hU hc
  have e' : (g'.met σ).form t t y = ((g'.met σ).G c' y).det :=
    ((g'.met σ).form_frame c' hU 0 0).trans (Matrix.det_fin_one _).symm
  refine ⟨e ▸ by positivity, ?_⟩
  refine (logNorm_ratOfSec (s := u) (hs := hξ) (M.φ σ) hy').trans ?_
  rw [(M.φ σ).nsq_eq (secVal_mem u) hi, e, e']
  congr 2
  change ‖ev p σ _ (coef s c' c) y‖ ^ 2 * Real.exp (-(-(-Real.log ((g'.met σ).G c' y).det.re) +
    -Real.log ((g.met σ).G c y).det.re)) = _
  rw [neg_neg, ← sub_eq_add_neg, neg_sub, Real.exp_sub, Real.exp_log hG, Real.exp_log hG', mul_div_assoc]

end GlobalTheory.LineHomSec
