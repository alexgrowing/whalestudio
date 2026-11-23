import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormOfGramMatrixAtHolomorphicFrameChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormOfGramMatrixAtCompHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder ComplexConjugate

namespace GlobalTheory.SecondChernPull

section Coordinates

open GlobalTheory.CxForm MvPolynomial

variable {n m : ℕ} {r : Type} [Fintype r] [DecidableEq r]

def subst (L : V n →L[ℂ] V m) : MvPolynomial (Fin m × Fin m) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
  aeval fun x : Fin m × Fin m => ∑ a, ∑ b, C (L (coordVec a) x.1 * conj (L (coordVec b) x.2)) * X (a, b)

theorem coe_aeval_sym_subst (L : V n →L[ℂ] V m) (q : MvPolynomial (Fin m × Fin m) ℂ) :
    ((aeval sym (subst L q) : Ev n) : Alt n) = pull L ((aeval sym q : Ev m) : Alt m) := by
  have h : ((Subalgebra.center ℂ (Alt n)).val.comp ((aeval sym).comp (subst L))) =
      (pull L).comp ((Subalgebra.center ℂ (Alt m)).val.comp (aeval sym)) := by
    refine MvPolynomial.algHom_ext fun x => ?_
    simp only [AlgHom.comp_apply, subst, aeval_X, map_sum, map_mul, aeval_C, Subalgebra.coe_val, sym,
      (pull_dz _ _).1, (pull_dz _ _).2, Finset.sum_mul_sum, smul_mul_smul_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, ← map_mul, ← Algebra.smul_def]
  exact DFunLike.congr_fun h q

theorem curv_eq_sum_sum {H : V m → Matrix r r ℂ} {y : V m} (h2 : MContDiffAt 2 H y) (hu : IsUnit (H y).det)
    (ξ η : V m) : curv H y ξ η = ∑ c, ∑ d, (ξ c * conj (η d)) • curv H y (coordVec c) (coordVec d) := by
  have e := GlobalTheory.ChernPull.curv_comp (H := H) (φ := fun x => x) (v := y) analyticAt_id h2 hu ξ η
  rw [fderiv_fun_id] at e
  refine e.trans (Finset.sum_congr rfl fun c _ => ?_)
  rw [GlobalTheory.ChernPull.curv_eq_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [smul_smul]; rfl

theorem curvPoly_comp {H : V m → Matrix r r ℂ} {φ : V n → V m} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) :
    curvPoly (fun x => H (φ x)) v = (curvPoly H (φ v)).map (subst (fderiv ℂ φ v)) := by
  have e (a b : Fin n) := (curv_comp_holo h2 hu hφ.contDiffAt (coordVec a) (coordVec b)).trans
    (curv_eq_sum_sum h2 hu _ _)
  refine Matrix.ext fun i j => ?_
  simp only [curvPoly, Matrix.of_apply, Matrix.map_apply, e, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, subst, aeval_X, aeval_C, algebraMap_eq,
    Finset.sum_mul, Finset.mul_sum]
  simp_rw [← Fintype.sum_prod_type']
  let e : Fin n × Fin n × Fin m × Fin m ≃ Fin m × Fin m × Fin n × Fin n :=
    ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun _ => rfl, fun _ => rfl⟩
  exact Fintype.sum_equiv e _ _ fun x => by simp only [e, Equiv.coe_fn_mk]; ring

theorem chernAt_comp_holo {H : V m → Matrix r r ℂ} {φ : V n → V m} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) (j : ℕ) :
    (chernAt (fun w => H (φ w)) v j : Alt n) = pull (fderiv ℂ φ v) (chernAt H (φ v) j : Alt m) := by
  have e : chernPoly (fun x => H (φ x)) v j = subst (fderiv ℂ φ v) (chernPoly H (φ v) j) := by
    unfold chernPoly
    rw [curvPoly_comp hφ h2 hu]
    have hm : -(curvPoly H (φ v)).map (subst (fderiv ℂ φ v)) =
        (-curvPoly H (φ v)).map (subst (fderiv ℂ φ v)).toRingHom := by
      rw [Matrix.map_neg (f := (subst (fderiv ℂ φ v)).toRingHom) (fun a => map_neg _ a)]; rfl
    rw [hm, ← GlobalTheory.ChernPull.charpolyRev_map, Polynomial.coeff_map]
    rfl
  rw [chernAt, chernAt, e, Subalgebra.coe_smul, Subalgebra.coe_smul, map_smul, coe_aeval_sym_subst]

theorem chernAt_reindex {r' : Type} [Fintype r'] [DecidableEq r'] (e : r' ≃ r)
    {G : V n → Matrix r r ℂ} {G' : V n → Matrix r' r' ℂ} {v : V n}
    (he : G' =ᶠ[𝓝 v] fun u => (G u).submatrix e e) (j : ℕ) : chernAt G' v j = chernAt G v j := by
  have e₁ : curvPoly G' v = (curvPoly G v).submatrix e e := by
    ext1 i j
    simp only [curvPoly, Matrix.of_apply, Matrix.submatrix_apply, curv_congr he, curv_submatrix_equiv]
  have e₂ (M : Matrix r r (MvPolynomial (Fin n × Fin n) ℂ)) :
      Matrix.charpolyRev (-M.submatrix e e) = Matrix.charpolyRev (-M) := by
    rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Matrix.det_submatrix_equiv_self e (1 - _)]
    congr 1
    ext1 i j
    simp [Matrix.one_apply]
  rw [chernAt, chernAt, chernPoly, chernPoly, e₁, e₂]

end Coordinates

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.LineForm

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}

theorem chern_G_eq (h : IsRegVar p D) {σ : k →+* ℂ} {E : X.Modules} {r : ℕ} {m : Met p σ E r} (H : m.IsCInf)
    (c c' : Chart E r) (x : (h.atlas σ).Pt) (hc : x.pt ∈ ptsIn p σ c.U) (hc' : x.pt ∈ ptsIn p σ c'.U) (j : ℕ) :
    (h.atlas σ).chern (m.G c') j x = (h.atlas σ).chern (m.G c) j x := by
  have e : x.ch.symm x.crd = x.pt := x.ch.left_inv x.2
  refine chernAt_changeFrame _ _ (fun v => c.tr p σ c' (x.ch.symm v)) _
    (((H c _ hc).mContDiffAt x.1.1 x.2).of_le (by norm_cast)) ?_ (fun a b => ?_) ?_ ?_ j
  · erw [e]; exact (isUnit_iff_isUnit_det _).1 (m.posDef c _ hc).isUnit
  · exact GlobalTheory.SCV.analyticAt_of_differentiableOn (AlgChart.holo x.1.1 _ _)
      ((ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds
        (ChartGlue.mem_over x.ch x.2 (mem_ptsIn_inf.2 ⟨hc', hc⟩)))
  · erw [e]; exact (isUnit_iff_isUnit_det _).1 (c.isUnit_tr c' hc hc')
  · filter_upwards [(ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds (ChartGlue.mem_over x.ch x.2 hc)] with v hv
    exact m.trans c c' _ hv.2

theorem c2F_eq_chern_of_mem_chart (h : IsRegVar p D) (σ : k →+* ℂ) {E : X.Modules} {m : VMetric p E 2} (H : m.IsCInf)
    (fl : Vert.Flag E 2) (c : Chart E 2) (x : (h.atlas σ).Pt) (hc : x.pt ∈ ptsIn p σ c.U) :
    c2F h σ m fl x = (h.atlas σ).chern ((m.met σ).G c) 2 x := by
  have hS := lineSC_shortExact fl
  have ha := mem_frameAt fl x.pt
  refine Eq.trans ?_ (chern_G_eq h (H σ) c ((frameAt fl x.pt).mid hS) x hc ha 2)
  refine chernAt_reindex (r := Fin 2) (finSumFinEquiv (m := 1) (n := 1)) ?_ 2
  filter_upwards [(ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds (ChartGlue.mem_over x.ch x.2 ha)] with v hv
  exact Met.gram_frame (S := lineSC fl) (r := 1) (s := 1) (m.met σ) hS _ hv.2

end GlobalTheory.SecondChernPull

end

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

open scoped ComplexOrder in
open GlobalTheory.Points GlobalTheory.HermFrame Filter Topology in

theorem GlobalTheory.SecondChernPull.c2F_pull_eq_pullF_c2F : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (Y : Scheme.{0}) (p' : Y ⟶ Sp k) (D' : ℕ) (hY : IsRegVar p' D') (π : Y ⟶ X) (w : π ≫ p = p'),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (fl' : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    fld _ (c2F hY σ (h.pull π w) fl') = pullF hX hY σ π w (fld _ (c2F hX σ h fl)) := by
  intro k _ X _ p D hX σ Y p' D' hY π w E h H fl fl'
  funext x
  set f : CxPts p' σ → CxPts p σ := PtsOver.map π w _ with hf
  have hm : ∀ z, (f z).1 = z.1 ≫ π := fun _ => rfl
  let x' : (hX.atlas σ).Pt := ⟨(_, f x.pt), ((hX.atlas σ).cover (f x.pt)).choose_spec⟩
  let c : Chart E 2 := (h.met σ).isVB.pick (f x.pt)
  have hc : f x.pt ∈ ptsIn p σ c.U := (h.met σ).isVB.mem_pick _
  change (c2F hY σ (h.pull π w) fl' x : Alt D') =
    pull (fderiv ℂ (x'.ch ∘ f ∘ x.ch.symm) x.crd) (c2F hX σ h fl x' : Alt D)
  rw [SecondChernPull.c2F_eq_chern_of_mem_chart hY σ (H.pull π w) fl' (c.pull (h.met σ).isVB π) x hc,
    SecondChernPull.c2F_eq_chern_of_mem_chart hX σ H fl c x' hc]
  have ho := ChartGlue.isOpen_over x.ch (x'.ch.open_source.preimage (continuous_of_comp hm))
  have hx := ho.mem_nhds (ChartGlue.mem_over x.ch x.2 (show x.pt ∈ f ⁻¹' x'.ch.source from x'.2))
  have hφ : AnalyticAt ℂ (x'.ch ∘ f ∘ x.ch.symm) x.crd :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (AlgChart.holo_map hm x.1.1 x'.1.1) hx
  have hv : (x'.ch ∘ f ∘ x.ch.symm) x.crd = x'.crd := congrArg (fun z => x'.ch (f z)) (x.ch.left_inv x.2)
  have key := SecondChernPull.chernAt_comp_holo (H := fun v => (h.met σ).G c (x'.ch.symm v)) hφ
    (by rw [hv]; exact ((H σ c _ hc).mContDiffAt x'.1.1 x'.2).of_le (by norm_cast))
    (by rw [hv, x'.ch.left_inv x'.2]; exact (Matrix.isUnit_iff_isUnit_det _).1 ((h.met σ).posDef c _ hc).isUnit) 2
  rw [hv] at key
  refine Eq.trans (congrArg Subtype.val (SecondChernPull.chernAt_reindex (Equiv.refl _) ?_ 2)) key
  filter_upwards [hx, (ChartGlue.isOpen_over x.ch ((isOpen_ptsIn c.U).preimage (continuous_of_comp hm))).mem_nhds
    (ChartGlue.mem_over x.ch x.2 (show x.pt ∈ f ⁻¹' ptsIn p σ c.U from hc))] with v h₁ h₂
  refine ((h.met σ).pull_G π w c h₂.2).trans ?_
  exact congrArg ((h.met σ).G c) (x'.ch.left_inv h₁.2).symm
