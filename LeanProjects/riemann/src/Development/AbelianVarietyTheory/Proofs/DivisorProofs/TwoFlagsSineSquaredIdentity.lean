import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoFlagRationalSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernIsometricEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocal
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocalLelong

open Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.HermFrame (kappa)

section Point

variable {n : ℕ}

theorem del_mul_dbar {F φ₁ φ₀ : V n → ℝ} {g : V n → ℂ} {z : V n} (hg : ContDiffAt ℂ 2 g z)
    (h₁ : ContDiffAt ℝ 2 φ₁ z) (h₀ : ContDiffAt ℝ 2 φ₀ z)
    (e : F =ᶠ[𝓝 z] fun u => ‖g u‖ ^ 2 * Real.exp (-(φ₁ u - φ₀ u))) :
    ContDiffAt ℝ 2 F z ∧ ∀ ξ η : V n, del (fun u => (F u : ℂ)) z ξ * dbar (fun u => (F u : ℂ)) z η =
      F z * (leviForm F z ξ η + F z * (leviForm φ₁ z ξ η - leviForm φ₀ z ξ η)) := by
  have hn : ContDiffAt ℝ 2 (fun u => ‖g u‖ ^ 2) z := (hg.restrict_scalars ℝ).norm_sq ℂ
  have hF : ContDiffAt ℝ 2 F z := (hn.mul (h₁.sub h₀).neg.exp).congr_of_eventuallyEq e
  refine ⟨hF, fun ξ η => ?_⟩
  by_cases h : g z = 0
  · have hz : F z = 0 := by rw [e.self_of_nhds]; simp [h]
    have hm : IsLocalMin F z := e.mono fun u hu => by rw [hz, hu]; positivity
    have hd := hF.differentiableAt two_ne_zero
    rw [hz, del_apply, fderiv_ofReal_apply hd, fderiv_ofReal_apply hd, hm.fderiv_eq_zero]
    simp
  · have hz : F z ≠ 0 := by rw [e.self_of_nhds]; positivity
    have hl : ContDiffAt ℝ 2 (fun u => Real.log (‖g u‖ ^ 2)) z := hn.log (by simpa using h)
    have e₁ : (fun u => Real.log (F u)) =ᶠ[𝓝 z] fun u => Real.log (‖g u‖ ^ 2) - (φ₁ u - φ₀ u) := by
      filter_upwards [e, hg.continuousAt.eventually_ne h] with u hu hu'
      rw [hu, Real.log_mul (by positivity) (by positivity), Real.log_exp, sub_eq_add_neg _ (_ - _)]
    have e₂ := leviForm_real_comp (h := Real.log) (Real.contDiffAt_log.2 hz) hF ξ η
    rw [leviForm_congr e₁, leviForm_sub hl (h₁.sub h₀), leviForm_log_normSq_eq_zero hg h, leviForm_sub h₁ h₀,
      Real.deriv_log', deriv_inv] at e₂
    have hz' : (F z : ℂ) ≠ 0 := by exact_mod_cast hz
    simp only [zero_sub, ContinuousLinearMap.neg_apply, ContinuousLinearMap.sub_apply] at e₂
    push_cast at e₂
    field_simp at e₂
    linear_combination e₂

theorem delAt_fun (u : V n → ℂ) (v : V n) :
    delAt (fun x => algebraMap ℂ (Alt n) (u x)) v = ∑ a, del u v (coordVec a) • dz a := by
  simp only [delAt, Algebra.algebraMap_eq_smul_one, ← bas_empty]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coefwise_smul (by simp), bas_empty, mul_smul_comm, mul_one]

theorem dbarAt_fun (u : V n → ℂ) (v : V n) :
    dbarAt (fun x => algebraMap ℂ (Alt n) (u x)) v = ∑ a, dbar u v (coordVec a) • dzb a := by
  simp only [dbarAt, Algebra.algebraMap_eq_smul_one, ← bas_empty]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coefwise_smul (by simp), bas_empty, mul_smul_comm, mul_one]

theorem coe_ofValues (α : V n → V n → ℂ) :
    (ofValues α : Alt n) = ∑ a, ∑ b, α (coordVec a) (coordVec b) • (dz a * dzb b) := by
  simp only [ofValues, AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, sym]

theorem delAt_mul_dbarAt {F φ₁ φ₀ : V n → ℝ} {g : V n → ℂ} {z : V n} (hg : ContDiffAt ℂ 2 g z)
    (h₁ : ContDiffAt ℝ 2 φ₁ z) (h₀ : ContDiffAt ℝ 2 φ₀ z)
    (e : F =ᶠ[𝓝 z] fun u => ‖g u‖ ^ 2 * Real.exp (-(φ₁ u - φ₀ u))) :
    kappa • (delAt (fun x => algebraMap ℂ (Alt n) (F x)) z * dbarAt (fun x => algebraMap ℂ (Alt n) (F x)) z) =
      algebraMap ℂ (Alt n) (F z) * (kappa • delAt (dbarAt fun x => algebraMap ℂ (Alt n) (F x)) z +
        algebraMap ℂ (Alt n) (F z) * ((ofValues (HermFrame.ddc φ₁ z) : Alt n) - ofValues (HermFrame.ddc φ₀ z))) := by
  obtain ⟨hF, key⟩ := del_mul_dbar hg h₁ h₀ e
  rw [delAt_dbarAt_fun hF, delAt_fun, dbarAt_fun, ← Algebra.smul_def, ← Algebra.smul_def, Finset.sum_mul_sum]
  simp only [coe_ofValues, smul_mul_smul_comm, key, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    Finset.smul_sum, smul_smul, ← sub_smul, ← add_smul, HermFrame.ddc]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ring

end Point

theorem del_mul_dbar_fn {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (f : M → ℝ) (x : A.Pt)
    {φ₁ φ₀ : V n → ℝ} {g : V n → ℂ} (hg : ContDiffAt ℂ 2 g x.crd)
    (h₁ : ContDiffAt ℝ 2 φ₁ x.crd) (h₀ : ContDiffAt ℝ 2 φ₀ x.crd)
    (e : (fun u => f (x.ch.symm u)) =ᶠ[𝓝 x.crd] fun u => ‖g u‖ ^ 2 * Real.exp (-(φ₁ u - φ₀ u))) :
    kappa • (A.del (A.fn f) x * A.dbar (A.fn f) x) = A.fn f x * (A.ddc (A.fn f) x +
      A.fn f x * ((ofValues (HermFrame.ddc φ₁ x.crd) : Alt n) - ofValues (HermFrame.ddc φ₀ x.crd))) := by
  have hc : x.crd ∈ x.ch.target := x.ch.map_source x.2
  have l₁ (v) (hv : v ∈ x.ch.target) : A.loc (A.fn f) x.1.1 =ᶠ[𝓝 v]
      fun u => algebraMap ℂ (Alt n) (f (x.ch.symm u)) := by
    filter_upwards [x.ch.open_target.mem_nhds hv] with u hu
    rw [HolAtlas.loc, dif_pos hu]
    rfl
  have l₂ : A.loc (A.dbar (A.fn f)) x.1.1 =ᶠ[𝓝 x.crd] dbarAt fun u => algebraMap ℂ (Alt n) (f (x.ch.symm u)) := by
    filter_upwards [x.ch.open_target.mem_nhds hc] with u hu
    rw [HolAtlas.loc, dif_pos hu, ← ((delAt_dbarAt_linear_local n u).2.2.2.1 _ _ (l₁ u hu)).2]
    exact congrArg (dbarAt _) (x.ch.right_inv hu)
  have key := delAt_mul_dbarAt hg h₁ h₀ e
  rw [← ((delAt_dbarAt_linear_local n _).2.2.2.1 _ _ l₂).1, ← ((delAt_dbarAt_linear_local n _).2.2.2.1 _ _ (l₁ _ hc)).1,
    ← ((delAt_dbarAt_linear_local n _).2.2.2.1 _ _ (l₁ _ hc)).2, x.ch.left_inv x.2] at key
  exact key

section Lines

open GlobalTheory.VMetric GlobalTheory.CurveDens
open GlobalTheory.Twist (resM resM_resM)
open scoped ComplexOrder

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem isFrame_resM {F : X.Modules} (c : Chart F 1) {U : X.Opens} (h : U ≤ c.U) :
    IsFrame fun _ : Fin 1 => resM F h (c.e 0) := fun W hW => by
  convert c.isFrame W (hW.trans h) using 3
  funext i
  rw [resM_resM, Subsingleton.elim i 0]

theorem form_frame_eq_exp {F : X.Modules} (m : Met p σ F 1) (c : Chart F 1) {U : X.Opens} (h : U ≤ c.U) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ U) :
    (m.form (resM F h (c.e 0)) (resM F h (c.e 0)) y).re = Real.exp (-m.detWeight.φ c y) := by
  have hc := ptsIn_mono h hy
  have hp := (Complex.pos_iff.1 ((m.posDef c y hc).diag_pos (i := 0))).1
  rw [m.form_resM _ _ h hy, m.form_frame c hc]
  change _ = Real.exp (- -Real.log (m.G c y).det.re)
  rw [neg_neg, Matrix.det_fin_one, Real.exp_log hp]

theorem two_flags [IsIntegral X] {D : ℕ} (hX : IsRegVar p D) {W : X.Modules} {h : VMetric p W 2} (H : h.IsCInf)
    (fl fl' : Vert.Flag W 2) {v : CxPts p σ → ℝ} (hv : IsCosSq (h.met σ) (fl.ι 1) (fl'.ι 1) v) (x : (hX.atlas σ).Pt) :
    kappa • ((hX.atlas σ).del ((hX.atlas σ).fn fun y => 1 - v y) x * (hX.atlas σ).dbar ((hX.atlas σ).fn fun y => 1 - v y) x) =
      (hX.atlas σ).fn (fun y => 1 - v y) x * ((hX.atlas σ).ddc ((hX.atlas σ).fn fun y => 1 - v y) x +
        (hX.atlas σ).fn (fun y => 1 - v y) x *
          ((c1F hX σ (grLB fl' 1 H) x : Alt D) - c1F hX σ (grLB fl 0 H) x)) := by
  have hS := shortExact_lineQuot fl'
  have hL := fl'.isVB 1
  have hL' := fl.isVB 1
  have hQ := fl'.isVB_gr 1
  have hl := fl'.isSubbundle 1
  have hl' := fl.isSubbundle 1
  have HQ := IsCInf.quot (S := .mk _ _ (line_lineQuot fl')) (r := 1) (s := 1) hS hL hQ H
  rw [← c1F_eq_of_isometric k X p D hX σ _ _ (isometric_grLB_zero H fl),
    ← c1F_eq_of_isometric k X p D hX σ _ _ (isometric_grLB_one H fl')]
  obtain ⟨⟨c, y⟩, hy⟩ := x
  have hy' : y ∈ c.e.source := hy
  let a : Chart (fl'.F 1) 1 := hL.pick y
  let b : Chart (fl.F 1) 1 := hL'.pick y
  let e : Chart (fl'.gr 1) 1 := hQ.pick y
  let U : X.Opens := a.U ⊓ (b.U ⊓ e.U)
  have ha : U ≤ a.U := inf_le_left
  have hb : U ≤ b.U := inf_le_right.trans inf_le_left
  have he : U ≤ e.U := inf_le_right.trans inf_le_right
  have hU : y ∈ ptsIn p σ U := mem_ptsIn_inf.2 ⟨hL.mem_pick y, mem_ptsIn_inf.2 ⟨hL'.mem_pick y, hQ.mem_pick y⟩⟩
  obtain ⟨g, hg⟩ := exists_smul_frame e le_rfl he ((fl.ι 1 ≫ lineQuot fl').app U (resM _ hb (b.e 0)))
  rw [resM_resM] at hg
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) U)
  have hm := ChartGlue.mem_over c.e hy' hU
  have hf : ContDiffAt ℂ 2 (ev p σ _ g ∘ c.e.symm) (c.e y) :=
    (SCV.analyticAt_of_differentiableOn (c.holo _ g) (ho.mem_nhds hm)).contDiffAt
  refine del_mul_dbar_fn (hX.atlas σ) _ ⟨(c, y), hy⟩ hf
    (((VMetric.det HQ).cInf σ).contDiffAt c hy' (mem_pick _ y))
    (((VMetric.det (H.restrict hl' hL')).cInf σ).contDiffAt c hy' (mem_pick _ y)) ?_
  filter_upwards [ho.mem_nhds hm] with u hu
  have key := AdjFlag.div_eq_one_sub hS hL hQ hL' hl hl' (h.met σ) hv.symm (isFrame_resM a ha) (isFrame_resM b hb) hu.2
  rw [hg, form_smul_smul, Complex.mul_conj, Complex.re_ofReal_mul, form_frame_eq_exp _ _ _ hu.2,
    form_frame_eq_exp _ _ _ hu.2, Complex.normSq_eq_norm_sq, mul_div_assoc, ← Real.exp_sub] at key
  refine key.symm.trans (congrArg (_ * Real.exp ·) ?_)
  rw [neg_sub_neg, neg_sub]
  rfl

end Lines

theorem local_identity : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    GlobalTheory.HermFrame.kappa • ((hY.atlas σ).del ((hY.atlas σ).fn (fun y => 1 - v y)) * (hY.atlas σ).dbar ((hY.atlas σ).fn (fun y => 1 - v y))) = ((hY.atlas σ).fn (fun y => 1 - v y)) * ((hY.atlas σ).ddc ((hY.atlas σ).fn (fun y => 1 - v y)) + ((hY.atlas σ).fn (fun y => 1 - v y)) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 4 - X 0)) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl _ A σ v hv
  funext x
  have key := two_flags hY (H.pull π w) fl (flB.pull π) hv x
  rw [c1F_eq_of_isometric k Y p _ hY σ _ _ (VMetric.isometric_grLB_pull k B Y q p E 2 h H flB π w 1)] at key
  refine key.trans ?_
  simp only [Pi.mul_apply, Pi.add_apply, evalF, fld, map_sub, map_X, aeval_X, Subalgebra.coe_sub]
  rfl

end GlobalTheory.LocalLelong
