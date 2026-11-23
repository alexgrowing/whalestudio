import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatrixIsFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsC1DensityForLinePair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinePairExtensionCosSqBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAngleFormReEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleWeightChartFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubbundleChartFormsExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMixZeroOfRealPartZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarHermitianFormLineFrameBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatrixLeviFormLogStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AngleFormDbarHermitianStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixDens

open GlobalTheory.Twist (resM)
open GlobalTheory.CurveDens (angleForm IsCosSq)

theorem green_algebra (A B v bc bc' ch ch' lA lB x y N : ℝ) (n : ℕ) (hA : 0 < A)
    (hB : 0 < B) (hN : N = v * A * B) (hx : x = (A * B - N) * bc)
    (hy : y = (B * A - N) * bc') (hc : ch = -lA) (hc' : ch' = -lB) :
    v ^ (n + 1) * (ch - ch') + (n + 1) * v ^ n * (1 - v) * (bc - bc') +
      ((n + 1) * (N / (A * B)) ^ n * ((y - x) / (A * B)) +
        (N / (A * B)) ^ (n + 1) * (lA - lB)) = 0 := by
  have e : N / (A * B) = v := by rw [hN]; field_simp
  rw [e, hx, hy, hN, hc, hc']
  field_simp
  ring

theorem mix_comb_eq_zero {d : ℕ} {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ} (hA : A.IsHermitian)
    (M₁ M₂ M₃ M₄ N : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (s t : ℝ)
    (h : ∀ ξ : V (d + 1), s * ((∑ j, ∑ l, ξ j * M₁ j l * starRingEnd ℂ (ξ l)).re -
        (∑ j, ∑ l, ξ j * M₂ j l * starRingEnd ℂ (ξ l)).re) +
      t * ((∑ j, ∑ l, ξ j * M₃ j l * starRingEnd ℂ (ξ l)).re -
        (∑ j, ∑ l, ξ j * M₄ j l * starRingEnd ℂ (ξ l)).re) +
      (∑ j, ∑ l, ξ j * N j l * starRingEnd ℂ (ξ l)).re = 0) :
    s * (mix d A M₁ - mix d A M₂) + t * (mix d A M₃ - mix d A M₄) + mix d A N = 0 := by
  have key := GlobalTheory.T.hermitian_mix_zero_of_real_part_zero d A ((s : ℂ) • M₁ + ((-s : ℝ) : ℂ) • M₂ + (t : ℂ) • M₃ + ((-t : ℝ) : ℂ) • M₄ + N) hA
    fun ξ => by
      rw [← h ξ]
      have e : ∑ j, ∑ l, ξ j * ((s : ℂ) • M₁ + ((-s : ℝ) : ℂ) • M₂ + (t : ℂ) • M₃ + ((-t : ℝ) : ℂ) • M₄ + N) j l *
          starRingEnd ℂ (ξ l) =
          (s : ℂ) * ((∑ j, ∑ l, ξ j * M₁ j l * starRingEnd ℂ (ξ l)) -
            (∑ j, ∑ l, ξ j * M₂ j l * starRingEnd ℂ (ξ l))) +
          (t : ℂ) * ((∑ j, ∑ l, ξ j * M₃ j l * starRingEnd ℂ (ξ l)) -
            (∑ j, ∑ l, ξ j * M₄ j l * starRingEnd ℂ (ξ l))) +
          (∑ j, ∑ l, ξ j * N j l * starRingEnd ℂ (ξ l)) := by
        simp only [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        push_cast
        ring
      rw [e]
      simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re]
  simp only [mix_add, mix_smul] at key
  linarith

theorem green_density {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}
    {E L Q L' Q' : X.Modules} {l : L ⟶ E} {m : E ⟶ Q} {w : l ≫ m = 0} {l' : L' ⟶ E} {m' : E ⟶ Q'}
    {w' : l' ≫ m' = 0} (hS : (ShortComplex.mk l m w).ShortExact)
    (hS' : (ShortComplex.mk l' m' w').ShortExact) (hL : IsVB L 1) (hQ : IsVB Q 1)
    (hL' : IsVB L' 1) (hQ' : IsVB Q' 1) (hl : IsSubbundle l) (hl' : IsSubbundle l')
    (h : Met p σ E (1 + 1)) (H : h.IsCInf) {v : CxPts p σ → ℝ} (hv : IsCosSq h l l' v) (n : ℕ)
    {α : AlgChart p σ (d + 1) → CxPts p σ → Fin (d + 1) → ℂ}
    (hm₃ : ∀ (U : X.Opens) (t : Γ(L, U)) (t' : Γ(L', U)), IsFrame (fun _ : Fin 1 => t) →
      IsFrame (fun _ : Fin 1 => t') → ∀ c : AlgChart p σ (d + 1), ∀ y ∈ c.e.source, y ∈ ptsIn p σ U → ∀ j,
      α c y j = angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re)
        (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re)
        (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single j 1) (c.e y))
    (c : AlgChart p σ (d + 1)) {y : CxPts p σ} (hy : y ∈ c.e.source)
    {A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ} (hA : A.IsHermitian) :
    v y ^ (n + 1) * (mix d A (chernMat (h.restrict hl hL).detWeight c y) -
        mix d A (chernMat (h.restrict hl' hL').detWeight c y)) +
      (n + 1) * v y ^ n * (1 - v y) * (mix d A (bcMat (S := ShortComplex.mk l m w) h hS hL hQ c y) -
        mix d A (bcMat (S := ShortComplex.mk l' m' w') h hS' hL' hQ' c y)) +
    mix d A (Matrix.of fun j l => dbar (fun v => α c (c.e.symm v) j) (c.e y) (EuclideanSpace.single l 1)) = 0 := by
  obtain ⟨U₁, e₁, hx₁, he₁⟩ := hL (y.1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨U₂, e₂, hx₂, he₂⟩ := hL' (y.1 (IsLocalRing.closedPoint ℂ))
  have hU : y ∈ ptsIn p σ (U₁ ⊓ U₂) := mem_ptsIn_inf.2 ⟨mem_ptsIn.2 hx₁, mem_ptsIn.2 hx₂⟩
  obtain ⟨U, hUdef⟩ : ∃ U, U = U₁ ⊓ U₂ := ⟨_, rfl⟩
  rw [← hUdef] at hU
  obtain ⟨t, ht⟩ : ∃ t : Γ(L, U), IsFrame (fun _ : Fin 1 => t) := by
    subst hUdef
    refine ⟨resM L inf_le_left (e₁ 0), ?_⟩
    have e : (fun _ : Fin 1 => resM L (inf_le_left : U₁ ⊓ U₂ ≤ U₁) (e₁ 0)) =
        fun i => resM L inf_le_left (e₁ i) := by
      funext i; rw [Subsingleton.elim i 0]
    rw [e]
    exact he₁.res inf_le_left
  obtain ⟨t', ht'⟩ : ∃ t' : Γ(L', U), IsFrame (fun _ : Fin 1 => t') := by
    subst hUdef
    refine ⟨resM L' inf_le_right (e₂ 0), ?_⟩
    have e : (fun _ : Fin 1 => resM L' (inf_le_right : U₁ ⊓ U₂ ≤ U₂) (e₂ 0)) =
        fun i => resM L' inf_le_right (e₂ i) := by
      funext i; rw [Subsingleton.elim i 0]
    rw [e]
    exact he₂.res inf_le_right
  have e₀ : c.e.symm (c.e y) = y := c.e.left_inv hy
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) U)
  have hm := ChartGlue.mem_over c.e hy hU
  have hn := ho.mem_nhds hm
  have dq : ContDiffAt ℝ 2 (fun x => h.form (l'.app U t') (l.app U t) (c.e.symm x)) (c.e y) :=
    (AngleGlue.contDiffAt_form h H _ _ hU c hy).of_le (by norm_cast)
  have da : ContDiffAt ℝ 2 (fun x => (h.form (l.app U t) (l.app U t) (c.e.symm x)).re) (c.e y) :=
    (AngleGlue.contDiffAt_re_form h H _ _ hU c hy).of_le (by norm_cast)
  have da' : ContDiffAt ℝ 2 (fun x => (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re) (c.e y) :=
    (AngleGlue.contDiffAt_re_form h H _ _ hU c hy).of_le (by norm_cast)
  have pa : 0 < (h.form (l.app U t) (l.app U t) y).re := AngleGlue.re_form_pos h hl hL t ht hU
  have pa' : 0 < (h.form (l'.app U t') (l'.app U t') y).re := AngleGlue.re_form_pos h hl' hL' t' ht' hU
  refine mix_comb_eq_zero hA _ _ _ _ _ _ _ fun ξ => ?_
  have hdb (j : Fin (d + 1)) : dbar (fun x => α c (c.e.symm x) j) (c.e y) =
      dbar (angleForm n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re)
        (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re)
        (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) (EuclideanSpace.single j 1)) (c.e y) :=
    dbar_congr (by
      filter_upwards [hn] with x hx
      have := hm₃ U t t' ht ht' c (c.e.symm x) (c.e.map_target hx.1) hx.2 j
      rwa [c.e.right_inv hx.1] at this)
  have hq := GlobalTheory.T.angle_form_dbar_hermitian _ n _ _ _ (c.e y) ξ da da' dq (by simpa only [e₀] using pa) (by simpa only [e₀] using pa')
  have hcalc := CurveDens.re_dbar_angleForm _ n (fun v => (h.form (l.app U t) (l.app U t) (c.e.symm v)).re)
    (fun v => (h.form (l'.app U t') (l'.app U t') (c.e.symm v)).re)
    (fun v => h.form (l'.app U t') (l.app U t) (c.e.symm v)) ξ (c.e y)
    da da' dq (by simpa only [e₀] using pa) (by simpa only [e₀] using pa')
  have hX := GlobalTheory.T.dbar_hermitian_form_line_frame_bound k X p σ _ (ShortComplex.mk l m w) h hS hL hQ H U t (l'.app U t') ht c y hy hU ξ
  have hY := GlobalTheory.T.dbar_hermitian_form_line_frame_bound k X p σ _ (ShortComplex.mk l' m' w') h hS' hL' hQ' H U t' (l.app U t) ht' c y hy hU ξ
  have hY' : ‖del (fun x => h.form (l'.app U t') (l.app U t) (c.e.symm x)) (c.e y) ξ -
        h.form (l'.app U t') (l.app U t) y *
        del (fun x => (Real.log (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re : ℂ)) (c.e y) ξ‖ ^ 2 =
      ((h.form (l'.app U t') (l'.app U t') y).re * (h.form (l.app U t) (l.app U t) y).re -
        ‖h.form (l'.app U t') (l.app U t) y‖ ^ 2) *
        (∑ j, ∑ i, ξ j * bcMat (S := ShortComplex.mk l' m' w') h hS' hL' hQ' c y j i * starRingEnd ℂ (ξ i)).re := by
    have e₁ : (fun x => h.form (l.app U t) (l'.app U t') (c.e.symm x)) =
        fun x => (starRingEnd ℂ) (h.form (l'.app U t') (l.app U t) (c.e.symm x)) := by
      funext x; rw [h.conj_form]
    have e₂ : h.form (l.app U t) (l'.app U t') y =
        (starRingEnd ℂ) (h.form (l'.app U t') (l.app U t) y) := by rw [h.conj_form]
    have hY2 : ‖dbar (fun x => h.form (l.app U t) (l'.app U t') (c.e.symm x)) (c.e y) ξ -
          h.form (l.app U t) (l'.app U t') y *
          dbar (fun x => (Real.log (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re : ℂ)) (c.e y) ξ‖ ^ 2 =
        ((h.form (l'.app U t') (l'.app U t') y).re * (h.form (l.app U t) (l.app U t) y).re -
          ‖h.form (l.app U t) (l'.app U t') y‖ ^ 2) *
        (∑ j, ∑ i, ξ j * bcMat (S := ShortComplex.mk l' m' w') h hS' hL' hQ' c y j i * starRingEnd ℂ (ξ i)).re := hY
    rw [e₁, e₂, dbar_conj, dbar_ofReal, ← map_mul, ← map_sub, Complex.norm_conj,
      Complex.norm_conj] at hY2
    exact hY2
  have c₁ := GlobalTheory.T.chern_matrix_levi_form_log k X p σ _ L (h.restrict hl hL) (H.restrict hl hL) U t ht c y hy hU ξ
  have c₂ := GlobalTheory.T.chern_matrix_levi_form_log k X p σ _ L' (h.restrict hl' hL') (H.restrict hl' hL') U t' ht' c y hy hU ξ
  have l₁ : leviForm (fun x => Real.log ((h.restrict hl hL).form t t (c.e.symm x)).re) (c.e y) =
      leviForm (fun x => Real.log (h.form (l.app U t) (l.app U t) (c.e.symm x)).re) (c.e y) :=
    CurveDens.leviForm_congr_germ (by
      filter_upwards [hn] with x hx
      rw [h.form_restrict hl hL _ _ hx.2])
  have l₂ : leviForm (fun x => Real.log ((h.restrict hl' hL').form t' t' (c.e.symm x)).re) (c.e y) =
      leviForm (fun x => Real.log (h.form (l'.app U t') (l'.app U t') (c.e.symm x)).re) (c.e y) :=
    CurveDens.leviForm_congr_germ (by
      filter_upwards [hn] with x hx
      rw [h.form_restrict hl' hL' _ _ hx.2])
  rw [l₁] at c₁
  rw [l₂] at c₂
  simp only [e₀] at hcalc
  simp only [Matrix.of_apply, hdb]
  rw [hq, hcalc]
  exact green_algebra _ _ (v y) _ _ _ _ _ _ _ _ _ n pa pa' (hv U t t' y hU) hX hY' c₁ c₂

theorem green_cosSq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ (d + 1)) → ∀ (E L Q L' Q' : X.Modules) (l : L ⟶ E) (m : E ⟶ Q) (w : l ≫ m = 0) (l' : L' ⟶ E) (m' : E ⟶ Q') (w' : l' ≫ m' = 0) (hS : (ShortComplex.mk l m w).ShortExact) (hS' : (ShortComplex.mk l' m' w').ShortExact) (hL : IsVB L 1) (hQ : IsVB Q 1) (hL' : IsVB L' 1) (hQ' : IsVB Q' 1) (hl : IsSubbundle l) (hl' : IsSubbundle l') (h : Met p σ E (1 + 1)), h.IsCInf → ∀ (N : LB X) (φ : Weight p σ N), φ.IsCInf → ∀ v : CxPts p σ → ℝ, CurveDens.IsCosSq h l l' v → ∀ n : ℕ, total (fun (c : AlgChart p σ (d + 1)) y => v y ^ (n + 1) * (mix d (chernMat φ c y) (chernMat (h.restrict hl hL).detWeight c y) - mix d (chernMat φ c y) (chernMat (h.restrict hl' hL').detWeight c y)) + (n + 1) * v y ^ n * (1 - v y) * (mix d (chernMat φ c y) (bcMat (S := ShortComplex.mk l m w) h hS hL hQ c y) - mix d (chernMat φ c y) (bcMat (S := ShortComplex.mk l' m' w') h hS' hL' hQ' c y))) = 0 := by
  intro k _ X p σ d _ _ _ hAn E L Q L' Q' l m w l' m' w' hS hS' hL hQ hL' hQ' hl hl' h H N φ hφ v hv n
  obtain ⟨α, h₁, h₂, h₃⟩ := GlobalTheory.T.subbundle_chart_forms_exist k X p σ d E L L' (1 + 1) h l l' H hl hl' hL hL' n
  have st := GlobalTheory.T.line_bundle_weight_chart_forms k X p σ d hAn N φ hφ (fun c y j => -α c y j) (fun c y hy j => (h₁ c y hy j).neg)
    (fun c c' y hy hy' j => by simp only [h₂ c c' y hy hy' j, mul_neg, Finset.sum_neg_distrib])
  rw [← st]
  refine total_congr fun c y hy => ?_
  have key := green_density hS hS' hL hQ hL' hQ' hl hl' h H hv n h₃ c hy ((GlobalTheory.T.chern_matrix_is_form k X p σ _ N φ hφ).2.2 c y hy)
  have e : (Matrix.of fun j i => dbar (fun v => -α c (c.e.symm v) j) (c.e y) (EuclideanSpace.single i 1)) =
      ((-1 : ℝ) : ℂ) • Matrix.of fun j i => dbar (fun v => α c (c.e.symm v) j) (c.e y) (EuclideanSpace.single i 1) := by
    ext j i
    simp only [Matrix.of_apply, Matrix.smul_apply, dbar_apply, fderiv_fun_neg, ContinuousLinearMap.neg_apply, smul_eq_mul]
    push_cast
    ring
  rw [e, mix_smul]
  linarith

end GlobalTheory.MixDens
