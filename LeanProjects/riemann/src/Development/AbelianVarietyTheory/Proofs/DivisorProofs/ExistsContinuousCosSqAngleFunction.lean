import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

open GlobalTheory.Twist (resM resM_resM)

namespace GlobalTheory.CurveDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {V L L' : X.Modules} {r : ℕ} (h : Met p σ V r)

theorem exists_smul_frame (c : Chart L 1) {W T : X.Opens} (hW : W ≤ c.U) (hT : T ≤ W)
    (s : Γ(L, T)) : ∃ f : Γ(X, T), s = f • resM L hT (resM L hW (c.e 0)) := by
  refine ⟨(c.isFrame.basis (hT.trans hW)).repr s 0, ?_⟩
  conv_lhs => rw [← (c.isFrame.basis (hT.trans hW)).sum_repr s]
  rw [Fin.sum_univ_one, IsFrame.basis_apply, resM_resM]

theorem form_smul_smul {T : X.Opens} (f g : Γ(X, T)) (a b : Γ(V, T)) (y : CxPts p σ) :
    h.form (f • a) (g • b) y =
      ev p σ T f y * starRingEnd ℂ (ev p σ T g y) * h.form a b y := by
  rw [h.form_smul_left, ← h.conj_form (g • b), h.form_smul_left, map_mul, h.conj_form, mul_assoc]

theorem normSq_form_le {T : X.Opens} (a b : Γ(V, T)) (y : CxPts p σ) :
    ‖h.form a b y‖ ^ 2 ≤ (h.form a a y).re * (h.form b b y).re := by
  have hp := (h.posDef _ y (h.isVB.mem_pick y)).posSemidef
  have e := norm_form_le hp ((h.isVB.pick y).crd p σ a y) ((h.isVB.pick y).crd p σ b y)
  have e₁ := gnorm_sq hp ((h.isVB.pick y).crd p σ a y)
  have e₂ := gnorm_sq hp ((h.isVB.pick y).crd p σ b y)
  calc ‖h.form a b y‖ ^ 2 ≤ _ := pow_le_pow_left₀ (norm_nonneg _) e 2
    _ = _ := by rw [mul_pow, e₁, e₂]; rfl

def frameImg (l : L ⟶ V) (c : Chart L 1) {W : X.Opens} (hW : W ≤ c.U) : Γ(V, W) :=
  l.app W (resM L hW (c.e 0))

theorem frameImg_pos {l : L ⟶ V} (hl : IsSubbundle l) (hL : IsVB L 1) (c : Chart L 1)
    {W : X.Opens} (hW : W ≤ c.U) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W)
    (hc : y ∈ ptsIn p σ c.U) : 0 < (h.form (frameImg l c hW) (frameImg l c hW) y).re := by
  rw [frameImg, ← h.form_restrict hl hL _ _ hy, Met.form_resM _ _ _ _ hy,
    Met.form_frame _ _ hc]
  exact (Complex.pos_iff.1 ((h.restrict hl hL).posDef c y hc).diag_pos).1

def cosRatio (l : L ⟶ V) (l' : L' ⟶ V) (c : Chart L 1) (c' : Chart L' 1) (y : CxPts p σ) : ℝ :=
  ‖h.form (frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U))
    (frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U)) y‖ ^ 2 /
  ((h.form (frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U))
      (frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U)) y).re *
    (h.form (frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U))
      (frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U)) y).re)

theorem resM_app_eq_smul (l : L ⟶ V) (c : Chart L 1) {U W T : X.Opens} (hW : W ≤ c.U)
    (hT : T ≤ W) (hU : T ≤ U) (s : Γ(L, U)) :
    ∃ f : Γ(X, T), resM V hU (l.app U s) = f • resM V hT (frameImg l c hW) := by
  obtain ⟨f, hf⟩ := exists_smul_frame c hW hT (resM L hU s)
  refine ⟨f, ?_⟩
  rw [← GlobalTheory.Twist.app_resM, hf, Scheme.Modules.Hom.app_smul, GlobalTheory.Twist.app_resM]
  rfl

theorem cosRatio_spec {l : L ⟶ V} {l' : L' ⟶ V} (hl : IsSubbundle l) (hl' : IsSubbundle l')
    (hL : IsVB L 1) (hL' : IsVB L' 1) (c : Chart L 1) (c' : Chart L' 1) {U : X.Opens}
    (s : Γ(L, U)) (s' : Γ(L', U)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ U)
    (hc : y ∈ ptsIn p σ c.U) (hc' : y ∈ ptsIn p σ c'.U) :
    ‖h.form (l'.app U s') (l.app U s) y‖ ^ 2 = cosRatio h l l' c c' y *
      (h.form (l.app U s) (l.app U s) y).re * (h.form (l'.app U s') (l'.app U s') y).re := by
  have hyW : y ∈ ptsIn p σ (c.U ⊓ c'.U) := mem_ptsIn_inf.2 ⟨hc, hc'⟩
  have hyT : y ∈ ptsIn p σ (U ⊓ (c.U ⊓ c'.U)) := mem_ptsIn_inf.2 ⟨hy, hyW⟩
  obtain ⟨f, hf⟩ := resM_app_eq_smul l c (inf_le_left : c.U ⊓ c'.U ≤ c.U)
    (inf_le_right : U ⊓ (c.U ⊓ c'.U) ≤ _) inf_le_left s
  obtain ⟨g, hg⟩ := resM_app_eq_smul l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U)
    (inf_le_right : U ⊓ (c.U ⊓ c'.U) ≤ _) inf_le_left s'
  have pos := frameImg_pos h hl hL c (inf_le_left : c.U ⊓ c'.U ≤ c.U) hyW hc
  have pos' := frameImg_pos h hl' hL' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U) hyW hc'
  rw [cosRatio]
  set u := frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U)
  set u' := frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U)
  have e₁ : h.form (l'.app U s') (l.app U s) y =
      ev p σ _ g y * starRingEnd ℂ (ev p σ _ f y) * h.form u' u y := by
    rw [← h.form_resM _ _ (inf_le_left : U ⊓ (c.U ⊓ c'.U) ≤ U) hyT, hf, hg, form_smul_smul,
      h.form_resM _ _ _ hyT]
  have e₂ : h.form (l.app U s) (l.app U s) y =
      ev p σ _ f y * starRingEnd ℂ (ev p σ _ f y) * h.form u u y := by
    rw [← h.form_resM _ _ (inf_le_left : U ⊓ (c.U ⊓ c'.U) ≤ U) hyT, hf, form_smul_smul,
      h.form_resM _ _ _ hyT]
  have e₃ : h.form (l'.app U s') (l'.app U s') y =
      ev p σ _ g y * starRingEnd ℂ (ev p σ _ g y) * h.form u' u' y := by
    rw [← h.form_resM _ _ (inf_le_left : U ⊓ (c.U ⊓ c'.U) ≤ U) hyT, hg, form_smul_smul,
      h.form_resM _ _ _ hyT]
  rw [e₁, e₂, e₃, Complex.mul_conj, Complex.mul_conj, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq]
  field_simp

theorem exists_isCosSq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    (V L L' : X.Modules) (r : ℕ) (h : Met p σ V r) (l : L ⟶ V) (l' : L' ⟶ V), h.IsCInf →
    IsSubbundle l → IsSubbundle l' → IsVB L 1 → IsVB L' 1 →
    ∃ v : CxPts p σ → ℝ, IsCosSq h l l' v ∧ Continuous v ∧ ∀ y, 0 ≤ v y ∧ v y ≤ 1 := by
  intro k _ X p σ V L L' r h l l' H hl hl' hL hL'
  have hv : IsCosSq h l l' fun y => cosRatio h l l' (hL.pick y) (hL'.pick y) y :=
    fun U t t' y hy => cosRatio_spec h hl hl' hL hL' _ _ t t' hy (hL.mem_pick y) (hL'.mem_pick y)
  refine ⟨_, hv, continuous_iff_continuousAt.2 fun y₀ => ?_, fun y => ?_⟩
  · have hc := hL.mem_pick y₀
    have hc' := hL'.mem_pick y₀
    generalize hL.pick y₀ = c at hc
    generalize hL'.pick y₀ = c' at hc'
    have hyW : y₀ ∈ ptsIn p σ (c.U ⊓ c'.U) := mem_ptsIn_inf.2 ⟨hc, hc'⟩
    have G := H.gram (![frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U),
      frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U)]) hyW
    have c₀₀ : ContinuousAt (fun z => h.form (frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U))
      (frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U)) z) y₀ := (G 0 0).continuousAt
    have c₁₀ : ContinuousAt (fun z => h.form (frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U))
      (frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U)) z) y₀ := (G 1 0).continuousAt
    have c₁₁ : ContinuousAt (fun z => h.form (frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U))
      (frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U)) z) y₀ := (G 1 1).continuousAt
    have pos := frameImg_pos h hl hL c (inf_le_left : c.U ⊓ c'.U ≤ c.U) hyW hc
    have pos' := frameImg_pos h hl' hL' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U) hyW hc'
    have R := (c₁₀.norm.pow 2).div
      ((Complex.continuous_re.continuousAt.comp c₀₀).mul
        (Complex.continuous_re.continuousAt.comp c₁₁)) (mul_pos pos pos').ne'
    refine R.congr ?_
    filter_upwards [(isOpen_ptsIn _).mem_nhds hyW] with z hz
    have e := hv (c.U ⊓ c'.U) (resM L inf_le_left (c.e 0)) (resM L' inf_le_right (c'.e 0)) z hz
    have p₁ := frameImg_pos h hl hL c (inf_le_left : c.U ⊓ c'.U ≤ c.U) hz (mem_ptsIn_inf.1 hz).1
    have p₂ := frameImg_pos h hl' hL' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U) hz (mem_ptsIn_inf.1 hz).2
    change ‖h.form (frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U))
      (frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U)) z‖ ^ 2 =
      cosRatio h l l' (hL.pick z) (hL'.pick z) z *
      (h.form (frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U))
        (frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U)) z).re *
      (h.form (frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U))
        (frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U)) z).re at e
    simp only [Pi.div_apply, Function.comp_apply, Pi.mul_apply, Pi.pow_apply]
    rw [e]
    field_simp
  · have hc := hL.mem_pick y
    have hc' := hL'.mem_pick y
    have hyW := mem_ptsIn_inf.2 ⟨hc, hc'⟩
    have pos := frameImg_pos h hl hL (hL.pick y) inf_le_left hyW hc
    have pos' := frameImg_pos h hl' hL' (hL'.pick y) inf_le_right hyW hc'
    refine ⟨div_nonneg (sq_nonneg _) (mul_pos pos pos').le, (div_le_one (mul_pos pos pos')).2 ?_⟩
    have := normSq_form_le h (frameImg l (hL.pick y) inf_le_left)
      (frameImg l' (hL'.pick y) inf_le_right) y
    rwa [← h.conj_form, Complex.norm_conj] at this

end GlobalTheory.CurveDens
