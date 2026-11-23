import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictPosOfExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet
open scoped ComplexOrder

namespace GlobalTheory.ShFam

attribute [local instance] Over.cartesianMonoidalCategory

section Manifold

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ} {d : ℕ}

def LiesIn (y : CxPts p σ) (C : Closeds Y) : Prop := y.1 (IsLocalRing.closedPoint ℂ) ∈ C

def IsDivNorm (R : AnRead p σ d) (C : Closeds Y) (n : CxPts p σ → ℝ) : Prop :=
  (∀ y, 0 ≤ n y ∧ n y ≤ 1) ∧ ∀ y, ∃ (V : Y.affineOpens) (t : Γ(Y, V.1)) (f : CxPts p σ → ℝ),
    y ∈ ptsIn p σ V.1 ∧ (Scheme.IdealSheafData.vanishingIdeal C).ideal V = Ideal.span {t} ∧
    R.SmoothOn (ptsIn p σ V.1) f ∧ ∀ z ∈ ptsIn p σ V.1, n z ^ 2 = ‖ev p σ V.1 t z‖ ^ 2 * Real.exp (-f z)

theorem ev_eq_zero_iff {C : Closeds Y} {V : Y.affineOpens} {t : Γ(Y, V.1)}
    (h : (Scheme.IdealSheafData.vanishingIdeal C).ideal V = Ideal.span {t}) {y : CxPts p σ} (hy : y ∈ ptsIn p σ V.1) :
    ev p σ V.1 t y = 0 ↔ LiesIn y C := by
  have h1 := Scheme.IdealSheafData.mem_support_iff_of_mem (I := Scheme.IdealSheafData.vanishingIdeal C)
    (U := V) (mem_ptsIn.1 hy)
  rw [h, Scheme.zeroLocus_span, Scheme.zeroLocus_singleton] at h1
  have h2 : (Scheme.IdealSheafData.vanishingIdeal C).support = C :=
    SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal C)
  rw [h2] at h1
  rw [LiesIn, h1, ← not_ne_iff, ← mem_ptsIn_basicOpen hy, mem_ptsIn]
  rfl

theorem isOpen_not_liesIn (C : Closeds Y) : IsOpen {y : CxPts p σ | ¬ LiesIn y C} := by
  have : {y : CxPts p σ | ¬ LiesIn y C} = ptsIn p σ C.compl := Set.ext fun y => (mem_ptsIn (y := y) (U := C.compl)).symm
  exact this ▸ isOpen_ptsIn _

namespace IsDivNorm

variable {R : AnRead p σ d} {C : Closeds Y} {n : CxPts p σ → ℝ} (h : IsDivNorm R C n)
include h

theorem pos_iff (y : CxPts p σ) : 0 < n y ↔ ¬ LiesIn y C := by
  obtain ⟨V, t, f, hy, ht, -, e⟩ := h.2 y
  rw [← ev_eq_zero_iff ht hy, (h.1 y).1.lt_iff_ne', ← sq_pos_iff, e y hy, mul_pos_iff_of_pos_right (Real.exp_pos _),
    sq_pos_iff, norm_ne_zero_iff]

theorem of_anRead (R' : AnRead p σ d) : IsDivNorm R' C n :=
  ⟨h.1, fun y => by
    obtain ⟨V, t, f, hy, ht, hf, e⟩ := h.2 y
    exact ⟨V, t, f, hy, ht, (AnRead.smoothOn_iff R R' (isOpen_ptsIn _)).1 hf, e⟩⟩

theorem smoothOn_log : R.SmoothOn {y | ¬ LiesIn y C} fun y => Real.log (n y ^ 2) := by
  choose V t f hy ht hf e using h.2
  refine AnRead.smoothOn_of_cover (fun y => isOpen_ptsIn (V y).1) (fun y _ => ⟨y, hy y⟩) fun y => ?_
  have h0 : ∀ z ∈ {z | ¬ LiesIn z C} ∩ ptsIn p σ (V y).1, ev p σ _ (t y) z ≠ 0 :=
    fun z hz h0 => hz.1 ((ev_eq_zero_iff (ht y) hz.2).1 h0)
  have h1 := (AnRead.holoOn_ev_of_subset (R := R) (t y) Set.inter_subset_right).smoothOn_log
    ((isOpen_not_liesIn C).inter (isOpen_ptsIn _)) h0
  refine AnRead.SmoothOn.congr (f := fun z => Real.log (‖ev p σ _ (t y) z‖ ^ 2) - f y z)
    (fun i => (h1 i).sub ((hf y).mono Set.inter_subset_right i)) fun z hz => ?_
  rw [e y z hz.2, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 (h0 z hz))) (Real.exp_ne_zero _), Real.log_exp,
    sub_eq_add_neg]

end IsDivNorm

theorem isDivNorm_of_eqn [IsAffine Y] (R : AnRead p σ d) {C : Closeds Y} {t : Γ(Y, ⊤)}
    (h : (Scheme.IdealSheafData.vanishingIdeal C).ideal ⟨⊤, isAffineOpen_top Y⟩ = Ideal.span {t}) :
    IsDivNorm R C fun y => ‖ev p σ ⊤ t y‖ / √(1 + ‖ev p σ ⊤ t y‖ ^ 2) := by
  have hp : ∀ y, 0 < 1 + ‖ev p σ ⊤ t y‖ ^ 2 := fun y => by positivity
  refine ⟨fun y => ⟨by positivity, ?_⟩, fun y => ⟨⟨⊤, isAffineOpen_top Y⟩, t,
    fun z => Real.log (1 + ‖ev p σ ⊤ t z‖ ^ 2), mem_ptsIn_top, h, fun i => ?_, fun z _ => ?_⟩⟩
  · exact (div_le_one (Real.sqrt_pos.2 (hp y))).2 (Real.le_sqrt_of_sq_le (by linarith))
  · exact (contDiffOn_const.add ((GlobalTheory.ChartGlue.contDiffOn_real (GlobalTheory.ChartGlue.isOpen_over _ (isOpen_ptsIn _))
      (R.holoOn_ev ⊤ t i)).norm_sq ℂ)).log fun _ _ => (hp _).ne'
  · rw [div_pow, Real.sq_sqrt (hp z).le, Real.exp_neg, Real.exp_log (hp z), div_eq_mul_inv]

abbrev ChartForm (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) : Type := AlgChart p σ d → CxPts p σ → (Fin d → ℂ) → ℝ

def ddcForm (f : CxPts p σ → ℝ) : ChartForm p σ d := fun c y ξ => c.levi f y ξ / Real.pi

def IsPotential (R : AnRead p σ d) (a : ChartForm p σ d) (W : Set (CxPts p σ)) (φ : CxPts p σ → ℝ) : Prop :=
  IsOpen W ∧ R.SmoothOn W φ ∧ ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, y ∈ W → ∀ ξ, a c y ξ = ddcForm φ c y ξ

def IsKaehlerForm (R : AnRead p σ d) (a : ChartForm p σ d) : Prop :=
  (∀ y, ∃ W φ, y ∈ W ∧ IsPotential R a W φ) ∧ ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ ξ, ξ ≠ 0 → 0 < a c y ξ

theorem IsKaehlerForm.trans {R : AnRead p σ d} {a : ChartForm p σ d} (h : IsKaehlerForm R a) {c c' : AlgChart p σ d}
    {y : CxPts p σ} (hy : y ∈ c.e.source) (hy' : y ∈ c'.e.source) (ξ : Fin d → ℂ) :
    a c y ξ = a c' y (c.dtrans c' y ξ) := by
  obtain ⟨W, φ, hW, ho, hs, e⟩ := h.1 y
  rw [e c y hy hW, e c' y hy' hW, ddcForm, ddcForm, AlgChart.levi_trans hy hy' (hs.contDiffAt_two ho hy' hW)]

theorem IsKaehlerForm.of_anRead {R : AnRead p σ d} {a : ChartForm p σ d} (h : IsKaehlerForm R a) (R' : AnRead p σ d) :
    IsKaehlerForm R' a :=
  ⟨fun y => by
    obtain ⟨W, φ, hW, ho, hs, e⟩ := h.1 y
    exact ⟨W, φ, hW, ho, (AnRead.smoothOn_iff R R' ho).1 hs, e⟩, h.2⟩

def curvForm {B : ReciprocityTheory.ChartRestriction.G.Semi.LB Y} (φ : Weight p σ B) : ChartForm p σ d :=
  fun c y => ddcForm (φ.φ (pick φ.isLB y)) c y

theorem isPotential_curvForm {R : AnRead p σ d} {B : ReciprocityTheory.ChartRestriction.G.Semi.LB Y} {φ : Weight p σ B} (h : φ.IsSmooth R)
    (i : B.ι) : IsPotential R (curvForm φ) (ptsIn p σ (B.U i)) (φ.φ i) :=
  ⟨isOpen_ptsIn _, h i, fun _ y hy hi ξ => congrArg (· / Real.pi) (h.levi_frame hy (mem_pick φ.isLB y) hi ξ)⟩

theorem isKaehlerForm_curvForm {R : AnRead p σ d} {B : ReciprocityTheory.ChartRestriction.G.Semi.LB Y} {φ : Weight p σ B} (h : φ.IsSmooth R)
    (hp : φ.StrictPos R) : IsKaehlerForm R (curvForm φ) :=
  ⟨fun y => ⟨_, _, mem_pick φ.isLB y, isPotential_curvForm h _⟩,
    fun _ y hy _ hξ => div_pos (hp.chart h hy (mem_pick φ.isLB y) hξ) Real.pi_pos⟩

theorem ddcForm_coord (c : AlgChart p σ d) (j : Fin d) {y : CxPts p σ} (hy : y ∈ c.e.source) (ξ : Fin d → ℂ) :
    ddcForm (fun z => Complex.normSq (c.e z j)) c y ξ = Complex.normSq (ξ j) / Real.pi := by
  have hg : ContDiffAt ℂ 2 (fun v : ReciprocityTheory.L2DbarEstimates.V d => v j) (c.e y) :=
    (EuclideanSpace.proj j : ReciprocityTheory.L2DbarEstimates.V d →L[ℂ] ℂ).contDiff.contDiffAt
  have e := ReciprocityTheory.L2DbarEstimates.leviV_normSq_comp hg ξ
  have e1 : ∀ a, ReciprocityTheory.L2DbarEstimates.wd d a (fun v : ReciprocityTheory.L2DbarEstimates.V d => v j) (c.e y) = if j = a then 1 else 0 := fun a => by
    have : (fun v : ReciprocityTheory.L2DbarEstimates.V d => v j) =
        ((EuclideanSpace.proj j : ReciprocityTheory.L2DbarEstimates.V d →L[ℂ] ℂ).restrictScalars ℝ) := rfl
    rw [ReciprocityTheory.L2DbarEstimates.wd, this, ContinuousLinearMap.fderiv]
    by_cases h : j = a
    · simp [ReciprocityTheory.L2DbarEstimates.bas, h]
    · simp [ReciprocityTheory.L2DbarEstimates.bas, h]
  have e2 : ∑ a, ReciprocityTheory.L2DbarEstimates.wd d a (fun v : ReciprocityTheory.L2DbarEstimates.V d => v j) (c.e y) * ξ a = ξ j := by simp [e1]
  rw [e2] at e
  refine congrArg (· / Real.pi) (Eq.trans (congrArg Complex.re (Eq.trans ?_ e)) (Complex.ofReal_re _))
  refine ReciprocityTheory.L2DbarEstimates.leviV_congr (Filter.eventually_of_mem (c.e.open_target.mem_nhds (c.e.map_source hy))
    fun v hv => ?_) ξ
  simp only [c.e.right_inv hv]

theorem isKaehlerForm_ddcForm {R : AnRead p σ d} {φ : CxPts p σ → ℝ} (h : R.SmoothOn Set.univ φ)
    (hp : ∀ y, ∃ c : AlgChart p σ d, y ∈ c.e.source ∧ ∀ ξ, ξ ≠ 0 → 0 < ddcForm φ c y ξ) : IsKaehlerForm R (ddcForm φ) :=
  ⟨fun _ => ⟨_, φ, Set.mem_univ _, isOpen_univ, h, fun _ _ _ _ _ => rfl⟩, fun c y hy ξ hξ => by
    obtain ⟨c', hy', h'⟩ := hp y
    rw [ddcForm, AlgChart.levi_trans hy hy' (h.contDiffAt_two isOpen_univ hy' trivial)]
    exact h' _ (AlgChart.dtrans_ne_zero hy hy' hξ)⟩

example (R : AnRead p σ 1) (t : Γ(Y, ⊤))
    (h : ∀ y, ∃ c : AlgChart p σ 1, y ∈ c.e.source ∧ ∀ z ∈ c.e.source, c.e z 0 = ev p σ ⊤ t z) :
    IsKaehlerForm R (ddcForm fun z => ‖ev p σ ⊤ t z‖ ^ 2) := by
  refine isKaehlerForm_ddcForm (AnRead.SmoothOn.mono (S := ptsIn p σ ⊤) (fun i => (GlobalTheory.ChartGlue.contDiffOn_real
    (GlobalTheory.ChartGlue.isOpen_over _ (isOpen_ptsIn _)) (R.holoOn_ev ⊤ t i)).norm_sq ℂ) fun _ _ => mem_ptsIn_top) fun y => ?_
  obtain ⟨c, hy, e⟩ := h y
  refine ⟨c, hy, fun ξ hξ => ?_⟩
  rw [ddcForm, AlgChart.levi_congr (g := fun z => Complex.normSq (c.e z 0)) c.e.open_source hy hy
    fun z hz => by rw [e z hz, Complex.normSq_eq_norm_sq]]
  refine lt_of_lt_of_eq (div_pos (Complex.normSq_pos.2 fun h0 => hξ (funext fun a => ?_)) Real.pi_pos)
    (ddcForm_coord c 0 hy ξ).symm
  rwa [Subsingleton.elim a 0]

example [IsAffine Y] (R : AnRead p σ d) : ∃ n, IsDivNorm R ⊥ n ∧ ∀ y, 0 < n y :=
  ⟨_, isDivNorm_of_eqn R (t := 1) (by simp), fun y =>
    ((isDivNorm_of_eqn R (C := ⊥) (t := 1) (by simp)).pos_iff y).2 id⟩

def IsConjMap (m : CxPts p σ' → CxPts p σ) : Prop := ∀ z, (m z).1 = spMap (starRingEnd ℂ) ≫ z.1

end Manifold

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

namespace EigFrame

variable {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X} (f : EigFrame Z φ x)

def vec (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) : TanM x Z.t.G := tanOf (f.tan τ i)

theorem act_vec (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (a : 𝓞 E) :
    actR Z.t.act a (f.vec τ i) = φ (embK c τ a) • f.vec τ i := tan_ext (f.eig τ i a)

theorem existsUnique_sum (τ : E →+* ℂ) (w : TanM x Z.t.G) (hw : ∀ a, actR Z.t.act a w = φ (embK c τ a) • w) :
    ∃! a : Fin (Dw.mult τ) → R, w = ∑ i, a i • f.vec τ i :=
  (existsUnique_congr fun a => isComb_iff (f.vec τ) a w).1
    (f.basis τ _ (isTan_tv w) fun a => congrArg (fun v => (tv v).left) (hw a))

theorem linearIndependent_vec (τ : E →+* ℂ) : LinearIndependent R (f.vec τ) :=
  Fintype.linearIndependent_iff.2 fun a ha => congrFun
    ((f.existsUnique_sum τ 0 fun a => by simp).unique ha.symm (y₂ := 0) (by simp))

def ofVec (v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → TanM x Z.t.G)
    (he : ∀ τ i a, actR Z.t.act a (v τ i) = φ (embK c τ a) • v τ i)
    (hb : ∀ τ (w : TanM x Z.t.G), (∀ a, actR Z.t.act a w = φ (embK c τ a) • w) →
      ∃! a : Fin (Dw.mult τ) → R, w = ∑ i, a i • v τ i) : EigFrame Z φ x where
  v τ i := (tv (v τ i)).left
  tan τ i := isTan_tv _
  eig τ i a := congrArg (fun v => (tv v).left) (he τ i a)
  basis τ _ hw h := (existsUnique_congr fun a => isComb_iff (v τ) a (tanOf hw)).2 (hb τ _ fun a => tan_ext (h a))

end EigFrame

section FrPt

variable {S : Type} [CommRing S] [Algebra c.F S] (Z) (y : FrPt Xo c S) {x : Sp S ⟶ Z.X}
  (hx : GlobalTheory.AllWt.ptF y ≫ Z.jQ ≫ genι Z = x)

theorem ptF_fst : GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _

theorem ptF_snd : GlobalTheory.AllWt.ptF y ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := pullback.lift_snd _ _ _

def lieEquiv : TanM y.x Xo.univ.t.G ≃ₗ[S] TanM x Z.t.G :=
  (pushE Z.m0.toSABMap (GlobalTheory.AllWt.ptF y) (ptF_fst y)).symm.trans (pushE Z.m (GlobalTheory.AllWt.ptF y) hx)

theorem lieEquiv_act (a : 𝓞 E) (v : TanM y.x Xo.univ.t.G) :
    lieEquiv Z y hx (actR Xo.univ.t.act a v) = actR Z.t.act a (lieEquiv Z y hx v) := by
  obtain ⟨w, rfl⟩ := (pushE Z.m0.toSABMap (GlobalTheory.AllWt.ptF y) (ptF_fst y)).surjective v
  rw [← pushE_act]
  simp only [lieEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact pushE_act _ _ _ _ _

def EigFrame.ofFrPt : EigFrame Z (algebraMap c.F S) x :=
  EigFrame.ofVec (fun τ i => lieEquiv Z y hx (tanOf (t := Xo.univ.t) (y.tan τ i)))
    (fun τ i a => by
      rw [← lieEquiv_act, ← map_smul]
      exact congrArg _ (tan_ext (y.eig τ i a)))
    fun τ w hw => by
      obtain ⟨w, rfl⟩ := (lieEquiv Z y hx).surjective w
      refine (existsUnique_congr fun a => ?_).1 (y.basis τ _ (isTan_tv w) fun a => congrArg (fun v => (tv v).left)
        ((lieEquiv Z y hx).injective (by rw [lieEquiv_act, hw, map_smul]) :
          actR Xo.univ.t.act a w = algebraMap c.F S (embK c τ a) • w))
      refine (isComb_iff (fun i => tanOf (t := Xo.univ.t) (y.tan τ i)) a w).trans ?_
      rw [← (lieEquiv Z y hx).injective.eq_iff, map_sum]
      simp only [map_smul]

theorem EigFrame.ofFrPt_v (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) : ∃ w : Sp (DualNumber S) ⟶ Z.oF.t.G.left,
    IsTanAtG Z.oF.t (GlobalTheory.AllWt.ptF y) w ∧ w ≫ Z.m0.toSABMap.φ = y.u τ i ∧
      w ≫ Z.m.φ = (EigFrame.ofFrPt Z y hx).v τ i :=
  ⟨_, isTan_tv _, congrArg (fun v => (tv v).left) ((pushE Z.m0.toSABMap (GlobalTheory.AllWt.ptF y)
    (ptF_fst y)).apply_symm_apply (tanOf (t := Xo.univ.t) (y.tan τ i))), rfl⟩

end FrPt

variable {σ σ' : c.F →+* ℂ}

variable (Z) in

def cxPt (y : FrPt Xo c (CAt σ)) : CxPts (genStr Z) σ :=
  ⟨GlobalTheory.AllWt.ptF (S := CAt σ) y ≫ Z.jQ,
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) Z.jQ_over).trans (ptF_snd y))⟩

theorem cxPt_congr {y y' : FrPt Xo c (CAt σ)} (h : y.x = y'.x) : cxPt Z y = cxPt Z y' :=
  Subtype.ext (congrArg (· ≫ Z.jQ) (pullback.hom_ext
    ((ptF_fst y).trans (h.trans (ptF_fst y').symm))
    ((ptF_snd y).trans (ptF_snd y').symm)))

theorem not_liesIn_cxPt (y : FrPt Xo c (CAt σ)) : ¬ LiesIn (cxPt Z y) (genBd Z) :=
  fun h => h ⟨GlobalTheory.AllWt.ptF y (IsLocalRing.closedPoint ℂ), rfl⟩

variable (Z) in

def cxFrame (y : FrPt Xo c (CAt σ)) : EigFrame Z σ ((cxPt Z y).1 ≫ genι Z) :=
  EigFrame.ofFrPt (S := CAt σ) Z y (Category.assoc _ _ _).symm

variable [SmoothOfRelativeDimension Dw.dim (genStr Z)]

variable (Z σ) in

abbrev manifold : AnRead (genStr Z) σ Dw.dim := AnRead.all _ _ _

variable (Z) in

structure OddPrimesWithRootsOfUnity : Type where

  m : ℕ

  cpt : Fin m → Closeds (gen Z)
  cpt_list : ReciprocityTheory.AnForm.R.FinalTheorems.CompList (genBd Z : Set (gen Z : Scheme.{0})) cpt

  nrm : ∀ σ : c.F →+* ℂ, Fin m → CxPts (genStr Z) σ → ℝ
  nrm_div : ∀ σ i, IsDivNorm (manifold Z σ) (cpt i) (nrm σ i)
  nrm_conj : ∀ σ σ' (j : CxPts (genStr Z) σ' → CxPts (genStr Z) σ), IsConjMap j → ∀ i z, nrm σ' i z = nrm σ i (j z)

  kae : ∀ σ : c.F →+* ℂ, ChartForm (genStr Z) σ Dw.dim
  kae_kaehler : ∀ σ, IsKaehlerForm (manifold Z σ) (kae σ)
  kae_conj : ∀ σ σ' (j : CxPts (genStr Z) σ' → CxPts (genStr Z) σ), IsConjMap j → ∀ W φ,
    IsPotential (manifold Z σ) (kae σ) W φ → IsPotential (manifold Z σ') (kae σ') (j ⁻¹' W) (φ ∘ j)

  cst : ℝ
  cst_pos : 0 < cst
  cst_small : ∀ σ i (ch : AlgChart (genStr Z) σ Dw.dim), ∀ y ∈ ch.e.source, ¬ LiesIn y (cpt i) → ∀ ξ,
    2 * m * cst * |ddcForm (fun z => Real.exp 1 - Real.log (nrm σ i z ^ 2)) ch y ξ| ≤ Real.exp 1 * kae σ ch y ξ

  met : ∀ (σ : c.F →+* ℂ) (y : CxPts (genStr Z) σ),
    TanM (y.1 ≫ genι Z) Z.t.G →ₗ[ℂ] TanM (y.1 ≫ genι Z) Z.t.G →ₗ⋆[ℂ] ℂ
  met_smooth : ∀ σ, IsLieMetric Z.t (genι Z) (manifold Z σ) (met σ)
  met_conj : ∀ σ σ' (y : CxPts (genStr Z) σ) (y' : CxPts (genStr Z) σ') (v w : TanM (y.1 ≫ genι Z) Z.t.G)
    (v' w' : TanM (y'.1 ≫ genι Z) Z.t.G), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 →
    (tv v').left = spMap (dualMap (starRingEnd ℂ)) ≫ (tv v).left →
    (tv w').left = spMap (dualMap (starRingEnd ℂ)) ≫ (tv w).left →
    met σ' y' v' w' = starRingEnd ℂ (met σ y v w)

namespace OddPrimesWithRootsOfUnity

variable (x : OddPrimesWithRootsOfUnity Z)

theorem liesIn_genBd_iff (y : CxPts (genStr Z) σ) : LiesIn y (genBd Z) ↔ ∃ i, LiesIn y (x.cpt i) :=
  (Set.ext_iff.1 x.cpt_list.2.1 _).symm.trans Set.mem_iUnion

theorem nrm_pos {y : CxPts (genStr Z) σ} (h : ¬ LiesIn y (genBd Z)) (i : Fin x.m) : 0 < x.nrm σ i y :=
  ((x.nrm_div σ i).pos_iff y).2 fun h' => h ((x.liesIn_genBd_iff y).2 ⟨i, h'⟩)

theorem m_eq_zero_iff : x.m = 0 ↔ (genBd Z : Set (gen Z : Scheme.{0})) = ∅ := by
  rw [← x.cpt_list.2.1, Set.iUnion_eq_empty]
  exact ⟨fun h i => (Fin.cast h i).elim0, fun h => by_contra fun h0 =>
    (x.cpt_list.1 ⟨0, Nat.pos_of_ne_zero h0⟩).nonempty.ne_empty (h _)⟩

def r (σ : c.F →+* ℂ) (y : CxPts (genStr Z) σ) : ℝ := Real.exp 1 - Real.log ((∏ i, x.nrm σ i y) ^ 2)

def gram (y : CxPts (genStr Z) σ) (f : EigFrame Z σ (y.1 ≫ genι Z)) (τ : E →+* ℂ) :
    Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ := gramOf (x.met σ y) (f.vec τ)

variable {y : CxPts (genStr Z) σ}

theorem gram_posDef (f : EigFrame Z σ (y.1 ≫ genι Z)) (τ : E →+* ℂ) : (x.gram y f τ).PosDef :=
  ((x.met_smooth σ).1 y).gram_posDef (f.linearIndependent_vec τ)

theorem gram_change (f g : EigFrame Z σ (y.1 ≫ genι Z)) (τ : E →+* ℂ)
    (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (h : ∀ i, IsCombAtG Z.t (y.1 ≫ genι Z) (f.v τ) (fun a => T a i) (g.v τ i)) :
    x.gram y g τ = Tᴴ * x.gram y f τ * T := by
  ext a b
  have e := fun i => (isComb_iff (f.vec τ) (fun a => T a i) (g.vec τ i)).1 (h i)
  rw [gram, gramOf, of_apply, e a, e b, form_sum, Matrix.mul_assoc]
  rfl

theorem met_vec_eq_zero (f g : EigFrame Z σ (y.1 ≫ genι Z)) {τ τ' : E →+* ℂ} (h : τ ≠ τ') (i : Fin (Dw.mult τ))
    (i' : Fin (Dw.mult τ')) : x.met σ y (f.vec τ i) (g.vec τ' i') = 0 :=
  ((x.met_smooth σ).1 y).2.2 (Formalism.L2.PjFree.relab c σ τ) (Formalism.L2.PjFree.relab c σ τ') _ _
    (fun e => h (RingHom.ext fun a => congrArg Subtype.val (σ.injective (RingHom.congr_fun e a))))
    (f.act_vec τ i) (g.act_vec τ' i')

theorem gram_smooth (V : (gen Z).affineOpens) {φ : c.F →+* Γ(gen Z, V.1)} (F : EigFrame Z φ (LogKS.chart V ≫ genι Z))
    (τ : E →+* ℂ) (a b : Fin (Dw.mult τ)) : ∃ g : CxPts (genStr Z) σ → ℂ,
      (manifold Z σ).SmoothOn (ptsIn _ σ V.1) (fun y => (g y).re) ∧
      (manifold Z σ).SmoothOn (ptsIn _ σ V.1) (fun y => (g y).im) ∧
      ∀ y (hy : y ∈ ptsIn _ σ V.1) (f : EigFrame Z σ (y.1 ≫ genι Z)),
        (∀ i, f.v τ i = spMap (dualMap (evHom hy)) ≫ F.v τ i) → x.gram y f τ a b = g y := by
  obtain ⟨g, h1, h2, h3⟩ := (x.met_smooth σ).2 V (F.vec τ b) (F.vec τ a)
  refine ⟨g, h1, h2, fun y hy f hf => ?_⟩
  rw [h3 y hy]
  exact congrArg₂ (fun v w => x.met σ y v w) (tan_ext (hf b)) (tan_ext (hf a))

theorem gram_conj {y' : CxPts (genStr Z) σ'} (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    (f : EigFrame Z σ (y.1 ≫ genι Z)) (f' : EigFrame Z σ' (y'.1 ≫ genι Z)) (τ : E →+* ℂ)
    (h : ∀ i, f'.v τ i = spMap (dualMap (starRingEnd ℂ)) ≫ f.v τ i) :
    x.gram y' f' τ = (x.gram y f τ).map (starRingEnd ℂ) :=
  Matrix.ext fun a b => x.met_conj σ σ' y y' _ _ _ _ e (h b) (h a)

end OddPrimesWithRootsOfUnity

end Free

end GlobalTheory.ShFam
