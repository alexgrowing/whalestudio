import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodChartDualRiemannStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusIntegralChangeOfParametrizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothIntegralOverUnitCubeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicNonnegIntegralPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatCoordsSymplecticPullbackForm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR GlobalTheory.VB
open GlobalTheory.LB (toMod)
open GlobalTheory.Twist (resM app_resM)
open GlobalTheory.LieVB (omega unitSec)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat cov per IsPeriodMap)
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

namespace GlobalTheory.ThetaSquareIntegrable

variable {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {σ σ' : k →+* ℂ} {A : Over S}
  {g D : ℕ}

theorem per_add (t : Matrix (Fin g) (Fin g) ℂ) (x y : Fl g) : per t (x + y) = per t x + per t y := by
  ext i
  simp [per, vecMul, dotProduct, add_mul, Finset.sum_add_distrib]
  ring

theorem mem_stdLat {x : Fl g} : x ∈ stdLat g ↔ ∀ i, ∃ n : ℤ, x i = n := by
  rw [stdLat, Module.Basis.mem_span_iff_repr_mem]
  exact forall_congr' fun i => ⟨fun ⟨n, hn⟩ => ⟨n, by simpa using hn.symm⟩,
    fun ⟨n, hn⟩ => ⟨n, by simpa using hn.symm⟩⟩

theorem contDiffOn_per {B : Set (V D)} {τ : V D → Matrix (Fin g) (Fin g) ℂ} (h : IsPeriodMap B τ) :
    ContDiffOn ℝ ∞ (fun Q : V D × Fl g => ((Q.1, per (τ Q.1) Q.2) : Pt (V D) g)) (B ×ˢ univ) := by
  refine contDiffOn_fst.prodMk (contDiffOn_pi.2 fun a => ?_)
  have c (i) : ContDiffOn ℝ ∞ (fun Q : V D × Fl g => (Q.2 i : ℂ)) (B ×ˢ univ) :=
    (Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ i).comp contDiff_snd)).contDiffOn
  simp only [per, vecMul, dotProduct, Pi.add_apply]
  exact (ContDiffOn.sum fun i _ => (c _).mul ((ChartGlue.contDiffOn_real h.1 (h.2.1 i a)).comp
    contDiffOn_fst fun _ hQ => hQ.1)).add (c _)

theorem continuousOn_of_isHolTo {X : Scheme.{0}} {q : X ⟶ Sp k} {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℂ W] {B : Set W} {y : W → CxPts q σ} (h : IsHolTo B fun b => (y b).1) :
    ContinuousOn y B := by
  rw [continuousOn_iff_continuous_domRestrict, CxPts.continuous_iff]
  intro U
  refine ⟨?_, fun f => ?_⟩
  · convert (h U 0).1.preimage (continuous_subtype_val (p := (· ∈ B))) using 1
    ext b
    exact ⟨fun hb => ⟨b.2, hb⟩, fun hb => hb.2⟩
  · exact (h U f).2.continuousOn.comp continuous_subtype_val.continuousOn fun b hb => ⟨b.2, hb⟩

theorem contDiffAt_of_isHolTo {X : Scheme.{0}} {q : X ⟶ Sp k} {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℂ W] [FiniteDimensional ℂ W] {B : Set W} (hB : IsOpen B) {y : W → CxPts q σ}
    (h : IsHolTo B fun b => (y b).1) {b : W} (hb : b ∈ B) {f : CxPts q σ → ℂ} (hf : VInfAt f (y b)) :
    ContDiffAt ℝ ∞ (fun w => f (y w)) b := by
  obtain ⟨U, J, _, u, F, O, h₁, h₂, h₃, h₄, h₅⟩ := hf
  have hg : ContDiffAt ℝ ∞ (fun w a => ev q σ U (u a) (y w)) b := contDiffAt_pi.2 fun a =>
    (SCV.contDiffAt_of_differentiableOn (h U (u a)).2 ((h U (u a)).1.mem_nhds ⟨hb, h₁⟩)
      _).restrict_scalars ℝ
  exact ((h₄.contDiffAt (h₂.mem_nhds h₃)).comp b hg).congr_of_eventuallyEq
    (((continuousOn_of_isHolTo h).continuousAt (hB.mem_nhds hb)).eventually h₅)

variable [GrpObj A] {h : VMetric p (omega A) g} {c : AlgChart p σ D}
  {τ : V D → Matrix (Fin g) (Fin g) ℂ} {ex : Pt (V D) g → CxPts (A.hom ≫ p) σ} {v : V D}

theorem exists_par (H : IsPeriodChart h c τ ex) (hv : v ∈ c.e.target) :
    ∃ E : Fl g → (Over.mk (c.e.symm v).1 ⟶ A), (∀ x, (E x).left = (ex (v, per (τ v) x)).1) ∧
      (∀ x y, E (x + y) = E x * E y) ∧ Function.Surjective E ∧
      ∀ x y, E x = E y ↔ ∀ i, ∃ n : ℤ, x i - y i = n := by
  obtain ⟨h₁, h₂, h₃, h₄, -⟩ := H.2.2 v hv
  have hu : IsUnit ((τ v).map Complex.im).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (H.1.2.2 v hv).2.isUnit
  let E : Fl g → (Over.mk (c.e.symm v).1 ⟶ A) := fun x => Over.homMk (ex (v, per (τ v) x)).1 (h₁ _)
  have ha (x y) : E (x + y) = E x * E y := Over.OverMorphism.ext (by
    rw [h₂ _ _ (E x) (E y) rfl rfl, ← per_add]; rfl)
  refine ⟨E, fun _ => rfl, ha, fun x => ?_, fun x y => ?_⟩
  · obtain ⟨z, hz⟩ := h₃ x
    exact ⟨IndefiniteRowSideFullHecke.SiegelReframe.flatOf (τ v) z, Over.OverMorphism.ext (by
      rw [hz, ← SympFlatChange.per_flatOf hu z]; simp only [SympFlatChange.flatOf_per hu]; rfl)⟩
  · have e : E x = E (x - y) * E y := by rw [← ha, sub_add_cancel]
    have e₁ : (1 : Over.mk (c.e.symm v).1 ⟶ A).left = (c.e.symm v).1 ≫ unitSec A := by
      rw [Hom.one_def]
      simp
      rfl
    rw [e, mul_eq_right]
    refine Iff.trans ⟨fun e => (congrArg (·.left) e).trans e₁, fun e => Over.OverMorphism.ext
      (e.trans e₁.symm)⟩ ((h₄ _).trans ⟨fun ⟨l, hl, e⟩ => ?_, fun e => ⟨_, mem_stdLat.2 e, rfl⟩⟩)
    have := congrArg (IndefiniteRowSideFullHecke.SiegelReframe.flatOf (τ v)) e
    rw [SympFlatChange.flatOf_per hu, SympFlatChange.flatOf_per hu] at this
    exact mem_stdLat.1 (this.symm ▸ hl : x - y ∈ stdLat g)

theorem continuous_par (H : IsPeriodChart h c τ ex) (hv : v ∈ c.e.target) :
    Continuous fun x => ex (v, per (τ v) x) :=
  continuousOn_univ.1 (((continuousOn_of_isHolTo H.2.1).comp (contDiffOn_per H.1).continuousOn
    fun _ hQ => ⟨hQ.1, trivial⟩).comp (f := fun x => (v, x)) (by fun_prop) fun _ _ => ⟨hv, trivial⟩)

omit [GrpObj A] in

theorem mem_pre {z : CxPts (A.hom ≫ p) σ} {y : CxPts p σ} (e : z.1 ≫ A.hom = y.1) {U : S.Opens}
    (hy : y ∈ ptsIn p σ U) : z ∈ ptsIn (A.hom ≫ p) σ (A.hom ⁻¹ᵁ U) := by
  have : ⊤ ≤ y.1 ⁻¹ᵁ U := hy
  rw [← e] at this
  exact this

theorem integral_eq [IsSeparated (A.hom ≫ p)] (H : IsPeriodChart h c τ ex) (hv : v ∈ c.e.target)
    {c' : AlgChart p σ' D} {τ' : V D → Matrix (Fin g) (Fin g) ℂ}
    {ex' : Pt (V D) g → CxPts (A.hom ≫ p) σ'} {v' : V D} (H' : IsPeriodChart h c' τ' ex')
    (hv' : v' ∈ c'.e.target) (κ : Sp ℂ ⟶ Sp ℂ) (hκ : κ ≫ κ = 𝟙 _)
    (e : (c'.e.symm v').1 = κ ≫ (c.e.symm v).1)
    (m : CxPts (A.hom ≫ p) σ → CxPts (A.hom ≫ p) σ') (hm : Continuous m)
    (hm' : ∀ z, (m z).1 = κ ≫ z.1) {U : S.Opens} (hU : c'.e.symm v' ∈ ptsIn p σ' U)
    {F : CxPts (A.hom ≫ p) σ' → ℂ} (hF : ContinuousOn F (ptsIn _ σ' (A.hom ⁻¹ᵁ U))) :
    ∫ x in Icc (0 : Fl g) 1, F (m (ex (v, per (τ v) x))) =
      ∫ x in Icc (0 : Fl g) 1, F (ex' (v', per (τ' v') x)) := by
  obtain ⟨E, e₁, e₂, e₃, e₄⟩ := exists_par H hv
  obtain ⟨E', e₁', e₂', e₃', e₄'⟩ := exists_par H' hv'
  let K : Over.mk (c'.e.symm v').1 ⟶ Over.mk (c.e.symm v).1 := Over.homMk κ e.symm
  let K' : Over.mk (c.e.symm v).1 ⟶ Over.mk (c'.e.symm v').1 :=
    Over.homMk κ (by simp [e, ← Category.assoc, hκ])
  have k₁ : K ≫ K' = 𝟙 _ := Over.OverMorphism.ext hκ
  have k₂ : K' ≫ K = 𝟙 _ := Over.OverMorphism.ext hκ
  have a (x x') : m (ex (v, per (τ v) x)) = ex' (v', per (τ' v') x') ↔ K ≫ E x = E' x' := by
    rw [Subtype.ext_iff, hm', ← e₁, ← e₁']
    exact ⟨fun e => Over.OverMorphism.ext e, fun e => congrArg (·.left) e⟩
  have hr : range (fun x => m (ex (v, per (τ v) x))) = range fun x => ex' (v', per (τ' v') x) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨x', hx⟩ := e₃' (K ≫ E x)
      exact ⟨x', ((a x x').2 hx.symm).symm⟩
    · rintro ⟨x', rfl⟩
      obtain ⟨x, hx⟩ := e₃ (K' ≫ E' x')
      exact ⟨x, (a x x').2 (by rw [hx, ← Category.assoc, k₁, Category.id_comp])⟩
  refine T.torus_integral_change_of_parametrization _ _ (fun x => m (ex (v, per (τ v) x))) _ (hm.comp (continuous_par H hv)) (continuous_par H' hv') (fun x y => ?_)
    (fun x y => ?_) hr (fun x x' y y' hx hy => ?_) F (hF.mono ?_)
  · rw [← e₄, Subtype.ext_iff, hm', hm', ← e₁, ← e₁]
    refine ⟨fun e => Over.OverMorphism.ext ?_, fun e => by rw [e]⟩
    have := congrArg (κ ≫ ·) e
    simpa only [← Category.assoc, hκ, Category.id_comp] using this
  · rw [← e₄', Subtype.ext_iff, ← e₁', ← e₁']
    exact ⟨fun e => Over.OverMorphism.ext e, fun e => by rw [e]⟩
  · rw [a] at hx hy ⊢
    rw [e₂, e₂', comp_mul, hx, hy]
  · rw [hr]
    rintro _ ⟨x, rfl⟩
    exact mem_pre ((H'.2.2 v' hv').1 _) hU

theorem contDiffOn_integral (H : IsPeriodChart h c τ ex) {U : S.Opens}
    {F : CxPts (A.hom ≫ p) σ → ℂ} (hF : ∀ z ∈ ptsIn _ σ (A.hom ⁻¹ᵁ U), VInfAt F z) :
    ContDiffOn ℝ ∞ (fun v => ∫ x in Icc (0 : Fl g) 1, F (ex (v, per (τ v) x)))
      (c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ U) := by
  refine T.smooth_integral_over_unit_cube _ _ _ (fun Q => F (ex (Q.1, per (τ Q.1) Q.2)))
    (ChartGlue.isOpen_over c.e (isOpen_ptsIn U)) fun Q hQ => ?_
  have ho : IsOpen (cov c.e.target g) := c.e.open_target.prod isOpen_univ
  have := (contDiffAt_of_isHolTo ho H.2.1 (b := (Q.1, per (τ Q.1) Q.2)) ⟨hQ.1.1, trivial⟩
    (hF _ (mem_pre ((H.2.2 _ hQ.1.1).1 _) hQ.1.2))).comp_contDiffWithinAt Q
    (contDiffOn_per H.1 Q ⟨hQ.1.1, trivial⟩)
  exact this.mono fun _ hR => ⟨hR.1.1, trivial⟩

theorem integral_pos (H : IsPeriodChart h c τ ex) (hv : v ∈ c.e.target) {U : S.Opens}
    (hU : c.e.symm v ∈ ptsIn p σ U) {F : CxPts (A.hom ≫ p) σ → ℝ}
    (hF : ContinuousOn F (ptsIn _ σ (A.hom ⁻¹ᵁ U))) (h₀ : ∀ z, 0 ≤ F z)
    {z : CxPts (A.hom ≫ p) σ} (hz : z.1 ≫ A.hom = (c.e.symm v).1) (hz' : F z ≠ 0) :
    0 < ∫ x in Icc (0 : Fl g) 1, F (ex (v, per (τ v) x)) := by
  obtain ⟨E, e₁, -, e₃, e₄⟩ := exists_par H hv
  refine T.periodic_nonneg_integral_pos _ _ (hF.comp_continuous (continuous_par H hv)
    fun x => mem_pre ((H.2.2 v hv).1 _) hU) (fun _ => h₀ _) (fun x n => congrArg F (Subtype.ext ?_)) ?_
  · rw [← e₁, ← e₁, (e₄ _ x).2 fun i => ⟨n i, by simp⟩]
  · obtain ⟨x, hx⟩ := e₃ (Over.homMk z.1 hz)
    exact ⟨x, by rwa [show ex (v, per (τ v) x) = z from Subtype.ext (by rw [← e₁, hx]; rfl)]⟩

section Norm

variable {X : Scheme.{0}} {q : X ⟶ Sp k} {E : X.Modules} {r : ℕ} (m : Met q σ E r) {W : X.Opens}

theorem form_self_nonneg (s : Γ(E, W)) (y : CxPts q σ) : 0 ≤ m.form s s y := by
  by_cases e : (m.isVB.pick y).crd q σ s y = 0
  · simp [Met.form, e, HermFrame.form]
  · exact ((HermFrame.posDef_iff.1 (m.posDef _ y (m.isVB.mem_pick y))).2 _ e).le

theorem form_smul_self (a : Γ(X, W)) (s : Γ(E, W)) (y : CxPts q σ) :
    m.form (a • s) (a • s) y = (‖ev q σ W a y‖ ^ 2 : ℝ) * m.form s s y := by
  rw [m.form_smul_left, ← m.conj_form (a • s) s, m.form_smul_left, map_mul, m.conj_form,
    ← _root_.mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem form_ofWeight {N : LB X} (φ : Weight q σ N) (s : Γ(toMod N, W)) {i : N.ι} {y : CxPts q σ}
    (hy : y ∈ ptsIn q σ W) (hi : y ∈ ptsIn q σ (N.U i)) :
    (Met.ofWeight φ).form s s y =
      (‖ev q σ _ (LB.coord s i) y‖ ^ 2 : ℝ) * (Real.exp (-φ.φ i y) : ℂ) := by
  have hW := mem_ptsIn_inf.2 ⟨hy, hi⟩
  have e := (Met.ofWeight φ).form_frame (Chart.ofLB φ.isLB i) hi 0 0
  rw [Met.ofWeight_G φ hi] at e
  rw [← Met.form_resM _ s s inf_le_left hW, ← (LB.chartEquiv φ.isLB i inf_le_right).symm_apply_apply
    (resM _ inf_le_left s), LB.chartEquiv_symm_apply, form_smul_self, LB.chartEquiv_apply,
    ev_res _ hW, LB.coord_map, ev_res _ (mem_ptsIn_inf.2 ⟨hW, hi⟩)]
  exact congrArg _ ((Met.form_resM _ _ _ inf_le_right hW).trans (e.trans (by simp)))

end Norm

omit [GrpObj A]

variable (L : HermLB (A.hom ≫ p)) {M : LB S}
  (ψ : toMod M ⟶ (Scheme.Modules.pushforward A.hom).obj (toMod L.B)) {U : S.Opens}

def nrm (s : Γ(toMod M, U)) (z : CxPts (A.hom ≫ p) σ) : ℂ :=
  ((VMetric.ofLB L).met σ).form (V := A.hom ⁻¹ᵁ U) (ψ.app U s) (ψ.app U s) z

theorem ofReal_re_nrm (s : Γ(toMod M, U)) (z : CxPts (A.hom ≫ p) σ) :
    ((nrm L ψ s z).re : ℂ) = nrm L ψ s z :=
  Complex.ext rfl (Complex.nonneg_iff.1 (form_self_nonneg _ _ z)).2

theorem vInfAt_nrm (s : Γ(toMod M, U)) :
    ∀ z ∈ ptsIn _ σ (A.hom ⁻¹ᵁ U), VInfAt (nrm L ψ s) z := fun _ hz =>
  (VMetric.isCInf_ofLB L σ).gram (U := A.hom ⁻¹ᵁ U) (fun _ : Unit => ψ.app U s) hz () ()

theorem continuousOn_nrm (s : Γ(toMod M, U)) :
    ContinuousOn (nrm L ψ s) (ptsIn _ σ (A.hom ⁻¹ᵁ U)) := fun z hz =>
  (vInfAt_nrm L ψ s z hz).continuousAt.continuousWithinAt

theorem nrm_eq (hM : M.IsLB) (s : Γ(toMod M, U)) {i : M.ι} {y : CxPts p σ} (hy : y ∈ ptsIn p σ U)
    (hi : y ∈ ptsIn p σ (M.U i)) {z : CxPts (A.hom ≫ p) σ} (e : z.1 ≫ A.hom = y.1) :
    nrm L ψ s z = (‖ev p σ _ (LB.coord s i) y‖ ^ 2 : ℝ) * nrm L ψ (LB.chartSec hM i) z := by
  have hW := mem_ptsIn_inf.2 ⟨hy, hi⟩
  have hz := mem_pre e hW
  have r {U' : S.Opens} (h' : U ⊓ M.U i ≤ U') (t : Γ(toMod M, U')) :
      nrm L ψ (resM _ h' t) z = nrm L ψ t z := by
    rw [nrm, app_resM]
    exact Met.form_resM _ _ _ (A.hom.preimage_mono h') hz
  have e' : PtsOver.map A.hom rfl _ z = y := Subtype.ext e
  rw [← r inf_le_left, ← r inf_le_right, ← (LB.chartEquiv hM i inf_le_right).symm_apply_apply
    (resM _ inf_le_left s), LB.chartEquiv_symm_apply, nrm, Scheme.Modules.Hom.app_smul]
  refine (form_smul_self _ (A.hom.app _ _) _ z).trans ?_
  rw [ev_app A.hom rfl, e', LB.chartEquiv_apply, ev_res _ hW, LB.coord_map,
    ev_res _ (mem_ptsIn_inf.2 ⟨hW, hi⟩)]
  rfl

theorem exists_pt [LocallyOfFiniteType A.hom] (y : CxPts p σ) {W : A.left.Opens} {a : A.left}
    (ha : a ∈ W) (e : A.hom a = y.1 (IsLocalRing.closedPoint ℂ)) :
    ∃ z : CxPts (A.hom ≫ p) σ, z.1 ≫ A.hom = y.1 ∧ z ∈ ptsIn _ σ W := by
  let t := Limits.pullback.snd A.hom y.1
  let u := Limits.pullback.fst A.hom y.1
  have := LocallyOfFiniteType.jacobsonSpace t
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback a _ e
  obtain ⟨x, hx, hc'⟩ := nonempty_inter_closedPoints (Z := u ⁻¹' W) ⟨w, show u w ∈ W from hw ▸ ha⟩
    (W.isOpen.preimage u.continuous).isLocallyClosed
  have hc : IsClosed ({x} : Set _) := hc'
  have e₁ : (pointOfClosedPoint t x hc ≫ u) ≫ A.hom = y.1 := by
    rw [Category.assoc, Limits.pullback.condition, pointOfClosedPoint_comp_assoc]
  exact ⟨⟨pointOfClosedPoint t x hc ≫ u, by rw [← Category.assoc, e₁, y.2]⟩, e₁,
    mem_ptsIn.2 ((congrArg (u · ∈ W) (pointOfClosedPoint_apply t x hc _)).mpr hx)⟩

theorem exists_nrm_ne_zero [LocallyOfFiniteType A.hom] (hP : PushInvertible A L.B) (hM : M.IsLB)
    [IsIso ψ] {i : M.ι} {y : CxPts p σ} (hi : y ∈ ptsIn p σ (M.U i)) :
    ∃ z : CxPts (A.hom ≫ p) σ, z.1 ≫ A.hom = y.1 ∧ (nrm L ψ (LB.chartSec hM i) z).re ≠ 0 := by
  obtain ⟨W, hW, θ, hθ, -, H⟩ := hP (y.1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨a, j, e, ha⟩ := H _ hW
  obtain ⟨z, hz, hz'⟩ := exists_pt y ha e
  refine ⟨z, hz, fun h0 => ?_⟩
  have h₁ := ptsIn_mono (A.left.basicOpen_le _) hz'
  have h₂ := nrm_eq L ψ hM ((inv ψ).app W (LB.mkSec θ hθ)) (mem_ptsIn.2 hW) hi hz
  have h₃ : ψ.app W ((inv ψ).app W (LB.mkSec θ hθ)) = LB.mkSec θ hθ :=
    congr(($(IsIso.inv_hom_id ψ)).app W (LB.mkSec θ hθ))
  rw [← ofReal_re_nrm L ψ (LB.chartSec hM i), h0, Complex.ofReal_zero, mul_zero, nrm, h₃] at h₂
  have h₄ := (form_ofWeight (L.φ σ) (LB.mkSec θ hθ) (mem_ptsIn_inf.1 h₁).1
    (mem_ptsIn_inf.1 h₁).2).symm.trans h₂
  simp only [LB.coord_mkSec, mul_eq_zero, Complex.ofReal_eq_zero, Real.exp_ne_zero, or_false,
    pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h₄
  exact (mem_ptsIn_basicOpen h₁ _).1 hz' h₄

def fib (s : Γ(toMod M, U)) (τ : V D → Matrix (Fin g) (Fin g) ℂ)
    (ex : Pt (V D) g → CxPts (A.hom ≫ p) σ) (v : V D) : ℝ :=
  ∫ x in Icc (0 : Fl g) 1, (nrm L ψ s (ex (v, per (τ v) x))).re

theorem ofReal_fib (s : Γ(toMod M, U)) : (fib L ψ s τ ex v : ℂ) =
    ∫ x in Icc (0 : Fl g) 1, nrm L ψ s (ex (v, per (τ v) x)) := by
  rw [fib, ← integral_complex_ofReal]
  simp only [ofReal_re_nrm]

variable [GrpObj A] {h : VMetric p (omega A) g}

theorem fib_eq (H : IsPeriodChart h c τ ex) (hv : v ∈ c.e.target) (hM : M.IsLB) (s : Γ(toMod M, U))
    {i : M.ι} (hy : c.e.symm v ∈ ptsIn p σ U) (hi : c.e.symm v ∈ ptsIn p σ (M.U i)) :
    fib L ψ s τ ex v = ‖ev p σ _ (LB.coord s i) (c.e.symm v)‖ ^ 2 *
      fib L ψ (LB.chartSec hM i) τ ex v := by
  rw [fib, fib, ← integral_const_mul]
  simp only [fun x => nrm_eq L ψ hM s hy hi ((H.2.2 v hv).1 (per (τ v) x)), Complex.re_ofReal_mul]

end GlobalTheory.ThetaSquareIntegrable

namespace GlobalTheory.ThetaSquareIntegrable

theorem exists_l2Weight : ∀ (k : Type) [CommRing k] (S : Scheme.{0}) (p : S ⟶ Sp k), IsRegSurf p →
    ∀ (P : PPAS S) (h : VMetric p (omega P.A) P.g), P.IsDualRiemann (1 / 2) h →
    ∀ L : HermLB (P.A.hom ≫ p), IsTheta P L.B → ∀ (M : LB S) (hM : M.IsLB)
      (ψ : toMod M ≅ (Scheme.Modules.pushforward P.A.hom).obj (toMod L.B)),
    ∃ (φ : ∀ σ : k →+* ℂ, Weight p σ M) (h₁ : ∀ σ, (φ σ).IsCInf)
      (h₂ : ∀ σ σ', (φ σ).IsConj (φ σ')), ∀ (σ : k →+* ℂ) (y : CxPts p σ),
      ∃ (c : AlgChart p σ 1) (τ : V 1 → Matrix (Fin P.g) (Fin P.g) ℂ)
        (ex : Pt (V 1) P.g → CxPts (P.A.hom ≫ p) σ),
        y ∈ c.e.source ∧ IsPeriodChart h c τ ex ∧ IsL2OnDiagonal L ⟨M, hM, φ, h₁, h₂⟩ ψ c τ ex := by
  intro k _ S p hS P h hh L hL M hM ψ
  choose c τ ex hc _ H using T.exists_period_chart_dual_riemann k S p hS P h hh
  have := hS.isLocallyNoetherian
  have := P.isAb.proper
  have : IsSeparated p := by
    obtain ⟨N, j, _, hj⟩ := hS.isProjOver
    have := isProper_str k N
    exact hj ▸ inferInstance
  have hP : PushInvertible P.A L.B :=
    PushInv.pushInvertible abelianSchemeLaws_all.1.secBaseChange S hL.polAV
  have hv (σ y) : (c σ y).e y ∈ (c σ y).e.target := (c σ y).e.map_source (hc σ y)
  have hl (σ y) : (c σ y).e.symm ((c σ y).e y) = y := (c σ y).e.left_inv (hc σ y)
  let N (σ) (i : M.ι) (y : CxPts p σ) : ℝ :=
    fib L ψ.hom (LB.chartSec hM i) (τ σ y) (ex σ y) ((c σ y).e y)
  have hN (σ y i) {v} (hv' : v ∈ (c σ y).e.target) (hi : (c σ y).e.symm v ∈ ptsIn p σ (M.U i)) :
      N σ i ((c σ y).e.symm v) = fib L ψ.hom (LB.chartSec hM i) (τ σ y) (ex σ y) v := by
    refine Complex.ofReal_injective ?_
    rw [ofReal_fib, ofReal_fib]
    exact integral_eq (H σ _) (hv σ _) (H σ y) hv' (𝟙 _) (Category.id_comp _)
      (by rw [hl, Category.id_comp]) id continuous_id (fun _ => (Category.id_comp _).symm) hi
      (continuousOn_nrm L ψ.hom _)
  have hpos (σ i y) (hi : y ∈ ptsIn p σ (M.U i)) : 0 < N σ i y := by
    obtain ⟨z, hz, hz'⟩ := exists_nrm_ne_zero L ψ.hom hP hM hi
    exact integral_pos (H σ y) (hv σ y) (by rwa [hl])
      (Complex.continuous_re.comp_continuousOn (continuousOn_nrm L ψ.hom _))
      (fun z => (Complex.nonneg_iff.1 (form_self_nonneg _ _ z)).1) (by rwa [hl]) hz'
  have hπ : 0 < ((2 * π) ^ P.g)⁻¹ := by positivity
  let φ (σ) : Weight p σ M := ⟨hM, fun i y => -Real.log (((2 * π) ^ P.g)⁻¹ * N σ i y),
    fun i j y hi hj => by
      have e := fib_eq L ψ.hom (H σ y) (hv σ y) hM (LB.chartSec hM j) (i := i) (by rwa [hl])
        (by rwa [hl])
      rw [hl, LB.coord_chartSec, ev_res _ (mem_ptsIn_inf.2 ⟨hj, hi⟩)] at e
      have h0 : ‖gv p σ M i j y‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (gv_ne_zero hi hj))
      rw [show N σ j y = ‖gv p σ M i j y‖ ^ 2 * N σ i y from e, mul_left_comm,
        Real.log_mul h0 (mul_pos hπ (hpos σ i y hi)).ne']
      ring⟩
  refine ⟨φ, fun σ i y hi => cInfAt_of_chart (isOpen_ptsIn _) (c σ y) ?_ (hc σ y) hi,
    fun σ σ' i y y' e hi => ?_, fun σ y => ⟨_, _, _, hc σ y, H σ y, fun v hv' U s hU => ?_⟩⟩
  · have := Complex.reCLM.contDiff.comp_contDiffOn
      (contDiffOn_integral (H σ y) (vInfAt_nrm L ψ.hom (LB.chartSec hM i)))
    have e (v) (hv' : v ∈ (c σ y).e.target ∩ (c σ y).e.symm ⁻¹' ptsIn p σ (M.U i)) :
        N σ i ((c σ y).e.symm v) = _ := (hN σ y i hv'.1 hv'.2).trans
      (congrArg Complex.re (ofReal_fib L ψ.hom (LB.chartSec hM i)))
    exact ((contDiffOn_const.mul (this.congr e)).log fun v hv' =>
      (mul_pos hπ (hpos σ i _ hv'.2)).ne').neg
  · obtain rfl := eq_conj_of_conj e
    have e₀ : spMap ((starRingEnd ℂ).comp σ) = spMap (starRingEnd ℂ) ≫ spMap σ := by
      rw [← Spec.map_comp]
      rfl
    let m : CxPts (P.A.hom ≫ p) σ → CxPts (P.A.hom ≫ p) ((starRingEnd ℂ).comp σ) := fun z =>
      ⟨spMap (starRingEnd ℂ) ≫ z.1, by rw [Category.assoc, z.2, e₀]⟩
    have hκ : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 (Sp ℂ) := by
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext z
      exact Complex.conj_conj z
    have e₁ := integral_eq (H σ y) (hv σ y) (H _ y') (hv _ y') _ hκ (by rw [hl, hl, e]) m
      (((conjHomeomorph _).continuous.comp continuous_subtype_val).subtype_mk _) (fun _ => rfl)
      (by rw [hl]; exact (mem_ptsIn_iff_of_conj e).2 hi)
      (continuousOn_nrm L ψ.hom (LB.chartSec hM i))
    refine congrArg (fun t => -Real.log (((2 * π) ^ P.g)⁻¹ * t)) (Complex.ofReal_injective ?_)
    rw [ofReal_fib, ofReal_fib, ← e₁]
    refine congrArg _ (funext fun x => ?_)
    refine (((VMetric.ofLB L).conj _ _).form_eq _ _ rfl
      (mem_pre (((H σ y).2.2 _ (hv σ y)).1 _) (by rwa [hl]))).trans ?_
    exact Met.conj_form _ _ _ _
  · have hi := mem_pick hM ((c σ y).e.symm v)
    refine (form_ofWeight (φ σ) s hU hi).trans (Eq.trans ?_ (congrArg _ (ofReal_fib L ψ.hom s)))
    rw [fib_eq L ψ.hom (H σ y) hv' hM s hU hi, ← hN σ y _ hv' hi, neg_neg,
      Real.exp_log (mul_pos hπ (hpos σ _ _ hi))]
    push_cast
    ring

end GlobalTheory.ThetaSquareIntegrable
