import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowerSectionOfChartFunctions
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtSecIsMul

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.ThetaOfArc

open GlobalTheory.FieldBaseChange GlobalTheory.ConstFam GlobalTheory.IndivisibleSection GlobalTheory.ThetaUnit IsLocalRing

section General

variable {X : Scheme.{0}} {L : LB X}

theorem sectionOfLineBundleOne_iff_germs_eq {σ : H0 L 1} {θ : L.Sec} : SectionOfLineBundleOne σ θ ↔ ∀ (y : X) (k : L.ι), y ∈ L.U k →
    gs (𝟙 X) y (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k)) (σ.f fun _ => k) = gs (𝟙 X) y (L.U k) (θ.f k) := by
  refine ⟨fun h y k hy => ?_, fun h j hj => ?_⟩
  · rw [h (fun _ => k) (fun z hz => Set.mem_iInter.1 hz 0)]
    exact gs_res (𝟙 X) y _ (mem_chart_one (𝟙 X) y hy) _
  · obtain ⟨k, rfl⟩ : ∃ k', j = fun _ => k' := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
    exact fn_ext fun y hy => (h y k (hj hy)).trans (gs_res (𝟙 X) y hj hy _).symm

theorem exists_h0Sec_left (θ : L.Sec) : ∃ σ : H0 L 1, SectionOfLineBundleOne σ θ := by
  obtain ⟨t, ht⟩ := exists_powerSection_of_chartFunctions θ
  exact ⟨t, sectionOfLineBundleOne_iff_germs_eq.2 fun y k hy => ht _ (𝟙 X) y k hy⟩

theorem exists_h0Sec_right (σ : H0 L 1) : ∃ θ : L.Sec, SectionOfLineBundleOne σ θ := by
  have le : ∀ k : L.ι, L.U k ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => k) :=
    fun k y hy => mem_chart_one (𝟙 X) y hy
  refine ⟨⟨fun k => resG X (le k) (σ.f fun _ => k), fun i j => fn_ext fun y hy => ?_⟩,
    sectionOfLineBundleOne_iff_germs_eq.2 fun y k hy => (gs_res (𝟙 X) y (le k) hy _).symm⟩
  refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le i) hy.1 _)).trans
    ((gs_compat σ (𝟙 X) y (le i hy.1) (le j hy.2)).trans (Eq.symm ((gs_mul (𝟙 X) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val (Eq.symm ?_)))
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le j) hy.2 _))))))
  refine (gm_linComb L _ _ (𝟙 X) y _ _ (le i hy.1) (le j hy.2)).trans ?_
  simp

def Same {L' : LB X} (σ : H0 L 1) (θ : L'.Sec) : Prop := ∃ θ' : L.Sec, SectionOfLineBundleOne σ θ' ∧ HEq θ θ'

variable {L' : LB X}

theorem exists_same_left (h : L = L') (θ : L'.Sec) : ∃ σ : H0 L 1, Same σ θ := by
  subst h
  obtain ⟨σ, hσ⟩ := exists_h0Sec_left θ
  exact ⟨σ, θ, hσ, HEq.rfl⟩

theorem exists_same_right (h : L = L') (σ : H0 L 1) : ∃ θ : L'.Sec, Same σ θ := by
  subst h
  obtain ⟨θ, hθ⟩ := exists_h0Sec_right σ
  exact ⟨θ, θ, hθ, HEq.rfl⟩

theorem Same.unique (h : L = L') {σ : H0 L 1} {θ₁ θ₂ : L'.Sec} (h₁ : Same σ θ₁) (h₂ : Same σ θ₂) : θ₁ = θ₂ := by
  subst h
  obtain ⟨_, a₁, ⟨⟩⟩ := h₁
  obtain ⟨_, a₂, ⟨⟩⟩ := h₂
  have e : θ₁.f = θ₂.f := funext fun k => fn_ext fun y hy =>
    (sectionOfLineBundleOne_iff_germs_eq.1 a₁ y k hy).symm.trans (sectionOfLineBundleOne_iff_germs_eq.1 a₂ y k hy)
  cases θ₁
  cases θ₂
  cases e
  rfl

theorem Same.mul_iff (h : L = L') {R : Type} [CommRing R] (p : X ⟶ Sp R) (r : R) {σ σ' : H0 L 1} {θ θ' : L'.Sec}
    (h₁ : Same σ θ) (h₂ : Same σ' θ') : SecIsMul p r σ' σ ↔ ∀ i, θ'.f i = constFn p _ r * θ.f i := by
  subst h
  obtain ⟨_, a₁, ⟨⟩⟩ := h₁
  obtain ⟨_, a₂, ⟨⟩⟩ := h₂
  refine ⟨fun hm k => fn_ext fun y hy => ?_, fun hm j => ?_⟩
  · refine (sectionOfLineBundleOne_iff_germs_eq.1 a₂ y k hy).symm.trans
      ((secIsMul_gs hm (𝟙 X) y (fun _ => k) (mem_chart_one (𝟙 X) y hy)).trans (Eq.symm ?_))
    exact (gs_mul (𝟙 X) y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_constFn p _ (𝟙 X) y hy r) (sectionOfLineBundleOne_iff_germs_eq.1 a₁ y k hy).symm)
  · obtain ⟨k, rfl⟩ : ∃ k', j = fun _ => k' := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
    rw [ThickDiv.resTop_scal]
    refine fn_ext fun y hy => ?_
    have hk : y ∈ L.U k := Set.mem_iInter.1 hy 0
    refine (sectionOfLineBundleOne_iff_germs_eq.1 a₂ y k hk).trans ((congrArg _ (hm k)).trans ((gs_mul (𝟙 X) y _ hk _ _).trans
      (Eq.symm ((gs_mul (𝟙 X) y _ hy _ _).trans (congrArg₂ (· * ·) ?_ (sectionOfLineBundleOne_iff_germs_eq.1 a₁ y k hk))))))
    exact (gs_constFn p _ (𝟙 X) y hy r).trans (gs_constFn p _ (𝟙 X) y hk r).symm

theorem Same.mem_nonzeroLocus (h : L = L') {σ : H0 L 1} {θ : L'.Sec} (h₁ : Same σ θ) {y : X}
    (hy : y ∈ nonzeroLocus σ) : y ∈ nonzeroLocus θ := by
  subst h
  obtain ⟨_, a₁, ⟨⟩⟩ := h₁
  obtain ⟨j, hj, hu⟩ := (SectionBaseChange.mem_nonzeroLocus σ _).1 hy
  obtain ⟨k, rfl⟩ : ∃ k', j = fun _ => k' := ⟨j 0, funext fun i => congrArg j (Subsingleton.elim i 0)⟩
  have hk : y ∈ L.U k := Set.mem_iInter.1 hj 0
  exact (SectionBaseChange.mem_nonzeroLocus θ _).2 ⟨k, hk, sectionOfLineBundleOne_iff_germs_eq.1 a₁ y k hk ▸ hu⟩

end General

theorem isPullTerm_mul {R A : Type} [CommRing R] [IsDomain R] [CommRing A] {D : DegPre R} {B₀ : Scheme.{0}}
    {M₀ : LB B₀} {φ : D.P.A.left ⟶ B₀} {w : LB.Iso D.P.L (M₀.pull φ)} {th th' : M₀.Sec} (q : B₀ ⟶ Sp A)
    (f : A →+* R) (hq : φ ≫ q = D.P.A.hom ≫ spMap f) (r : A) (hm : ∀ j, th'.f j = constFn q _ r * th.f j)
    {t t' : D.SecB 1 0} (h : IsPullTerm D φ w th t) (ht : SecIsMul D.P.A.hom (f r) t' t) :
    IsPullTerm D φ w th' t' := by
  refine isPullTerm_iff.2 fun y J j₀ hJ hy => ?_
  rw [hm, gs_mul φ y _ hy, gs_constFn q _ φ y hy, isPullTerm_iff.1 h y J j₀ hJ hy, sval_of_secIsMul ht _ y hJ, hq,
    cst_comp, Category.id_comp, mul_left_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {A : Type} [CommRing A] [IsDomain A] {b : O →+* A} {a : ArcIn Dw l β A b} {χ : Sp (PowerSeries A) ⟶ Y.X}

theorem thetaOf_iff (W : Wit Y a χ) (th : a.D₀.P.L.Sec) (θ : LB.Sec W.t.PP.L) : ThetaOf W th θ ↔
    ∃ (σ : H0 W.P.U.LG.L 1) (fam : ∀ x, W.P.D.toPre.SecB 1 x), (∀ n, W.P.U.toUnifPre.ExpandsAt n 1 σ fam) ∧
      IsPullTerm W.P.D.toPre W.φ W.w th (fam 0) ∧ Same σ θ :=
  ⟨fun ⟨σ, fam, θ', h₁, h₂, h₃⟩ => ⟨σ, fam, h₁, h₂, θ', h₃⟩, fun ⟨σ, fam, h₁, h₂, θ', h₃⟩ => ⟨σ, fam, θ', h₁, h₂, h₃⟩⟩

theorem secIsMul_of_weight_zero {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {P : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D P G)
    (σ σ' : SecOver G.hom (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ))))
    (f f' : ∀ α, SecBMod D.toPre 1 α) (hE : ∀ e, U.ExpandsAt e 1 σ f) (hE' : ∀ e, U.ExpandsAt e 1 σ' f')
    (hu : ∀ (σ₁ : H0 U.LG.L 1) (f₁ : ∀ α, D.toPre.SecB 1 α), f₁ 0 = f 0 → (∀ e, U.ExpandsAt e 1 σ₁ f₁) → σ₁ = σ)
    (r : R) (h : SecIsMul D.toPre.P.A.hom r (f' 0) (f 0)) : SecIsMul G.hom r σ' σ := by
  have h₀ : f' 0 = r • f 0 := (secIsMul_iff _ _ _ _).1 h
  have h₁ : (f' + (1 - r) • f) 0 = f 0 := by
    rw [Pi.add_apply, Pi.smul_apply, h₀, ← add_smul, add_sub_cancel, one_smul]
  have h₂ : σ' + (1 - r) • σ = σ :=
    hu _ _ h₁ fun e => expandsAt_add U (hE' e) (expandsAt_smul U (1 - r) (hE e))
  refine (secIsMul_iff _ _ _ _).2 ?_
  rw [sub_smul, one_smul] at h₂
  rw [← sub_eq_zero, ← add_left_inj σ, zero_add]
  refine Eq.trans ?_ h₂
  abel

end GlobalTheory.ThetaOfArc

namespace GlobalTheory

open GlobalTheory.ThetaUnit GlobalTheory.ThetaOfArc IsLocalRing

theorem existsUnique_thetaOf : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (th : a.D₀.P.L.Sec), ThNZ th → (∃! θ : LB.Sec W.t.PP.L, ThetaOf W th θ) ∧ ∀ θ, ThetaOf W th θ → (∀ s : LB.Sec W.t.PP.L, ∃! r : PowerSeries A, ∀ i, s.f i = constFn W.t.G.hom _ r * θ.f i) ∧ (∃ g : W.t.G.left, W.t.G.hom g = IsLocalRing.closedPoint (PowerSeries A) ∧ g ∈ Out.nonzeroLocus θ) ∧ ∀ (r : A) (th' : a.D₀.P.L.Sec) (θ' : LB.Sec W.t.PP.L), ThMul r th th' → (ThetaOf W th' θ' ↔ ∀ i, θ'.f i = constFn W.t.G.hom _ (PowerSeries.C (R := A) r) * θ.f i) := by
  intro hL _ E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W th hth
  have hI : Ideal.span {(PowerSeries.X : PowerSeries A)} ≤ maximalIdeal (PowerSeries A) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_maximalIdeal, mem_nonunits_iff,
      PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
  have hb : W.P.U.LG.L = W.t.PP.L := congrArg (fun q => q.L) W.P.bundle
  obtain ⟨⟨t, ht, htu⟩, hnz⟩ := existsUnique_pullTerm W th
  have ht₀ := hnz t ht hth (closedPoint _)
  obtain ⟨σ, fam, rfl, hE, hmem, huq, hgen, -⟩ := exists_theta_arc hL.globalFns hL.secBaseChange hI W t ht₀
  have key : ∀ θ, ThetaOf W th θ ↔ Same σ θ := fun θ => by
    rw [thetaOf_iff]
    refine ⟨fun ⟨σ₁, f₁, h₁, h₂, h₃⟩ => huq σ₁ f₁ (htu _ h₂) h₁ ▸ h₃, fun h => ⟨σ, fam, hE, ht, h⟩⟩
  refine ⟨?_, fun θ hθ => ⟨fun s => ?_, ?_, fun r th' θ' hm => ?_⟩⟩
  · obtain ⟨θ, hθ⟩ := exists_same_right hb σ
    exact ⟨θ, (key θ).2 hθ, fun θ' h => ((key θ').1 h).unique hb hθ⟩
  · obtain ⟨s', hs'⟩ := exists_same_left hb s
    simpa only [((key θ).1 hθ).mul_iff hb W.t.G.hom _ hs'] using hgen s'
  · obtain ⟨g, hg, hn⟩ := exists_mem_nonzeroLocus hI W.P.U.toUnifPre (hE 0) ht₀ hmem
    exact ⟨g, hg, ((key θ).1 hθ).mem_nonzeroLocus hb hn⟩
  · choose fam' hfam' using fun α =>
      IntegralExpansion.exists_secIsMul W.P.D.toPre.P.A.hom (PowerSeries.C (R := A) r) (fam α)
    have hp : IsPullTerm W.P.D.toPre W.φ W.w th' (fam' 0) :=
      isPullTerm_mul a.D₀.P.A.hom _ W.spec.1.1.w r hm ht (hfam' 0)
    rw [thetaOf_iff]
    refine ⟨fun ⟨σ₁, f₁, h₁, h₂, h₃⟩ => (((key θ).1 hθ).mul_iff hb W.t.G.hom _ h₃).1 ?_, fun h => ?_⟩
    · exact secIsMul_of_weight_zero W.P.U.toUnifPre σ σ₁ fam f₁ hE h₁ huq _
        (h₂.unique a.D₀.P.isLB hp ▸ hfam' 0)
    · obtain ⟨σ', hσ'⟩ := exists_same_left hb θ'
      exact ⟨σ', fam', fun n => expandsAt_secIsMul _ _ _ _ _ _ n 1 _ σ σ' fam fam'
        ((((key θ).1 hθ).mul_iff hb W.t.G.hom _ hσ').2 h) hfam' (hE n), hp, hσ'⟩

end GlobalTheory
