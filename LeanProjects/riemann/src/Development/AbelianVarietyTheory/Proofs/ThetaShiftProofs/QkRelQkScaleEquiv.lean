import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm

noncomputable section

namespace GlobalTheory.TauTwist

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorusExt

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {ψ : PsiFam D} {hψ : ∀ χ, (ψ χ).IsGen}
  {F : Type} [Field F] [Algebra (FractionRing R) F]

attribute [local instance] gtGroup

def PsiRel (D : DegPre R) (ψ : PsiFam D) (q : D.X → (FractionRing R)ˣ) : Prop :=
  ∀ (χ : D.X) (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J), Good D.P.L z J →
    val (ψ χ) r z J = unitAt r z (q χ) * val (D.psi χ) r z J

theorem psiRel_rescale (D : DegPre R) (q : D.X → (FractionRing R)ˣ) : PsiRel D (rescale D q).psi q :=
  fun χ _ r _ _ hJ => val_psi_rescale q χ r hJ

theorem PsiRel.symm {q : D.X → (FractionRing R)ˣ} (h : PsiRel D ψ q) :
    PsiRel (withPsi D ψ hψ) D.psi fun χ => (q χ)⁻¹ := fun χ Z r z J hJ => by
  have e : val ((withPsi D ψ hψ).psi χ) r z J = _ := h χ Z r z J hJ
  rw [e, map_inv, inv_mul_cancel_left]

theorem PsiRel.val_tau {q : D.X → (FractionRing R)ˣ} (h : PsiRel D ψ q) {a b : D.X} {x : (FractionRing R)ˣ}
    (hx : q (a + b) = q a * q b * x) {Z : Scheme.{0}} (r : Z ⟶ (TK R).left) {z : Z} {J} (hJ : Good D.P.L z J) :
    val ((withPsi D ψ hψ).tau a b) r z J = unitAt r z x * val (D.tau a b) r z J := by
  have e := TauTwist.val_tau (withPsi D ψ hψ) a b r hJ
  have e₁ : val ((withPsi D ψ hψ).psi (a + b)) r z J = _ := h (a + b) Z r z J hJ
  have e₂ : val ((withPsi D ψ hψ).psi a) r z J = _ := h a Z r z J hJ
  have e₃ : val ((withPsi D ψ hψ).psi b) r z J = _ := h b Z r z J hJ
  have e₄ := TauTwist.val_tau D a b r hJ
  rw [hx, map_mul, map_mul] at e₁
  have e₅ : val (withPsi D ψ hψ).rigK r z J = val D.rigK r z J := rfl
  rw [e₁, e₂, e₃, e₅] at e
  rw [e, e₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

def GtRel (g : GtPtF D F) (g' : GtPtF (withPsi D ψ hψ) F) (a : D.X → Fˣ) : Prop :=
  g'.b = g.b ∧ ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (g'.s χ) (scaleGen (unitOn (a χ)) (g.s χ))

def gtScale (ψ : PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) (g : GtPtF D F) (a : D.X → Fˣ)
    (ha : ∀ χ χ', a (χ + χ') = a χ * a χ') : GtPtF (withPsi D ψ hψ) F where
  b := g.b
  s χ := scaleGen (unitOn (a χ)) (g.s χ)
  isGen χ := scaleGen_isGen _ _ (g.isGen χ)
  s_zero := corr_of_val D.P.isLB fun y J hJ => by
    have h₀ := ha 0 0
    rw [add_zero] at h₀
    refine (val_scale (a 0) (g.s 0) _ hJ).trans ?_
    rw [mul_eq_left.1 h₀.symm, map_one, _root_.one_mul]
    exact val_corr hJ g.s_zero _
  mult χ χ' := corr_of_val D.P.isLB fun y J hJ => by
    have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (g.mult χ χ') (𝟙 _)).trans (val_mul hJ _ _ _))
    refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (val_scale (a (χ + χ')) (g.s (χ + χ')) _ hJ) rfl).trans
      (Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_scale (a χ) (g.s χ) _ hJ)
        (val_scale (a χ') (g.s χ') _ hJ))).symm))
    rw [ha, map_mul, _root_.mul_mul_mul_comm, _root_.mul_assoc]
    exact congrArg _ e

theorem GtRel.val {g : GtPtF D F} {g' : GtPtF (withPsi D ψ hψ) F} {a : D.X → Fˣ} (h : GtRel g g' a) (χ : D.X)
    {Z : Scheme.{0}} (r : Z ⟶ (TF (R := R) F).left) {z : Z} {J} (hJ : Good D.P.L z J) :
    val (g'.s χ) r z J = unitAt r z (a χ) * val (g.s χ) r z J :=
  (val_corr hJ (h.2 χ) r).trans (val_scale (a χ) (g.s χ) r hJ)

theorem gtRel_of_val {g : GtPtF D F} {g' : GtPtF (withPsi D ψ hψ) F} {a : D.X → Fˣ} (hb : g'.b = g.b)
    (h : ∀ χ y J, Good D.P.L y J → charVal g' χ y J = unitAt (𝟙 (TF (R := R) F).left) y (a χ) * charVal g χ y J) :
    GtRel g g' a :=
  ⟨hb, fun χ => corr_of_val D.P.isLB fun y J hJ => (h χ y J hJ).trans (val_scale (a χ) (g.s χ) _ hJ).symm⟩

theorem gtRel_gtScale (g : GtPtF D F) (a : D.X → Fˣ) (ha : ∀ χ χ', a (χ + χ') = a χ * a χ') :
    GtRel g (gtScale ψ hψ g a ha) a :=
  gtRel_of_val rfl fun χ _ _ hJ => val_scale (a χ) (g.s χ) _ hJ

namespace GtRel

variable {g g₁ g₂ g₃ : GtPtF D F} {g' g₁' g₂' g₃' : GtPtF (withPsi D ψ hψ) F} {a a₁ a₂ a₃ : D.X → Fˣ}

theorem symm (h : GtRel g g' a) : GtRel (D := withPsi D ψ hψ) (ψ := D.psi) (hψ := D.psi_gen) g' g fun χ => (a χ)⁻¹ :=
  gtRel_of_val h.1.symm fun χ y J hJ => by
    have e : charVal g' χ y J = _ := h.val χ _ hJ
    rw [e, map_inv, inv_mul_cancel_left]

theorem unique (h₁ : GtRel g g₁' a) (h₂ : GtRel g g₂' a) : g₁' = g₂' :=
  gt_ext_val (h₁.1.trans h₂.1.symm) fun χ _ _ hJ => (h₁.val χ _ hJ).trans (h₂.val χ _ hJ).symm

theorem isAdd (h₁ : GtRel g₁ g₁' a₁) (h₂ : GtRel g₂ g₂' a₂) (h₃ : GtRel g₃ g₃' a₃) (ha : ∀ χ, a₃ χ = a₁ χ * a₂ χ)
    (h : g₁.IsAdd g₂ g₃) : g₁'.IsAdd g₂' g₃' := by
  obtain ⟨b, v⟩ := (isAdd_iff_val _ _ _).1 h
  refine (isAdd_iff_val _ _ _).2 ⟨h₃.1.trans (b.trans (congrArg₂ (· * ·) h₁.1 h₂.1).symm), fun χ y J hJ => ?_⟩
  have e₁ : charVal g₁' χ y J = _ := h₁.val χ _ hJ
  have e₂ : charVal g₂' χ y J = _ := h₂.val χ _ hJ
  have e₃ : charVal g₃' χ y J = _ := h₃.val χ _ hJ
  rw [e₁, e₂, e₃, h₁.1, h₂.1, ha, map_mul, _root_.mul_mul_mul_comm, _root_.mul_assoc]
  exact congrArg _ (v χ y J hJ)

theorem add (h₁ : GtRel g₁ g₁' a₁) (h₂ : GtRel g₂ g₂' a₂) : GtRel (g₁ + g₂) (g₁' + g₂') fun χ => a₁ χ * a₂ χ := by
  refine gtRel_of_val ((add_b g₁' g₂').trans ((congrArg₂ (· * ·) h₁.1 h₂.1).trans (add_b g₁ g₂).symm))
    fun χ y J hJ => ?_
  have e₁ : charVal g₁' χ y J = _ := h₁.val χ _ hJ
  have e₂ : charVal g₂' χ y J = _ := h₂.val χ _ hJ
  have e := add_val g₁' g₂' χ hJ
  rw [e₁, e₂, h₁.1, h₂.1, _root_.mul_mul_mul_comm, ← map_mul] at e
  exact mul_right_cancel (e.trans ((congrArg _ (add_val g₁ g₂ χ hJ).symm).trans (_root_.mul_assoc _ _ _).symm))

theorem zero : GtRel (0 : GtPtF D F) (0 : GtPtF (withPsi D ψ hψ) F) fun _ => 1 :=
  gtRel_of_val ((zero_b (D := withPsi D ψ hψ)).trans (zero_b (D := D)).symm) fun χ y J hJ => by
    rw [zero_val (D := withPsi D ψ hψ) χ hJ, zero_val (D := D) χ hJ, map_one, _root_.mul_one]

theorem nsmul (h : GtRel g g' a) (k : ℕ) : GtRel (k • g) (k • g') fun χ => a χ ^ k := by
  induction k with
  | zero => simpa only [zero_nsmul, pow_zero] using zero
  | succ k ih => simpa only [succ_nsmul, pow_succ] using ih.add h

theorem isNsmul (h₁ : GtRel g₁ g₁' a₁) (h₂ : GtRel g₂ g₂' a₂) {k : ℕ} (ha : ∀ χ, a₂ χ = a₁ χ ^ k)
    (h : GtPtF.IsNsmul k g₁ g₂) : GtPtF.IsNsmul k g₁' g₂' := by
  obtain rfl : a₂ = fun χ => a₁ χ ^ k := funext ha
  obtain rfl := (isNsmul_iff_eq _ _ _).1 h
  exact (isNsmul_iff_eq _ _ _).2 (h₂.unique (h₁.nsmul k))

theorem isIota {q : D.X → (FractionRing R)ˣ} (hq : PsiRel D ψ q) {x : D.X} {t : D.X → (FractionRing R)ˣ}
    (ht : ∀ χ, q (x + χ) = q x * q χ * t χ) (h : GtRel g g' a)
    (ha : ∀ χ, a χ = Units.map (algebraMap (FractionRing R) F).toMonoidHom (t χ)) (hι : GtPtF.IsIota x g) :
    GtPtF.IsIota (D := withPsi D ψ hψ) x g' := by
  obtain ⟨b, v⟩ := (isIota_iff_val _ _).1 hι
  refine (isIota_iff_val _ _).2 ⟨h.1.trans b, fun χ y J hJ => (h.val χ _ hJ).trans
    (Eq.trans (congrArg₂ (· * ·) ?_ (v χ y J hJ)) (hq.val_tau (ht χ) _ hJ).symm)⟩
  rw [ha]
  exact (unitAt_spMap _ (algebraMap (FractionRing R) F) y _).symm

theorem gtAct {O : Type} [CommRing O] [StarRing O] [Module O D.X] {oa : D.OAct O} {oa' : (withPsi D ψ hψ).OAct O}
    (ho : oa'.onB = oa.onB) {x : O} (h₁ : GtRel g₁ g₁' a₁) (h₂ : GtRel g₂ g₂' a₂) (ha : ∀ χ, a₂ χ = a₁ (star x • χ))
    (h : GtAct oa x g₁ g₂) : GtAct oa' x g₁' g₂' := by
  obtain ⟨B, c₁, c₂⟩ := oa'
  obtain rfl : B = oa.onB := ho
  refine ⟨h₂.1.trans (h.1.trans (congrArg (· ≫ oa.onB.act x) h₁.1.symm)), fun u hu u₀ χ =>
    corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (h.2 u hu u₀ χ) (𝟙 _))
  rw [val_pull hJ] at e
  refine (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) (h₁.val _ _ hJ) (val_pull hJ _ _ _)).trans
    (Eq.trans ?_ (h₂.val χ _ hJ).symm))
  rw [ha, h₁.1, _root_.mul_assoc]
  exact congrArg _ e

end GtRel

def QkRel {k : ℕ} (r : D.X → D.X → Fˣ) (p : QkPt D F k) (p' : QkPt (withPsi D ψ hψ) F k) : Prop :=
  p'.y = p.y ∧ GtRel p.g p'.g (r p.y)

theorem QkRel.symm {k : ℕ} {r : D.X → D.X → Fˣ} {p : QkPt D F k} {p' : QkPt (withPsi D ψ hψ) F k} (h : QkRel r p p') :
    QkRel (D := withPsi D ψ hψ) (ψ := D.psi) (hψ := D.psi_gen) (fun y x => (r y x)⁻¹) p' p :=
  ⟨h.1.symm, by rw [h.1]; exact h.2.symm⟩

theorem QkRel.unique {k : ℕ} {r : D.X → D.X → Fˣ} {p : QkPt D F k} {p₁ p₂ : QkPt (withPsi D ψ hψ) F k}
    (h₁ : QkRel r p p₁) (h₂ : QkRel r p p₂) : p₁ = p₂ := qk_ext (h₁.1.trans h₂.1.symm) (h₁.2.unique h₂.2)

theorem QkRel.qkExt {k : ℕ} {F' : Type} [Field F'] [Algebra (FractionRing R) F'] {f : F →+* F'} {r : D.X → D.X → Fˣ}
    {r' : D.X → D.X → F'ˣ} (hr : ∀ y x, r' y x = Units.map f.toMonoidHom (r y x)) {p : QkPt D F k} {q : QkPt D F' k}
    {p' : QkPt (withPsi D ψ hψ) F k} {q' : QkPt (withPsi D ψ hψ) F' k} (hp : QkRel r p p') (hq : QkRel r' q q')
    (h : QkExt f p q) : QkExt f p' q' := by
  refine ⟨hq.1.trans (h.1.trans hp.1.symm), ?_, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  · rw [hq.2.1, hp.2.1]; exact h.2.1
  · refine (hq.2.val χ _ hJ).trans (Eq.trans (congrArg₂ (· * ·) ?_ ((val_corr hJ (h.2.2 χ) _).trans (val_pull hJ _ _ _)))
      ((val_pull hJ _ _ _).trans (hp.2.val χ _ hJ)).symm)
    rw [hr, h.1]
    exact (unitAt_spMap _ f y _).symm

section Root

variable {O : Type} [CommRing O] [StarRing O] [Module O D.X] {w : O} {t : D.X → D.X → (FractionRing R)ˣ} {k : ℕ}
  {r : D.X → D.X → Fˣ}

variable (O) in

def IsRootForm {X K F : Type} [AddCommGroup X] [Module O X] [Field K] [Field F] [Algebra K F] (k : ℕ) (t : X → X → Kˣ)
    (r : X → X → Fˣ) : Prop :=
  IsScalarForm O r ∧ ∀ y x, r y x ^ k = Units.map (algebraMap K F).toMonoidHom (t y x)

theorem IsRootForm.inv {X K F : Type} [AddCommGroup X] [Module O X] [Field K] [Field F] [Algebra K F] {k : ℕ}
    {t : X → X → Kˣ} {r : X → X → Fˣ} (h : IsRootForm O k t r) :
    IsRootForm O k (fun y x => (t y x)⁻¹) fun y x => (r y x)⁻¹ :=
  ⟨h.1.inv, fun y x => by rw [inv_pow, h.2, map_inv]⟩

def qkScale (hw : w + star w = 1) (ht : IsScalarForm O t) (hq : PsiRel D ψ fun y => t y (w • y))
    (hr : IsRootForm O k t r) (hψ : ∀ χ, (ψ χ).IsGen) (p : QkPt D F k) : QkPt (withPsi D ψ hψ) F k where
  y := p.y
  g := gtScale ψ hψ p.g (r p.y) (hr.1.add_right p.y)
  eq := by
    obtain ⟨h, h₁, h₂⟩ := p.eq
    have e := gtRel_gtScale (hψ := hψ) h (fun χ => r p.y χ ^ k) ((hr.1.pow k).add_right p.y)
    exact ⟨_, (gtRel_gtScale _ _ _).isNsmul e (fun _ => rfl) h₁, e.isIota hq (ht.refine_add hw p.y) (hr.2 p.y) h₂⟩

variable (hw : w + star w = 1) (ht : IsScalarForm O t) (hq : PsiRel D ψ fun y => t y (w • y)) (hr : IsRootForm O k t r)

theorem qkRel_qkScale (p : QkPt D F k) : QkRel r p (qkScale hw ht hq hr hψ p) :=
  ⟨rfl, gtRel_gtScale _ _ (hr.1.add_right p.y)⟩

namespace QkRel

variable {p₁ p₂ p₃ : QkPt D F k} {p₁' p₂' p₃' : QkPt (withPsi D ψ hψ) F k}
include hw ht hq hr

theorem equiv (h₁ : QkRel r p₁ p₁') (h₂ : QkRel r p₂ p₂') (h : QkPt.Equiv D F p₁ p₂) :
    QkPt.Equiv (withPsi D ψ hψ) F p₁' p₂' := by
  obtain ⟨z, hy, g, hι, hg⟩ := h
  have e := gtRel_gtScale (hψ := hψ) g (fun χ => r z χ ^ k) ((hr.1.pow k).add_right z)
  refine ⟨z, h₂.1.trans (hy.trans (congrArg (· + k • z) h₁.1.symm)), _,
    e.isIota hq (ht.refine_add hw z) (hr.2 z) hι, h₁.2.isAdd e h₂.2 (fun χ => ?_) hg⟩
  rw [hy, hr.1.add_left, hr.1.nsmul_left]

theorem qkAdd (h₁ : QkRel r p₁ p₁') (h₂ : QkRel r p₂ p₂') (h₃ : QkRel r p₃ p₃') (h : QkAdd p₁ p₂ p₃) :
    QkAdd p₁' p₂' p₃' := by
  obtain ⟨q, hy, hg, he⟩ := h
  have e := qkRel_qkScale (hψ := hψ) hw ht hq hr q
  refine ⟨_, hy.trans (congrArg₂ (· + ·) h₁.1 h₂.1).symm, h₁.2.isAdd h₂.2 e.2 (fun χ => ?_) hg,
    equiv hw ht hq hr e h₃ he⟩
  rw [hy, hr.1.add_left]

theorem qkAct {oa : D.OAct O} {oa' : (withPsi D ψ hψ).OAct O} (ho : oa'.onB = oa.onB) {x : O} (h₁ : QkRel r p₁ p₁')
    (h₂ : QkRel r p₂ p₂') (h : QkAct oa x p₁ p₂) : QkAct oa' x p₁' p₂' := by
  obtain ⟨q, hy, hg, he⟩ := h
  have e := qkRel_qkScale (hψ := hψ) hw ht hq hr q
  refine ⟨_, hy.trans (congrArg (x • ·) h₁.1).symm, h₁.2.gtAct ho e.2 (fun χ => ?_) hg, equiv hw ht hq hr e h₂ he⟩
  rw [hy, hr.1.bal]

theorem equiv_iff (h₁ : QkRel r p₁ p₁') (h₂ : QkRel r p₂ p₂') :
    QkPt.Equiv (withPsi D ψ hψ) F p₁' p₂' ↔ QkPt.Equiv D F p₁ p₂ :=
  ⟨equiv (D := withPsi D ψ hψ) hw ht.inv hq.symm hr.inv h₁.symm h₂.symm, equiv hw ht hq hr h₁ h₂⟩

theorem qkAdd_iff (h₁ : QkRel r p₁ p₁') (h₂ : QkRel r p₂ p₂') (h₃ : QkRel r p₃ p₃') :
    QkAdd p₁' p₂' p₃' ↔ QkAdd p₁ p₂ p₃ :=
  ⟨qkAdd (D := withPsi D ψ hψ) hw ht.inv hq.symm hr.inv h₁.symm h₂.symm h₃.symm, qkAdd hw ht hq hr h₁ h₂ h₃⟩

theorem qkAct_iff {oa : D.OAct O} {oa' : (withPsi D ψ hψ).OAct O} (ho : oa'.onB = oa.onB) {x : O} (h₁ : QkRel r p₁ p₁')
    (h₂ : QkRel r p₂ p₂') : QkAct oa' x p₁' p₂' ↔ QkAct oa x p₁ p₂ :=
  ⟨qkAct (D := withPsi D ψ hψ) hw ht.inv hq.symm hr.inv ho.symm h₁.symm h₂.symm, qkAct hw ht hq hr ho h₁ h₂⟩

end QkRel

def qkScaleEquiv (hψ : ∀ χ, (ψ χ).IsGen) : QkPt D F k ≃ QkPt (withPsi D ψ hψ) F k where
  toFun := qkScale hw ht hq hr hψ
  invFun := qkScale (D := withPsi D ψ hψ) hw ht.inv hq.symm hr.inv D.psi_gen
  left_inv p := (qkRel_qkScale (D := withPsi D ψ hψ) hw ht.inv hq.symm hr.inv _).unique (qkRel_qkScale hw ht hq hr p).symm
  right_inv p := (qkRel_qkScale hw ht hq hr _).unique (by
    simpa only [inv_inv] using (qkRel_qkScale (D := withPsi D ψ hψ) (hψ := D.psi_gen) hw ht.inv hq.symm hr.inv p).symm)

theorem qkRel_qkScaleEquiv (p : QkPt D F k) : QkRel r p (qkScaleEquiv hw ht hq hr hψ p) := qkRel_qkScale hw ht hq hr p

end Root

end GlobalTheory.TauTwist
