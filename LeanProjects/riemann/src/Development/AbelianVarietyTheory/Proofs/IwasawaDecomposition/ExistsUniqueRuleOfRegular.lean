import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromTestAndValLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PointsDetectFrobeniusSections
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyAlgHomAlgebraicClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqOfLocallyFractionOnGenerisations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegrallyClosedMvPolynomialOfFinite

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.FlagTan

namespace GlobalTheory.ShFam

namespace Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

section Cpt

variable (C : FlagCpt Z e)

def Fk : Type := C.Y.Fn

instance : Field (Fk C) := inferInstanceAs (Field C.Y.Fn)

instance : Algebra c.F (Fk C) := RingHom.toAlgebra (constF e C.Y : c.F →+* C.Y.Fn)

def St (y : C.Y.X) : Type := C.Y.X.presheaf.stalk y

instance (y : C.Y.X) : CommRing (St C y) := inferInstanceAs (CommRing (C.Y.X.presheaf.stalk y))

instance (y : C.Y.X) : IsLocalRing (St C y) := inferInstanceAs (IsLocalRing (C.Y.X.presheaf.stalk y))

def pt (y : C.Y.X) : Sp (St C y) ⟶ C.Y.X := stalkPt C.Y y

instance (y : C.Y.X) : Mono (pt C y) := inferInstanceAs (Mono (C.Y.X.fromSpecStalk y))

instance (y : C.Y.X) : Algebra c.F (St C y) := (Spec.preimage (pt C y ≫ C.π ≫ genStr Z)).hom.toAlgebra

theorem pt_str (y : C.Y.X) : pt C y ≫ C.π ≫ genStr Z = spMap (algebraMap c.F (St C y)) := (Spec.map_preimage _).symm

def gpt : Sp (Fk C) ⟶ C.Y.X := genericPt C.Y

def fr0 : FrPt Xo c (Fk C) := C.y0

theorem frame_point_over : GlobalTheory.AllWt.ptF (fr0 C) ≫ Z.jQ = gpt C ≫ C.π := C.y0_x

theorem str_of_over {T : Type} [CommRing T] [Algebra c.F T] {z : FrPt Xo c T} {x : Sp T ⟶ gen Z}
    (h : GlobalTheory.AllWt.ptF z ≫ Z.jQ = x) : x ≫ genStr Z = spMap (algebraMap c.F T) := by
  rw [← h, Category.assoc, Z.jQ_over, ptF_snd]

variable {C} in

def algOf {T : Type} [CommRing T] [Algebra c.F T] {y : C.Y.X} (ψ : St C y →+* T) {p : Sp T ⟶ C.Y.X}
    (h : spMap ψ ≫ pt C y = p) (hp : p ≫ C.π ≫ genStr Z = spMap (algebraMap c.F T)) : St C y →ₐ[c.F] T :=
  { ψ with commutes' := fun a => DFunLike.congr_fun (sp_inj (f := ψ.comp (algebraMap c.F (St C y))) (by
      rw [← sp_comp, ← pt_str, ← Category.assoc, h, hp])) a }

def toFkR (y : C.Y.X) : St C y →+* Fk C := algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField

theorem toFkR_pt (y : C.Y.X) : spMap (toFkR C y) ≫ pt C y = gpt C :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)

def toFk (y : C.Y.X) : St C y →ₐ[c.F] Fk C :=
  algOf (toFkR C y) (toFkR_pt C y) (by rw [← Category.assoc]; exact str_of_over (frame_point_over C))

theorem toFk_pt (y : C.Y.X) : spMap (toFk C y).toRingHom ≫ pt C y = gpt C := toFkR_pt C y

theorem toFk_injective (y : C.Y.X) : Function.Injective (toFk C y) :=
  IsFractionRing.injective (C.Y.X.presheaf.stalk y) C.Y.X.functionField

variable {C}

theorem exists_factor {T : Type} [CommRing T] [IsLocalRing T] [Algebra c.F T] (p : Sp T ⟶ C.Y.X)
    (hp : p ≫ C.π ≫ genStr Z = spMap (algebraMap c.F T)) :
    ∃ (y : C.Y.X) (ψ : St C y →ₐ[c.F] T), spMap ψ.toRingHom ≫ pt C y = p ∧ p (IsLocalRing.closedPoint T) = y :=
  have h : spMap (R := St C _) (Scheme.stalkClosedPointTo p).hom ≫ pt C _ = p :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk p
  ⟨_, algOf _ h hp, h, rfl⟩

theorem specializes_of {T : Type} [CommRing T] {y : C.Y.X} {ψ : St C y →+* T} {p : Sp T ⟶ C.Y.X}
    (h : spMap ψ ≫ pt C y = p) (s : Sp T) : p s ⤳ y := by
  have : p s ∈ Set.range (C.Y.X.fromSpecStalk y) := ⟨spMap ψ s, by rw [← h]; rfl⟩
  rwa [Scheme.range_fromSpecStalk] at this

theorem hom_eq {T : Type} [CommRing T] {y : C.Y.X} {ψ ψ' : St C y →+* T} (h : spMap ψ ≫ pt C y = spMap ψ' ≫ pt C y) :
    ψ = ψ' := sp_inj ((cancel_mono _).1 h)

theorem exists_spec {y y' : C.Y.X} (h : y' ⤳ y) : ∃ sp : St C y →ₐ[c.F] St C y',
    spMap sp.toRingHom ≫ pt C y = pt C y' ∧ ∀ a, toFk C y' (sp a) = toFk C y a := by
  have k : spMap (R := St C y) (R' := St C y') (C.Y.X.presheaf.stalkSpecializes h).hom ≫ pt C y = pt C y' :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk h
  refine ⟨algOf _ k (pt_str C y'), k, fun a => ?_⟩
  refine DFunLike.congr_fun (hom_eq (ψ := (toFk C y').toRingHom.comp (algOf _ k (pt_str C y')).toRingHom)
    (ψ' := (toFk C y).toRingHom) ?_) a
  rw [← sp_comp, Category.assoc, toFk_pt]
  exact (congrArg (_ ≫ ·) k).trans (toFk_pt C y')

theorem exists_lift_open {T : Type} [CommRing T] [IsLocalRing T] (x : Sp T ⟶ gen Z)
    (h : x (IsLocalRing.closedPoint T) ∉ genBd Z) : ∃ xF : Sp T ⟶ Xo.XF c, xF ≫ Z.jQ = x := by
  have := Z.jQ_open
  refine ⟨IsOpenImmersion.lift Z.jQ x ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨s, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint s).map x.continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range
    (not_not.1 h)

theorem x_eq_of_over {T : Type} [CommRing T] [Algebra c.F T] {z z' : FrPt Xo c T}
    (h : GlobalTheory.AllWt.ptF z' ≫ Z.jQ = GlobalTheory.AllWt.ptF z ≫ Z.jQ) : z'.x = z.x := by
  have := Z.jQ_open
  rw [← ptF_fst, ← ptF_fst, (cancel_mono _).1 h]

variable (C) in

def rationalEigenFrame : EigFrame Z (algebraMap c.F (Fk C)) (gpt C ≫ C.π ≫ genι Z) := C.f0

theorem tie0 : Comparison₂ (fr0 C) (rationalEigenFrame C) := by
  have hx : GlobalTheory.AllWt.ptF (fr0 C) ≫ Z.j = gpt C ≫ C.π ≫ genι Z := by
    rw [Model.j, ← Category.assoc, frame_point_over, Category.assoc]
  exact ⟨rfl, hx, C.flagComponentFramedPoint_frame⟩

variable (C) in

structure Chart (y : C.Y.X) (P : FrPt Xo c (St C y)) (t : Ix Dw → (Fk C)ˣ) : Prop where
  ov : GlobalTheory.AllWt.ptF P ≫ Z.jQ = pt C y ≫ C.π
  bm : BM (toFk C y) t P (fr0 C)

theorem Chart.over_j {y : C.Y.X} {P : FrPt Xo c (St C y)} {t : Ix Dw → (Fk C)ˣ} (h : Chart C y P t) :
    GlobalTheory.AllWt.ptF P ≫ Z.j = pt C y ≫ C.π ≫ genι Z := by
  rw [Model.j, ← Category.assoc, h.ov, Category.assoc]

theorem pt_closedPoint (y : C.Y.X) : pt C y (IsLocalRing.closedPoint (St C y)) = y :=
  Scheme.fromSpecStalk_closedPoint

theorem Chart.notMem {y : C.Y.X} {P : FrPt Xo c (St C y)} {t : Ix Dw → (Fk C)ˣ} (h : Chart C y P t) :
    C.π y ∉ genBd Z := fun hb => hb ⟨GlobalTheory.AllWt.ptF P (IsLocalRing.closedPoint _), (congrArg (fun g => g (IsLocalRing.closedPoint (St C y))) h.ov).trans (congrArg C.π (pt_closedPoint y))⟩

theorem exists_chart {y : C.Y.X} (hy : C.π y ∉ genBd Z) :
    ∃ P t, Chart C y P t ∧ ∀ τ i, (C.gr τ i).IsEqn y (t (some ⟨τ, i⟩)) := by
  obtain ⟨φ, f, t, hf, ht⟩ := C.gr_spec y
  obtain ⟨xF, hx⟩ := exists_lift_open (pt C y ≫ C.π) fun h => hy ((congrArg C.π (pt_closedPoint y)) ▸ h)
  have hφ : (φ : c.F →+* St C y) = algebraMap c.F (St C y) := RingHom.ext fun a => toFk_injective C y
    ((DFunLike.congr_fun hf.2.1 a).symm.trans ((toFk C y).commutes a).symm)
  obtain ⟨P, hP, hT⟩ := exists_tie_point (S := St C y) (xF := xF) (x := pt C y ≫ C.π ≫ genι Z)
    (by rw [← Z.jQ_over, ← Category.assoc, hx, Category.assoc, pt_str])
    (by rw [Model.j, ← Category.assoc, hx, Category.assoc]) hφ f
  have := Z.jQ_open
  have hx0 : (fr0 C).x = spMap (toFk C y).toRingHom ≫ P.x := by
    rw [← ptF_fst, ← ptF_fst, ← Category.assoc]
    congr 1
    rw [← cancel_mono Z.jQ, frame_point_over, Category.assoc, hP, hx, ← Category.assoc, toFk_pt]
  obtain ⟨u, hu, hu'⟩ := hT.bm_of_tri tie0 hx0 (t := t) hf
  exact ⟨P, u, ⟨hP ▸ hx, hu⟩, fun τ i => (hu' τ i).symm ▸ ht τ i⟩

theorem isEqn_LEx {y : C.Y.X} {t : Ix Dw → (Fk C)ˣ} (ht : ∀ τ i, (C.gr τ i).IsEqn y (t (some ⟨τ, i⟩)))
    {ex : Ix Dw → ℤ} (hex : ex none = 0) : (C.LEx ex).IsEqn y (chi ex t)⁻¹ := by
  have key : ∀ s : Finset (Σ τ : E →+* ℂ, Fin (Dw.mult τ)),
      (∑ x ∈ s, ex (some x) • C.gr x.1 x.2).IsEqn y (∏ x ∈ s, t (some x) ^ ex (some x) : (Fk C)ˣ) := by
    classical
    intro s
    induction s using Finset.induction_on with
    | empty => exact CartierDiv.isEqn_zero y
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      exact ((ht a.1 a.2).zsmul _).add ih
  have e : chi ex t = ∏ x, t (some x) ^ ex (some x) := by
    rw [chi, Fintype.prod_option, hex, zpow_zero, one_mul]
  exact (congrArg (fun u : (Fk C)ˣ => (C.LEx ex).IsEqn y u⁻¹) e).mpr (key Finset.univ).neg

theorem Chart.exists_coeff {y : C.Y.X} {P : FrPt Xo c (St C y)} {t : Ix Dw → (Fk C)ˣ}
    (h : Chart C y P t) {ex : Ix Dw → ℤ} (hex : ex none = 0) {s : Fk C} (hs : (C.LEx ex).RegularAt y s) :
    ∃ a, toFk C y a * chi ex t = s := by
  obtain ⟨P₂, t₂, h₂, ht⟩ := exists_chart h.notMem
  have ha := (isEqn_LEx ht hex).regularAt_iff.1 hs
  obtain ⟨v, -, rfl⟩ := BM.descend (toFk_injective C y) (x_eq_of_over (h.ov.trans h₂.ov.symm)) h₂.bm h.bm
  obtain ⟨a, ha'⟩ : ∃ a : St C y, toFk C y a = s * ((chi ex (t * umap (toFk C y) v))⁻¹ : (Fk C)ˣ) := ha
  refine ⟨a * (chi ex v : (St C y)ˣ), ?_⟩
  rw [map_mul, ha', ← chi_umap, mul_assoc, mul_assoc, ← Units.val_mul, ← Units.val_mul, chi_mul, mul_comm (chi ex t),
    inv_mul_cancel, Units.val_one, mul_one]

theorem Chart.move {y y' : C.Y.X} {P : FrPt Xo c (St C y)} {t : Ix Dw → (Fk C)ˣ} (h : Chart C y P t) (hy : y' ⤳ y) :
    ∃ (sp : St C y →ₐ[c.F] St C y') (P' : FrPt Xo c (St C y')), FrMap sp P P' ∧ Chart C y' P' t ∧
      spMap sp.toRingHom ≫ pt C y = pt C y' ∧ ∀ a, toFk C y' (sp a) = toFk C y a := by
  obtain ⟨sp, h1, h2⟩ := exists_spec hy
  obtain ⟨P', hP⟩ := exists_frMap sp P
  exact ⟨sp, P', hP, ⟨by rw [ptF_map hP.1, Category.assoc, h.ov, ← Category.assoc, h1], BM.cancel hP h.bm h2⟩, h1, h2⟩

end Cpt

section Wit

variable {C : FlagCpt Z e} {T T' : Type} [CommRing T] [Algebra c.F T] [CommRing T'] [Algebra c.F T']

variable (C) in

structure Wit (p : Sp T ⟶ C.Y.X) (z : FrPt Xo c T) : Type where
  y : C.Y.X
  ψ : St C y →ₐ[c.F] T
  P : FrPt Xo c (St C y)
  t : Ix Dw → (Fk C)ˣ
  t' : Ix Dw → Tˣ
  chart : Chart C y P t
  hp : spMap ψ.toRingHom ≫ pt C y = p
  bm : BM ψ t' P z

variable {p : Sp T ⟶ C.Y.X} {z : FrPt Xo c T}

theorem Wit.ov (w : Wit C p z) : GlobalTheory.AllWt.ptF z ≫ Z.jQ = p ≫ C.π := by
  rw [ptF_map w.bm.x_eq, Category.assoc, w.chart.ov, ← Category.assoc, w.hp]

theorem Wit.transfer [IsLocalRing T] (w : Wit C p z) {y : C.Y.X} {P : FrPt Xo c (St C y)} {t : Ix Dw → (Fk C)ˣ}
    (h : Chart C y P t) {ψ : St C y →ₐ[c.F] T} (hp : spMap ψ.toRingHom ≫ pt C y = p) :
    ∃ t', BM ψ t' P z ∧ ∀ (ex : Ix Dw → ℤ) a₁ a₂, toFk C w.y a₁ * chi ex w.t = toFk C y a₂ * chi ex t →
      chi ex w.t' * w.ψ a₁ = chi ex t' * ψ a₂ := by
  obtain ⟨y', χ, hχ, hy'⟩ := exists_factor p (by rw [← Category.assoc]; exact str_of_over w.ov)
  obtain ⟨s₁, P₁, a1, a2, a3, a4⟩ := w.chart.move (hy' ▸ specializes_of w.hp (IsLocalRing.closedPoint T) : y' ⤳ w.y)
  obtain ⟨s₂, P₂, b1, b2, b3, b4⟩ := h.move (hy' ▸ specializes_of hp (IsLocalRing.closedPoint T) : y' ⤳ y)
  have e1 : ∀ a, χ (s₁ a) = w.ψ a := fun a => DFunLike.congr_fun
    (hom_eq (ψ := χ.toRingHom.comp s₁.toRingHom) (by rw [← sp_comp, Category.assoc, a3, hχ, w.hp])) a
  have e2 : ∀ a, χ (s₂ a) = ψ a := fun a => DFunLike.congr_fun
    (hom_eq (ψ := χ.toRingHom.comp s₂.toRingHom) (by rw [← sp_comp, Category.assoc, b3, hχ, hp])) a
  obtain ⟨v, hv, ht⟩ := BM.descend (toFk_injective C _) (x_eq_of_over (a2.ov.trans b2.ov.symm)) b2.bm a2.bm
  have k1 : BM χ (w.t' * umap χ v) P₂ z := (BM.of_frBor hv).comp (BM.cancel a1 w.bm e1) fun _ => rfl
  have k2 := (BM.of_frMap b1).comp k1 e2
  have e3 : umap χ (1 : Ix Dw → (St C _)ˣ) = 1 := funext fun i => map_one _
  rw [e3, mul_one] at k2
  refine ⟨_, k2, fun ex a₁ a₂ ha => ?_⟩
  rw [ht, chi_mul, Units.val_mul, chi_umap, ← a4, ← b4] at ha
  have ha' : s₁ a₁ = s₂ a₂ * (chi ex v : (St C _)ˣ) := toFk_injective C _ (by
    rw [map_mul]
    refine (chi ex w.t).isUnit.mul_right_cancel ?_
    rw [ha]; ring)
  rw [chi_mul, Units.val_mul, chi_umap, ← e1, ← e2, ha', map_mul]
  ring

theorem carries_iff {k : Type} [Field k] {p : Sp k ⟶ C.Y.X} {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {g : EigFrame Z φ x} :
    C.Carries p g ↔ ∃ (y : C.Y.X) (ψ : St C y →+* k) (φ₁ : c.F →+* St C y)
    (f : EigFrame Z φ₁ (pt C y ≫ C.π ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fk C)ˣ)
    (t' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ), p = spMap ψ ≫ pt C y ∧
      f.Tri (toFk C y).toRingHom (rationalEigenFrame C) t ∧ f.Tri ψ g t' := Iff.rfl

theorem Wit.carries {k : Type} [Field k] [Algebra c.F k] {p : Sp k ⟶ C.Y.X} {z : FrPt Xo c k} (w : Wit C p z)
    {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {g : EigFrame Z φ x} (hg : Comparison₂ z g) : C.Carries p g := by
  obtain ⟨f, hf⟩ := exists_tie_frame w.P w.chart.over_j
  exact carries_iff.2 ⟨w.y, w.ψ.toRingHom, _, f, _, _, w.hp.symm, hf.tri_of_bm tie0 w.chart.bm, hf.tri_of_bm hg w.bm⟩

theorem lower_of_mul {k : Type} [Field k] {n : ℕ} {A M : Matrix (Fin n) (Fin n) k} (hA : ∀ i j, i < j → A i j = 0)
    (hd : ∀ i, A i i ≠ 0) (h : ∀ i j, i < j → (A * M) i j = 0) : ∀ i j, i < j → M i j = 0 := by
  intro i
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    intro j hij
    have := h i j hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun m _ hm => ?_) (by simp)] at this
    · exact (mul_eq_zero.1 this).resolve_left (hd i)
    · rcases lt_or_gt_of_ne hm with h1 | h1
      · rw [ih m h1 j (h1.trans hij), mul_zero]
      · rw [hA i m h1, zero_mul]

theorem lower_mul {k : Type} [CommRing k] {n : ℕ} {A M : Matrix (Fin n) (Fin n) k} (hA : ∀ i j, i < j → A i j = 0)
    (hM : ∀ i j, i < j → M i j = 0) (i j : Fin n) (hij : i < j) : (A * M) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  rcases le_or_gt m i with h | h
  · rw [hM m j (h.trans_lt hij), mul_zero]
  · rw [hA i m h, zero_mul]

theorem dual_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (dualMap g) ≫ spMap (dualMap f) = spMap (dualMap (g.comp f)) := by
  rw [sp_comp]
  congr 1
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap]

theorem dual_eps {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    spMap (dualMap f) ≫ spMap (epsMul a) = spMap (epsMul (f a)) ≫ spMap (dualMap f) := by
  rw [sp_comp, sp_comp]
  congr 1
  refine RingHom.ext fun z => ?_
  ext <;> simp [dualMap, epsMul, mul_comm]

theorem wit_of_carries {k : Type} [Field k] [Algebra c.F k] {p : Sp k ⟶ C.Y.X} {z : FrPt Xo c k}
    (hp : GlobalTheory.AllWt.ptF z ≫ Z.jQ = p ≫ C.π) {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {g : EigFrame Z φ x} (hg : Comparison₂ z g)
    (h : C.Carries p g) : Nonempty (Wit C p z) := by
  obtain ⟨y, ψ, φ₁, f, t, t', e0, h1, h2⟩ := carries_iff.1 h
  obtain rfl : φ₁ = algebraMap c.F (St C y) := RingHom.ext fun a => toFk_injective C y
    ((DFunLike.congr_fun h1.2.1 a).symm.trans ((toFk C y).commutes a).symm)
  obtain ⟨y', χ, hχ, hy'⟩ := exists_factor p (by rw [← Category.assoc]; exact str_of_over hp)
  obtain ⟨sp, s1, s2⟩ := exists_spec (hy' ▸ specializes_of e0.symm (IsLocalRing.closedPoint k) : y' ⤳ y)
  obtain ⟨P, u, hC, -⟩ := exists_chart (C := C) (y := y') fun hb =>
    hb ⟨GlobalTheory.AllWt.ptF z (IsLocalRing.closedPoint k),
      (congrArg (fun g => g (IsLocalRing.closedPoint k)) hp).trans (congrArg C.π hy')⟩
  obtain ⟨f', hf'⟩ := exists_tie_frame P hC.over_j
  have e1 : χ.toRingHom.comp sp.toRingHom = ψ := hom_eq (by rw [← sp_comp, Category.assoc, s1, hχ, e0])
  have e2 : (toFk C y').toRingHom.comp sp.toRingHom = (toFk C y).toRingHom := RingHom.ext s2
  have hM : ∀ τ i, ∃ a, IsCombAtG Z.t (pt C y' ≫ C.π ≫ genι Z) (f'.v τ) a
      (spMap (dualMap sp.toRingHom) ≫ f.v τ i) := fun τ i => by
    refine (f'.basis τ _ ?_ fun a => ?_).exists
    · have := GlobalTheory.FactorDepth.isTanAtG_map Z.t sp.toRingHom (f.tan τ i)
      rwa [← Category.assoc, s1] at this
    · have e3 : sp.toRingHom (algebraMap c.F (St C y) (embK c τ a)) = algebraMap c.F (St C y') (embK c τ a) :=
        sp.commutes _
      rw [Category.assoc, f.eig, ← Category.assoc, dual_eps, Category.assoc, e3]
  choose M hM using hM
  choose A A1 A2 A3 using h1.2.2
  choose B B1 B2 B3 using h2.2.2
  obtain ⟨P', p1, p2⟩ := hC.bm
  have low : ∀ τ i j, i < j → M τ i j = 0 := fun τ i j hij => by
    have key := lower_of_mul (A := A τ) (M := Matrix.map (M τ) (toFk C y')) (A2 τ)
      (fun i => by rw [A1]; exact Units.ne_zero _) (fun i j hij => ?_) i j hij
    · exact toFk_injective C _ (key.trans (map_zero _).symm)
    · obtain ⟨cf, -, c2, c3⟩ := p2.2.1 τ i
      have c4 := hf'.comb tie0 p1 p2.1 τ (M := M τ) (N := A τ) (hM τ) (fun i => by
        simp only [← Category.assoc, dual_comp, e2]
        exact A3 τ i) i
      rw [(P'.basis τ _ (p2.1 ▸ (fr0 C).tan τ i) ((fr0 C).eig τ i)).unique c4 c3]
      exact c2 j hij
  obtain ⟨Q, hQ⟩ := exists_frMap χ P
  have hx : z.x = Q.x := x_eq_of_over (by
    rw [hp, ptF_map hQ.1, Category.assoc, hC.ov, ← Category.assoc, hχ])
  obtain ⟨v, hv, -⟩ := exists_frBor hx (fun τ => Matrix.of (B τ) * Matrix.map (M τ) χ)
    (fun τ => lower_mul (B2 τ) fun i j hij => (congrArg χ (low τ i j hij)).trans (map_zero _))
    fun τ i => hf'.comb hg hQ hx τ (M := M τ) (N := B τ) (hM τ) (fun i => by
      simp only [← Category.assoc, dual_comp, e1]
      exact B3 τ i) i
  exact ⟨⟨_, χ, P, u, v, hC, hχ, Q, hQ, hv⟩⟩

theorem Wit.extend {V K : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    [Algebra c.F V] [Algebra c.F K] [IsScalarTower c.F V K] {p : Sp K ⟶ C.Y.X} {z : FrPt Xo c V} {zK : FrPt Xo c K}
    (w : Wit C p zK) (hz : FrMap (IsScalarTower.toAlgHom c.F V K) z zK) : ∃ q, Nonempty (Wit C q z) := by
  have : IsProper Z.s := by
    obtain ⟨N, i, _, hi⟩ := Z.proj
    have := isProper_str O N
    rw [← hi]; infer_instance
  have : IsIso (spMap e.toRingHom) := by
    have : IsIso (CommRingCat.ofHom e.toRingHom) := e.toCommRingCatIso.isIso_hom
    infer_instance
  have : IsProper (C.π ≫ genStr Z ≫ spMap e.toRingHom) := by rw [C.π_str]; infer_instance
  have : IsProper C.π := IsProper.of_comp C.π (genStr Z ≫ spMap e.toRingHom)
  have hv : ValuativeCriterion.Existence C.π := by
    have h : UniversallyClosed C.π := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have sq : p ≫ C.π = spMap (algebraMap V K) ≫ GlobalTheory.AllWt.ptF z ≫ Z.jQ := by
    rw [← w.ov, ptF_map hz.1, Category.assoc]; rfl
  obtain ⟨⟨q, q1, q2⟩⟩ := (hv ⟨V, K, p, GlobalTheory.AllWt.ptF z ≫ Z.jQ, ⟨sq⟩⟩).exists_lift
  change Sp V ⟶ C.Y.X at q
  change spMap (algebraMap V K) ≫ q = p at q1
  change q ≫ C.π = GlobalTheory.AllWt.ptF z ≫ Z.jQ at q2
  obtain ⟨y', χ, hχ, hy'⟩ := exists_factor q (by rw [← Category.assoc]; exact str_of_over q2.symm)
  obtain ⟨P, u, hC, -⟩ := exists_chart (C := C) (y := y') fun hb =>
    hb ⟨GlobalTheory.AllWt.ptF z (IsLocalRing.closedPoint V),
      (congrArg (fun g => g (IsLocalRing.closedPoint V)) q2.symm).trans (congrArg C.π hy')⟩
  obtain ⟨t', ht', -⟩ := w.transfer hC (ψ := (IsScalarTower.toAlgHom c.F V K).comp χ) (by
    rw [← q1, ← hχ, ← Category.assoc, sp_comp]; rfl)
  obtain ⟨Q, hQ⟩ := exists_frMap χ P
  have hx : z.x = Q.x := x_eq_of_over (by
    rw [← q2, ptF_map hQ.1, Category.assoc, hC.ov, ← Category.assoc, hχ])
  obtain ⟨v, hv, -⟩ := BM.descend (IsFractionRing.injective V K) hx (BM.cancel hQ ht' fun _ => rfl) (BM.of_frMap hz)
  exact ⟨q, ⟨⟨_, χ, P, u, v, hC, hχ, Q, hQ, hv⟩⟩⟩

end Wit

section Global

variable {σ : c.F →+* ℂ} {N : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ N} (Φ : FlagTor Z e U) (ex : Ix Dw → ℤ)
  (s : ∀ k, Fk (Φ.C k)) {T T' : Type} [CommRing T] [Algebra c.F T] [CommRing T'] [Algebra c.F T']

def Val (z : FrPt Xo c T) (v : T) : Prop :=
  ∃ (i : U.Comp) (p : Sp T ⟶ (Φ.C i).Y.X) (w : Wit (Φ.C i) p z) (a : St (Φ.C i) w.y),
    toFk _ w.y a * chi ex w.t = s i ∧ v = chi ex w.t' * w.ψ a

def Rep (P : FrPt Xo c T) (r : T) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (φ : T →ₐ[c.F] k) (z : FrPt Xo c k), FrMap φ P z →
    Val Φ ex s z (φ r)

variable {Φ ex s}

theorem Val.comp {z : FrPt Xo c T} {v : T} (h : Val Φ ex s z v) {χ : T →ₐ[c.F] T'} {u : Ix Dw → T'ˣ}
    {z' : FrPt Xo c T'} (hz : BM χ u z z') : Val Φ ex s z' (chi ex u * χ v) := by
  obtain ⟨i, p, w, a, h1, rfl⟩ := h
  refine ⟨i, _, ⟨w.y, χ.comp w.ψ, w.P, w.t, _, w.chart, rfl, w.bm.comp hz fun _ => rfl⟩, a, h1, ?_⟩
  show _ = (chi ex (u * umap χ w.t') : T') * χ (w.ψ a)
  rw [chi_mul, Units.val_mul, chi_umap, map_mul, mul_assoc]

theorem Val.map {z : FrPt Xo c T} {v : T} (h : Val Φ ex s z v) {χ : T →ₐ[c.F] T'}
    {z' : FrPt Xo c T'} (hz : FrMap χ z z') : Val Φ ex s z' (χ v) := by
  simpa [chi_one] using h.comp (BM.of_frMap hz)

theorem lift_frame {k : Type} [Field k] [Algebra c.F k] (z : FrPt Xo c k) :
    ∃ g : EigFrame Z (algebraMap c.F k) ((GlobalTheory.AllWt.ptF z ≫ Z.jQ) ≫ genι Z), Comparison₂ z g :=
  exists_tie_frame z (by rw [Model.j, Category.assoc])

theorem Val.unique {k : Type} [Field k] [IsAlgClosed k] [Algebra c.F k] {z : FrPt Xo c k} {v v' : k}
    (h : Val Φ ex s z v) (h' : Val Φ ex s z v') : v = v' := by
  obtain ⟨i, p, w, a, h1, rfl⟩ := h
  obtain ⟨i', p', w', a', h1', rfl⟩ := h'
  obtain ⟨g, hg⟩ := lift_frame (Z := Z) z
  have e0 : (⟨i, p⟩ : Σ i : U.Comp, (Sp k ⟶ (Φ.C i).Y.X)) = ⟨i', p'⟩ :=
    (Φ.lifts k _ _ (str_of_over rfl) g).unique ⟨w.ov.symm, w.carries hg⟩ ⟨w'.ov.symm, w'.carries hg⟩
  cases e0
  obtain ⟨t', k1, k2⟩ := w.transfer w'.chart w'.hp
  rw [k2 ex a a' (h1.trans h1'.symm), k1.unique w'.bm]

theorem exists_wit {k : Type} [Field k] [IsAlgClosed k] [Algebra c.F k] (z : FrPt Xo c k) :
    ∃ i p, Nonempty (Wit (Φ.C i) p z) := by
  obtain ⟨g, hg⟩ := lift_frame (Z := Z) z
  obtain ⟨⟨i, p⟩, ⟨h1, h2⟩, -⟩ := Φ.lifts k _ _ (str_of_over rfl) g
  exact ⟨i, p, wit_of_carries h1.symm hg h2⟩

theorem Rep.map {P : FrPt Xo c T} {r : T} (h : Rep Φ ex s P r) {χ : T →ₐ[c.F] T'} {Q : FrPt Xo c T'}
    (hQ : FrMap χ P Q) : Rep Φ ex s Q (χ r) := fun k _ _ _ φ z hz =>
  h k (φ.comp χ) z (frMap_comp hQ hz fun _ => rfl)

theorem Rep.unique [IsReduced T] {P : FrPt Xo c T} {r r' : T} (h : Rep Φ ex s P r) (h' : Rep Φ ex s P r') : r = r' := by
  refine sub_eq_zero.1 (GeometricValues.eq_zero_of_forall_algClosed (K := c.F) _ fun k _ _ _ φ => ?_)
  obtain ⟨z, hz⟩ := exists_frMap φ P
  rw [map_sub, (h k φ z hz).unique (h' k φ z hz), sub_self]

theorem Val.rep {P : FrPt Xo c T} {r : T} (h : Val Φ ex s P r) : Rep Φ ex s P r := fun _ _ _ _ _ _ hz => h.map hz

theorem Rep.bor {P Q : FrPt Xo c T} {r : T} (h : Rep Φ ex s P r) {t : Ix Dw → Tˣ} (hb : FrBor t P Q) :
    Rep Φ ex s Q (chi ex t * r) := fun k _ _ _ φ z hz => by
  obtain ⟨P', hP⟩ := exists_frMap φ P
  have := (h k φ P' hP).comp (BM.of_frBor (frBor_map hb hP hz))
  rwa [chi_umap, AlgHom.id_apply, ← map_mul] at this

variable (hex : ex none = 0)
  (hs : ∀ k (y : (Φ.C k).Y.X), (Φ.C k).π y ∉ genBd Z → ((Φ.C k).LEx ex).RegularAt y (s k))

include hex hs

theorem Wit.exists_val {i : U.Comp} {p : Sp T ⟶ (Φ.C i).Y.X} {z : FrPt Xo c T} (w : Wit (Φ.C i) p z) :
    ∃ v, Val Φ ex s z v := by
  obtain ⟨a, ha⟩ := w.chart.exists_coeff hex (hs i _ w.chart.notMem)
  exact ⟨_, i, p, w, a, ha, rfl⟩

theorem exists_values (P : FrPt Xo c T) :
    ∃ W : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k], (T →ₐ[c.F] k) → k,
      ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (φ : T →ₐ[c.F] k) (z : FrPt Xo c k), FrMap φ P z →
        Val Φ ex s z (W k φ) := by
  have : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (φ : T →ₐ[c.F] k), ∃ v : k, ∀ z : FrPt Xo c k,
      FrMap φ P z → Val Φ ex s z v := fun k _ _ _ φ => by
    obtain ⟨z, hz⟩ := exists_frMap φ P
    obtain ⟨i, p, ⟨w⟩⟩ := exists_wit (Φ := Φ) z
    obtain ⟨v, hv⟩ := w.exists_val hex hs
    exact ⟨v, fun z' hz' => frMap_unique hz hz' ▸ hv⟩
  exact ⟨fun k _ _ _ φ => (this k φ).choose, fun k _ _ _ φ => (this k φ).choose_spec⟩

theorem exists_rep_valuationRing {V : Type} [CommRing V] [IsDomain V] [ValuationRing V] [Algebra c.F V]
    (hV : IsAlgClosed (FractionRing V)) (P : FrPt Xo c V) : ∃ r, Rep Φ ex s P r := by
  obtain ⟨z, hz⟩ := exists_frMap (IsScalarTower.toAlgHom c.F V (FractionRing V)) P
  obtain ⟨i, p, ⟨w⟩⟩ := exists_wit (Φ := Φ) z
  obtain ⟨q, ⟨w'⟩⟩ := w.extend hz
  obtain ⟨v, hv⟩ := w'.exists_val hex hs
  exact ⟨v, hv.rep⟩

theorem exists_rep_normal [IsDomain T] [IsIntegrallyClosed T] (P : FrPt Xo c T) : ∃ r, Rep Φ ex s P r := by
  obtain ⟨W, hW⟩ := exists_values hex hs P
  obtain ⟨r, hr⟩ := GlobalTheory.PointFunction.exists_eq_eval c.F T W (fun k k' _ _ _ _ _ _ φ χ => by
    obtain ⟨z, hz⟩ := exists_frMap φ P
    obtain ⟨z', hz'⟩ := exists_frMap χ z
    exact (hW k' _ z' (frMap_comp hz hz' fun _ => rfl)).unique ((hW k φ z hz).map hz')) (fun V _ _ _ _ hV ι => by
    obtain ⟨Q, hQ⟩ := exists_frMap ι P
    obtain ⟨v, hv⟩ := exists_rep_valuationRing hex hs hV Q
    refine ⟨v, fun k _ _ _ φ => ?_⟩
    obtain ⟨z, hz⟩ := exists_frMap φ Q
    exact (hW k _ z (frMap_comp hQ hz fun _ => rfl)).unique (hv k φ z hz))
  exact ⟨r, fun k _ _ _ φ z hz => hr k φ ▸ hW k φ z hz⟩

theorem exists_rep_local [IsLocalRing T] (P : FrPt Xo c T) : ∃ r, Rep Φ ex s P r := by
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have hn := (GlobalTheory.isNormalScheme_iff _).1 (GlobalTheory.isNormalScheme_of_smooth (S := Spec (.of c.F))
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)))
  obtain ⟨B, _, _, _, _, j, ψ, hj⟩ : ∃ (B : Type) (_ : CommRing B) (_ : IsLocalRing B) (_ : IsDomain B)
      (_ : IsIntegrallyClosed B) (j : Sp B ⟶ Xo.XF c) (ψ : B →+* T), spMap ψ ≫ j = GlobalTheory.AllWt.ptF P :=
    ⟨(Xo.XF c).presheaf.stalk (GlobalTheory.AllWt.ptF P (IsLocalRing.closedPoint T)), inferInstance, inferInstance, (hn _).1,
      (hn _).2, (Xo.XF c).fromSpecStalk _, (Scheme.stalkClosedPointTo (GlobalTheory.AllWt.ptF P)).hom,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk _⟩
  letI : Algebra c.F B := (Spec.preimage (j ≫ pullback.snd _ _)).hom.toAlgebra
  have hB : j ≫ pullback.snd _ _ = spMap (algebraMap c.F B) := (Spec.map_preimage _).symm
  let ψ' : B →ₐ[c.F] T := { ψ with commutes' := fun a => DFunLike.congr_fun (sp_inj (f := ψ.comp (algebraMap c.F B)) (by
      rw [← sp_comp, ← hB, ← Category.assoc, hj, ptF_snd])) a }
  obtain ⟨y₀, hy₀⟩ := exists_frPt (c := c) (j ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hB, sp_comp]; rfl)
  obtain ⟨A, _, _, _, π, X, u, _, hA⟩ := GlobalTheory.exists_frameRing_integrallyClosed c.F (E →+* ℂ) (fun τ => Dw.mult τ) B
  obtain ⟨u₀, hu₀⟩ := exists_frMap π y₀
  obtain ⟨Q, hQ, -⟩ := existsUnique_frChg E H Dw l Xo c A u₀ X u hA.1
  obtain ⟨a, ⟨-, ha⟩, -⟩ := univFrame_classifies GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c B A y₀ π X u Q
    ⟨hA, u₀, hu₀, hQ⟩ T P ψ' (by rw [hy₀, ← ptF_fst, ← hj, Category.assoc])
  obtain ⟨r, hr⟩ := exists_rep_normal hex hs Q
  exact ⟨_, hr.map ha⟩

theorem exists_rep [IsNoetherianRing T] (P : FrPt Xo c T) : ∃ r, Rep Φ ex s P r := by
  obtain ⟨W, hW⟩ := exists_values hex hs P
  obtain ⟨r, hr⟩ := GlobalTheory.exists_eq_of_locally_fraction_on_generisations c.F T W fun q _ => by
    obtain ⟨Q, hQ⟩ := exists_frMap (IsScalarTower.toAlgHom c.F T (Localization.AtPrime q)) P
    obtain ⟨v, hv⟩ := exists_rep_local hex hs Q
    refine ⟨v, fun k _ _ _ φ => ?_⟩
    obtain ⟨z, hz⟩ := exists_frMap φ Q
    exact (hW k _ z (frMap_comp hQ hz fun _ => rfl)).unique (hv k φ z hz)
  exact ⟨r, fun k _ _ _ φ z hz => hr k φ ▸ hW k φ z hz⟩

theorem val_frame_zero (i : U.Comp) : Val Φ ex s (fr0 (Φ.C i)) (s i) := by
  obtain ⟨y, χ, hχ, hy⟩ := exists_factor (gpt (Φ.C i)) (by rw [← Category.assoc]; exact str_of_over (frame_point_over _))
  obtain ⟨P, t, hC, -⟩ := exists_chart (C := Φ.C i) (y := y) fun hb =>
    hb ⟨GlobalTheory.AllWt.ptF (fr0 (Φ.C i)) (IsLocalRing.closedPoint (Fk (Φ.C i))),
      (congrArg (fun g => g (IsLocalRing.closedPoint (Fk (Φ.C i)))) (frame_point_over _)).trans (congrArg (Φ.C i).π hy)⟩
  obtain ⟨a, ha⟩ := hC.exists_coeff hex (hs i _ hC.notMem)
  exact ⟨i, _, ⟨y, toFk _ y, P, t, t, hC, rfl, hC.bm⟩, a, ha, ha.symm.trans (mul_comm _ _)⟩

omit hex hs in
theorem rep_of_mem {f : Rul Xo c} (hf : f ∈ secZ Xo c ex) (hv : ∀ i, evR Xo c f (fr0 (Φ.C i)) = s i) (p : TRing c.F)
    (P : FrPt Xo c p.R) : Rep Φ ex s P (f p P) := fun k _ _ _ φ z hz => by
  obtain ⟨i, q, ⟨w⟩⟩ := exists_wit (Φ := Φ) z
  refine ⟨i, q, w, evR Xo c f w.P, ?_, ?_⟩
  · rw [← hv, w.chart.bm.evR hf, mul_comm]
  · rw [← w.bm.evR hf, evR_eq hf.1 hz]

theorem existsUnique_rule : ∃! f : Rul Xo c, f ∈ secZ Xo c ex ∧ ∀ i, evR Xo c f (fr0 (Φ.C i)) = s i := by
  have red : ∀ p : TRing c.F, IsReduced p.R := fun p => (Ideal.isRadical_iff_quotient_reduced p.I).mp p.rad
  choose f hf using fun (p : TRing c.F) (P : FrPt Xo c p.R) => exists_rep hex hs P
  have hm : f ∈ secZ Xo c ex := ⟨fun p q φ y z h => (hf q z).unique ((hf p y).map h),
    fun p t y y' h => (hf p y').unique ((hf p y).bor h)⟩
  refine ⟨f, ⟨hm, fun i => ?_⟩, fun g hg => ?_⟩
  · obtain ⟨p, φ, y, hy⟩ := fromTest_of_isLocalRing (fr0 (Φ.C i))
    rw [evR_eq hm.1 hy]
    exact ((hf p y).map hy).unique (val_frame_zero hex hs i).rep
  · funext p P
    exact (rep_of_mem hg.1 hg.2 p P).unique (hf p P)

end Global

end Descent

theorem existsUnique_rule_of_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (N : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ N) (Φ : FlagTor Z e U) (ex : Ix Dw → ℤ), ex none = 0 → ∀ s : ∀ k, (Φ.C k).Y.Fn, (∀ k (y : (Φ.C k).Y.X), (Φ.C k).π y ∉ genBd Z → ((Φ.C k).LEx ex).RegularAt y (s k)) → ∃! f : Rul Xo c, f ∈ GlobalTheory.AllWt.secZ Xo c ex ∧ ∀ k, (Φ.C k).val f = s k := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e σ N U Φ ex hex s hs
  exact Descent.existsUnique_rule (s := s) hex hs

end GlobalTheory.ShFam
