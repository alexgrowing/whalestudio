import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniformisationOfComplexConjugateKeyDatum
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm
open GlobalTheory.ArchMetricCompare GlobalTheory.ConjUnif

namespace GlobalTheory.ConjTransport

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {s s₁ : Sp ℂ ⟶ Sp B} {o : Obj D l b s} {o₁ : Obj D l b s₁}

theorem cjPt_act (m : ObjMap o₁ o cj) (x : 𝟙_ (Over (Sp ℂ)) ⟶ o.t.G) (a : 𝓞 E) :
    cjPt m.cart (x ≫ o.t.act.act a) = cjPt m.cart x ≫ o₁.t.act.act a := by
  refine pt_ext m.cart ((cjPt_comp _ _).trans ?_)
  rw [Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc (cjPt m.cart x).left, cjPt_comp]
  exact (Category.assoc _ _ _).symm

theorem cjPt_eta (m : ObjMap o₁ o cj) (a : D.La) : cjPt m.cart (o.eta a) = o₁.eta a :=
  pt_ext m.cart ((cjPt_comp _ _).trans (m.eta a).symm)

theorem cjPt_etaA (m : ObjMap o₁ o cj) (a : D.La) : cjPt m.cart (o.etaA a) = o₁.etaA a :=
  pt_ext m.cart ((cjPt_comp _ _).trans (m.etaA a).symm)

theorem exists_unif (m : ObjMap o₁ o cj) {g : ℕ} (u : HolUnif o.t.G o.t.PP.L g) {Hm : Matrix (Fin g) (Fin g) ℂ}
    {κ : u.Λ → ℂ} (hA : u.IsAH Hm κ) :
    ∃ (u₁ : HolUnif o₁.t.G o₁.t.PP.L g) (κ₁ : u₁.Λ → ℂ), u₁.IsAH (Hm.map star) κ₁ ∧
      (∀ z, z ∈ u₁.Λ ↔ star z ∈ u.Λ) ∧ ∀ z, u₁.ex z = cjPt m.cart (u.ex (star z)) := by
  obtain ⟨w, hw, -⟩ := m.lin
  obtain ⟨w', hw', -⟩ := exists_inv w hw
  have hP := pull_isLB o.t.PP.isLB m.cm.F
  exact ⟨carry (conjPull m.cart u) hP o₁.t.PP.isLB hw', _,
    carry_isAH hP o₁.t.PP.isLB hw' (conjPull_isAH m.cart u hA), fun _ => Iff.rfl, fun _ => rfl⟩

theorem herm_map_star {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    (herm (Hm.map star) z w).im = -(herm Hm (star z) (star w)).im := by
  rw [herm, herm, ← star_form]
  rfl

def conjEquiv (g : ℕ) : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := (starL' ℝ (A := Fin g → ℂ)).toLinearEquiv

theorem conjEquiv_apply {g : ℕ} (z : Fin g → ℂ) : conjEquiv g z = star z := rfl

theorem isTransport_conj {s' s₁' : Sp ℂ ⟶ Sp B} {o' : Obj D l b s'} {o₁' : Obj D l b s₁'}
    (m : ObjMap o₁ o cj) (m' : ObjMap o₁' o' cj) {g g' : ℕ}
    {u : HolUnif o.t.G o.t.PP.L g} {u' : HolUnif o'.t.G o'.t.PP.L g'}
    {u₁ : HolUnif o₁.t.G o₁.t.PP.L g} {u₁' : HolUnif o₁'.t.G o₁'.t.PP.L g'}
    {Hm : Matrix (Fin g) (Fin g) ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ}
    (hΛ : ∀ z, z ∈ u₁.Λ ↔ star z ∈ u.Λ) (hx : ∀ z, u₁.ex z = cjPt m.cart (u.ex (star z)))
    (hΛ' : ∀ z, z ∈ u₁'.Λ ↔ star z ∈ u'.Λ) (hx' : ∀ z, u₁'.ex z = cjPt m'.cart (u'.ex (star z)))
    {φ : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g' → ℂ)} (h : IsTransport o₁ o₁' u₁ u₁' (Hm.map star) (Hm'.map star) φ) :
    IsTransport o o' u u' Hm Hm' ((conjEquiv g).trans (φ.trans (conjEquiv g'))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : ∀ z, ((conjEquiv g).trans (φ.trans (conjEquiv g'))) z = star (φ (star z)) := fun _ => rfl
  refine ⟨fun z => ?_, fun a z w hw => ?_, fun z w => ?_, fun a z hz => ?_, fun a z hz => ?_⟩
  · rw [e, ← hΛ', h1, hΛ, star_star]
  · refine cjPt_injective m'.cart ?_
    rw [e, e, cjPt_act, ← hx', ← hx']
    refine h2 a _ _ ?_
    rw [hx, hx, star_star, star_star, hw, cjPt_act]
  · have := h3 (star z) (star w)
    rw [herm_map_star, herm_map_star, star_star, star_star] at this
    rw [e, e]
    exact neg_injective this
  · refine cjPt_injective m'.cart ?_
    rw [e, ← hx', cjPt_eta]
    refine h4 a _ ?_
    rw [hx, star_star, hz, cjPt_eta]
  · refine cjPt_injective m'.cart ?_
    rw [e, ← hx', cjPt_etaA]
    refine h5 a _ ?_
    rw [hx, star_star, hz, cjPt_etaA]

theorem exists_conj_obj (Xo : Moduli D l) (c : Coeff l) (y : Sp ℂ ⟶ Xo.XF c)
    (o : Obj D l (baseKA l) (y ≫ toX Xo c ≫ Xo.s)) (n : ObjMap o Xo.univ (y ≫ toX Xo c)) :
    ∃ o₁ : Obj D l (baseKA l) ((cj ≫ y) ≫ toX Xo c ≫ Xo.s),
      Nonempty (ObjMap o₁ o cj) ∧ Nonempty (ObjMap o₁ Xo.univ ((cj ≫ y) ≫ toX Xo c)) := by
  obtain ⟨o₁, ⟨m⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _
    ((cj ≫ y) ≫ toX Xo c ≫ Xo.s) cj rfl rfl
    (by rw [DetExtendZero.spMap_id, Category.comp_id, Category.assoc]) o
  obtain ⟨k, -⟩ := ObjComp.objMap_comp n m
  exact ⟨o₁, ⟨m⟩, by rw [Category.assoc cj y (toX Xo c)]; exact ⟨k⟩⟩

end GlobalTheory.ConjTransport

namespace GlobalTheory

open ConjTransport

theorem hasTransport_of_conj (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (e : c.F →+* ℂ)
    (h : HasTransport Xo c U ((starRingEnd ℂ).comp e)) : HasTransport Xo c U e := by
  rintro y y' hy hy' hU hU' o o' ⟨n⟩ ⟨n'⟩ g g' u u' Hm Hm' κ κ' hA hA'
  obtain ⟨o₁, ⟨m⟩, k⟩ := exists_conj_obj Xo c y o n
  obtain ⟨o₁', ⟨m'⟩, k'⟩ := exists_conj_obj Xo c y' o' n'
  obtain ⟨u₁, κ₁, hA₁, hΛ, hx⟩ := exists_unif m u hA
  obtain ⟨u₁', κ₁', hA₁', hΛ', hx'⟩ := exists_unif m' u' hA'
  have a : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ toF Xo c = spMap e →
      (cj ≫ y) ≫ toF Xo c = spMap ((starRingEnd ℂ).comp e) := fun y hy => by
    rw [Category.assoc, hy, DetExtendZero.spMap_comp]
  have r : ∀ y : Sp ℂ ⟶ Xo.XF c, Set.range y ⊆ U → Set.range (cj ≫ y) ⊆ U := by
    rintro y hy _ ⟨z, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hy ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ := h (cj ≫ y) (cj ≫ y') (a y hy) (a y' hy') (r y hU) (r y' hU') o₁ o₁' k k' g g' u₁ u₁' _ _ κ₁ κ₁'
    hA₁ hA₁'
  exact ⟨_, isTransport_conj m m' hΛ hx hΛ' hx' hφ⟩

end GlobalTheory
