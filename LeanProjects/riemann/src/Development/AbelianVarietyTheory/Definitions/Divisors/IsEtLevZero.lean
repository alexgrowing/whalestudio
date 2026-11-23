import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

theorem wSub_zero (D : Datum p) (w0 : Ideal (𝓞 D.F)) : wSub D w0 0 = ⊤ := by
  refine eq_top_iff.2 fun z _ => Submodule.subset_span ⟨1, by simp, z, by simp⟩

theorem isEtLev_zero {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) :
    IsEtLev o w0 0 (fun _ => 1) := by
  refine ⟨fun _ _ => (mul_one 1).symm, fun c x => ?_, fun _ _ => rfl, ?_⟩
  · haveI := o.act.hom c
    exact (MonObj.one_comp _).symm
  intro k _ _ x
  refine ⟨fun y _ => by rw [wSub_zero]; trivial, fun g hg => ⟨0, ?_⟩⟩
  have := hg 1 (by simp)
  rw [map_one, o.act.one, Category.comp_id] at this
  rw [this, MonObj.comp_one]

section act
variable {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ}
  {lv : D.La → (𝟙_ (Over S) ⟶ o.A)}

theorem IsEtLev.congr (h : IsEtLev o w0 r lv) {x y : D.La} (hxy : x - y ∈ wSub D w0 r) : lv x = lv y := by
  have : x = y + (x - y) := by abel
  rw [this, h.1, h.2.2.1 _ hxy, _root_.mul_one]

theorem IsEtLev.congr_mk (h : IsEtLev o w0 r lv) {x y : D.La}
    (hxy : Submodule.Quotient.mk (p := wSub D w0 r) x = Submodule.Quotient.mk y) : lv x = lv y :=
  h.congr ((Submodule.Quotient.eq _).1 hxy)

def liftAct (g : LevGrp D w0 r) (x : D.La) : D.La :=
  (Submodule.Quotient.mk_surjective (wSub D w0 r) (g (Submodule.Quotient.mk x))).choose

theorem mk_liftAct (g : LevGrp D w0 r) (x : D.La) :
    Submodule.Quotient.mk (p := wSub D w0 r) (liftAct g x) = g (Submodule.Quotient.mk x) :=
  (Submodule.Quotient.mk_surjective (wSub D w0 r) (g (Submodule.Quotient.mk x))).choose_spec

theorem IsEtLev.twist (h : IsEtLev o w0 r lv) (g : LevGrp D w0 r) :
    IsEtLev o w0 r (fun x => lv (liftAct g x)) := by
  refine ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ pt => ⟨fun y hy => ?_, fun q hq => ?_⟩⟩
  · rw [← h.1]; apply h.congr_mk
    simp only [mk_liftAct, Submodule.Quotient.mk_add, map_add]
  · rw [← h.2.1]; apply h.congr_mk
    simp only [mk_liftAct, Submodule.Quotient.mk_smul, map_smul]
  · have : Submodule.Quotient.mk (p := wSub D w0 r) (liftAct g x) = 0 := by
      rw [mk_liftAct, (Submodule.Quotient.mk_eq_zero _).2 hx, map_zero]
    exact h.2.2.1 _ ((Submodule.Quotient.mk_eq_zero _).1 this)
  · have h1 := ((Submodule.Quotient.mk_eq_zero _).2 ((h.2.2.2 k pt).1 _ hy))
    rw [mk_liftAct, LinearEquiv.map_eq_zero_iff] at h1
    exact (Submodule.Quotient.mk_eq_zero _).1 h1
  · obtain ⟨y, hy⟩ := (h.2.2.2 k pt).2 q hq
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective (wSub D w0 r) (g.symm (Submodule.Quotient.mk y))
    refine ⟨x, ?_⟩
    rw [← hy, h.congr_mk (by rw [mk_liftAct, hx, LinearEquiv.apply_symm_apply])]

end act

end GlobalTheory.UPel.HT.EtLev
