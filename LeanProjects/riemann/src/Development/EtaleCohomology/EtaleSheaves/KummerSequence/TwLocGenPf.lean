import Development.EtaleCohomology.EtaleSheaves.KummerSequence.TwLocGenPfSec

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.H2CurveOrder.TwLocGenPf
open LateralTheory.E.H2CurveOrder.TwLocGenPfSec

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (h ≫ g) y = Sec.res h (Sec.res g y) := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem TwLocGen_of : LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.TwLocGen := by
  intro q _ U y
  have hT := TwSecLoc_of_alg AlgPow_of
  refine loc_bind (loc_surj (twF q 1) U y) ?_
  rintro V g ⟨x, hx⟩
  by_cases hP : Nonempty (Prim q Γ(V, ⊤))
  · obtain ⟨ζ⟩ := hP
    refine loc_mono (hT q 1 V ζ (Sec.res g y)) ?_
    rintro W h ⟨c, hc⟩
    right
    exact ⟨ζ.map h.appTop.hom, c, by rw [res_comp]; exact hc⟩
  · have hx0 : x = 0 := by
      haveI : IsEmpty (Prim q Γ(V, ⊤)) := not_nonempty_iff.mp hP
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have : z = 0 := Subsingleton.elim _ _
      rw [this]; rfl
    refine loc_mono (loc_true V) ?_
    intro W h _
    left
    have hx' : Sec.res (F := tw q 1) g y = ofRings.sec (twF q 1) V x := hx
    rw [res_comp, hx', hx0]
    have h0 : ofRings.sec (twF q 1) V 0 = 0 :=
      map_zero ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 1)).app (op V)).hom
    rw [h0]
    exact map_zero _

end LateralTheory.E.H2CurveOrder.TwLocGenPf
