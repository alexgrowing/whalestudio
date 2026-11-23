import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SquareUnits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetApproximation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace ReciprocityTheory.ChartRestriction.G.H1.LocalResidues

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {k : Type} [Field k] {X W Z : Scheme.{0}}

def kappa (p : X ⟶ Spec (CommRingCat.of k)) (y : X) : k →+* X.presheaf.stalk y :=
  (X.presheaf.germ (p ⁻¹ᵁ ⊤) y trivial).hom.comp
    ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)

theorem exists_frac (h0 : X ⟶ W) [IsIso h0] (D : W.Opens) (hD : IsAffineOpen D) (y : X) (hy : h0 y ∈ D)
    (f : X.presheaf.stalk y) :
    ∃ g g' : Γ(W, D), IsUnit (gs h0 y D g') ∧ f * gs h0 y D g' = gs h0 y D g := by
  have hiso : IsIso (h0.stalkMap y) := ((isIso_iff_isIso_stalkMap h0).1 inferInstance).2 y
  obtain ⟨f0, rfl⟩ := (ConcreteCategory.bijective_of_isIso (h0.stalkMap y)).2 f
  let _ : Algebra Γ(W, D) (W.presheaf.stalk (h0 y)) := TopCat.Presheaf.algebra_section_stalk W.presheaf ⟨h0 y, hy⟩
  have := hD.isLocalization_stalk ⟨h0 y, hy⟩
  obtain ⟨⟨g, g'⟩, hmk⟩ := IsLocalization.mk'_surjective (hD.primeIdealOf ⟨h0 y, hy⟩).asIdeal.primeCompl f0
  have hmk' : IsLocalization.mk' (W.presheaf.stalk (h0 y)) g g' = f0 := hmk
  have hspec := IsLocalization.mk'_spec (W.presheaf.stalk (h0 y)) g g'
  have hunit := IsLocalization.map_units (W.presheaf.stalk (h0 y)) g'
  have ge : ∀ a : Γ(W, D), gs h0 y D a = (h0.stalkMap y).hom (algebraMap Γ(W, D) (W.presheaf.stalk (h0 y)) a) :=
    fun a => (gs_stalkMap h0 y D hy a).trans (congrArg _ (gs_eq (𝟙 W) (h0 y) D hy a))
  refine ⟨g, g'.1, ?_, ?_⟩
  · rw [ge]; exact hunit.map _
  · rw [ge, ge, ← map_mul, ← hmk', hspec]

theorem gs_const {Y' : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (q : X ⟶ Y') (e : Y' ⟶ Spec (CommRingCat.of k))
    [IsIso e] (hq : q ≫ e = p) (y : X) (a : Γ(Y', ⊤)) : ∃ c : k, gs q y ⊤ a = kappa p y c := by
  subst hq
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ((inv (e.app ⊤)).hom a), ?_⟩
  have h1 : (e.app ⊤).hom ((inv (e.app ⊤)).hom a) = a := by
    exact congrArg (fun f => f.hom a) (IsIso.inv_hom_id (e.app ⊤))
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ((inv (e.app ⊤)).hom a)) = (inv (e.app ⊤)).hom a := by
    exact congrArg (fun f => f.hom ((inv (e.app ⊤)).hom a)) (Scheme.ΓSpecIso (CommRingCat.of k)).hom_inv_id
  simp only [kappa, gs, RingHom.comp_apply, h2]
  rw [dif_pos (show q y ∈ (⊤ : Y'.Opens) from trivial)]
  first
    | (show _ = (X.presheaf.germ _ y _).hom ((q.app ⊤).hom ((e.app ⊤).hom ((inv (e.app ⊤)).hom a)))
       rw [h1])
    | (simp [Scheme.Hom.comp_app, h1]; done)
    | (erw [Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply, h1]; rfl)
    | (simp only [Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply, h1]; clear * -; done)

theorem sval_rel {L : LB X} {K : Type} [Fintype K] {φ : K → (W ⟶ X)} {ε : K → ℤ}
    (s s₀ : LB.Sec (LB.LinComb L φ ε)) (D : W.Opens) (rr : Γ(W, D))
    (hrel : ∀ j, (W.presheaf.map (homOfLE (inf_le_right : D ⊓ (LB.LinComb L φ ε).U j ≤ (LB.LinComb L φ ε).U j)).op).hom
        (s.f j) =
      (W.presheaf.map (homOfLE (inf_le_left : D ⊓ (LB.LinComb L φ ε).U j ≤ D)).op).hom rr *
      (W.presheaf.map (homOfLE (inf_le_right : D ⊓ (LB.LinComb L φ ε).U j ≤ (LB.LinComb L φ ε).U j)).op).hom
        (s₀.f j))
    (r : Z ⟶ W) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (hz : r z ∈ D) :
    sval s r z J = gs r z D rr * sval s₀ r z J := by
  have hm : r z ∈ D ⊓ (LB.LinComb L φ ε).U (fun k => J (r ≫ φ k)) := ⟨hz, hJ.mem φ r⟩
  have e := congrArg (gs r z _) (hrel (fun k => J (r ≫ φ k)))
  rw [gs_res r z _ hm, gs_mul r z _ hm, gs_res r z _ hm, gs_res r z _ hm] at e
  exact e

end ReciprocityTheory.ChartRestriction.G.H1.LocalResidues
