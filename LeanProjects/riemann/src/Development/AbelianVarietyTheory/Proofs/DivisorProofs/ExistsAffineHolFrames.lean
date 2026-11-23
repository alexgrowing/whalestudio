import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEquationComplexPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.ShFam.HolFrames

theorem exists_affine_frame {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) {T : Scheme.{0}} (io : T ⟶ gen Y) (y : T) :
    ∃ (W : T.Opens) (hW : IsAffineOpen W) (φ : c.F →+* Γ(T, W))
      (_ : EigFrame Y φ (((show Sp Γ(T, W) ⟶ T from hW.fromSpec) ≫ io) ≫ genι Y)),
      y ∈ W ∧ ((show Sp Γ(T, W) ⟶ T from hW.fromSpec) ≫ io) ≫ genStr Y = spMap φ := by
  obtain ⟨U, hU, φ, f, hy, hφ, -⟩ := GlobalTheory.ShFam.EigSpread.exists_stable_eigFrame E H D l Xo c O β Y (io y)
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWU⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
    (a := y) (u := (io ⁻¹ᵁ U : T.Opens)) hy (io ⁻¹ᵁ U).2
  have hW : IsAffineOpen W := hW
  have e : (show Sp Γ(T, W) ⟶ T from hW.fromSpec) ≫ io =
      spMap (io.appLE U W hWU).hom ≫ (show Sp Γ(gen Y, U) ⟶ gen Y from hU.fromSpec) :=
    (IsAffineOpen.SpecMap_appLE_fromSpec io hU hW hWU).symm
  obtain ⟨g, -⟩ := exists_bc f (io.appLE U W hWU).hom (φ' := (io.appLE U W hWU).hom.comp φ)
    (x' := ((show Sp Γ(T, W) ⟶ T from hW.fromSpec) ≫ io) ≫ genι Y) rfl (by rw [e, Category.assoc])
  refine ⟨W, hW, _, g, hyW, ?_⟩
  rw [e, Category.assoc, spMap_comp₂]
  exact congrArg _ hφ

open GlobalTheory.Points GlobalTheory.ShFam.EigLoc in

theorem exists_affine_holFrames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (e : c.F →+* ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsOpenImmersion io → io ≫ genStr Y = B.str → ∃ (W : B.X → B.X.Opens) (hW : ∀ y, IsAffineOpen (W y)) (φ : ∀ y, c.F →+* Γ(B.X, W y)) (fr : ∀ y, EigFrame Y (φ y) (((show Sp Γ(B.X, W y) ⟶ B.X from (hW y).fromSpec) ≫ io) ≫ genι Y)) (a : B.X → GlobalTheory.CxPts B.str e → CxFr Y e), (∀ y, y ∈ W y) ∧ (∀ y, ((show Sp Γ(B.X, W y) ⟶ B.X from (hW y).fromSpec) ≫ io) ≫ genStr Y = spMap (φ y)) ∧ (∀ y p, (a y p).1.1 = p.1 ≫ io) ∧ (∀ y p (h : p ∈ GlobalTheory.CxPts.ptsIn B.str e (W y)) ρ i, (a y p).2.v ρ i = spMap (Chart.dualMapR (GlobalTheory.CxPts.evHom h)) ≫ (fr y).v ρ i) ∧ ∀ y (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (A : Set V) (x : V → GlobalTheory.CxPts B.str e), IsOpen A → IsHolTo A (fun b => (x b).1) → Set.MapsTo x A (GlobalTheory.CxPts.ptsIn B.str e (W y)) → HolFam A (fun b => a y (x b)) := by
  intro E _ _ _ H D l Xo c O _ β Y e B io _ hio
  choose U hU φ fr hy hφ using fun y => exists_affine_frame Y io y
  have hov : ∀ p : GlobalTheory.CxPts B.str e, (p.1 ≫ io) ≫ genStr Y = spMap e := fun p => by
    rw [Category.assoc, hio, p.2]
  have hp : ∀ y (p : GlobalTheory.CxPts B.str e) (h : p ∈ GlobalTheory.CxPts.ptsIn _ _ (U y)),
      spMap (GlobalTheory.CxPts.evHom h) ≫ (show Sp Γ(B.X, U y) ⟶ B.X from (hU y).fromSpec) = p.1 := fun y p h =>
    specMap_valMap_fromSpec (hU y) p.1 h
  have hx : ∀ y (p : GlobalTheory.CxPts B.str e) (h : p ∈ GlobalTheory.CxPts.ptsIn _ _ (U y)), (p.1 ≫ io) ≫ genι Y =
      spMap (GlobalTheory.CxPts.evHom h) ≫ ((show Sp Γ(B.X, U y) ⟶ B.X from (hU y).fromSpec) ≫ io) ≫ genι Y := fun y p h => by
    rw [← hp y p h]
    simp only [Category.assoc]
  have ex : ∀ y (p : GlobalTheory.CxPts B.str e), ∃ g : EigFrame Y e ((p.1 ≫ io) ≫ genι Y),
      ∀ h : p ∈ GlobalTheory.CxPts.ptsIn _ _ (U y), ∀ ρ i,
        g.v ρ i = spMap (Chart.dualMapR (GlobalTheory.CxPts.evHom h)) ≫ (fr y).v ρ i := fun y p => by
    by_cases h : p ∈ GlobalTheory.CxPts.ptsIn _ _ (U y)
    · obtain ⟨g, hg⟩ := exists_bc (fr y) (GlobalTheory.CxPts.evHom h) (φ' := e) (spMap_inj (by
        rw [spMap_comp₂, ← hφ y, ← hov p, ← hp y p h]
        simp only [Category.assoc])) (hx y p h)
      exact ⟨g, fun _ => hg⟩
    · obtain ⟨g⟩ := exists_eigFrame E H D l Xo c O β Y ℂ e _ (hov p)
      exact ⟨g, fun h' => (h h').elim⟩
  choose g hg using ex
  refine ⟨U, hU, φ, fr, fun y p => ⟨⟨p.1 ≫ io, hov p⟩, g y p⟩, hy, hφ, fun _ _ => rfl, hg,
    fun y V _ _ _ A x hA hol hm => ⟨fun W f => by
      simp only [valAt'_eq_valR, valR_comp]
      exact hol (io ⁻¹ᵁ W) ((io.app W).hom f), fun ρ i => ?_⟩⟩
  exact holTan_dualMap hA ((fr y).v ρ i) (fun b hb => GlobalTheory.CxPts.evHom (hm hb)) (fun a => ⟨_,
    (hol (U y) a).2.mono fun b hb => ⟨hb, hm hb⟩, fun b hb => (GlobalTheory.CxPts.ev_eq (hm hb) a).symm⟩)
    fun b hb => hg y _ (hm hb) ρ i

end GlobalTheory.ShFam.HolFrames
