import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.Toroidal

namespace GlobalTheory.HorComp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
  {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz] {β : Oz →+* c.F}
  (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

abbrev genCx (σ : c.F →+* ℂ) : Scheme.{0} := pullback (genStr Z) (spMap σ)

omit [NumberField E] [IsCMField E] in

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

variable {Z} {Y : Scheme.{0}} {q : Y ⟶ Sp Oz}

abbrev cxFib {R F : Type} [CommRing R] [CommRing F] (β : R →+* F) (q : Y ⟶ Sp R) (σ : F →+* ℂ) : Scheme.{0} :=
  pullback q (spMap (σ.comp β))

def toGen (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) : cxFib β q σ ⟶ gen Z :=
  pullback.lift (pullback.fst _ _ ≫ j) (pullback.snd _ _ ≫ spMap σ)
    (by rw [Category.assoc, hj, pullback.condition, Category.assoc, spMap_comp_spMap])

def toGenCx (j : Y ⟶ Z.X) (hj : j ≫ Z.s = q) (σ : c.F →+* ℂ) : cxFib β q σ ⟶ genCx Z σ :=
  pullback.lift (toGen j hj σ) (pullback.snd _ _) (pullback.lift_snd _ _ _)

variable (Z) in

def ptOf {σ : c.F →+* ℂ} (x : CxPts (genStr Z) σ) : genCx Z σ :=
  (pullback.lift x.1 (𝟙 _) (x.2.trans (Category.id_comp _).symm) : Sp ℂ ⟶ genCx Z σ) (IsLocalRing.closedPoint ℂ)

variable (Z) in

def ptsOf {σ : c.F →+* ℂ} (T : Set (genCx Z σ)) : Set (CxPts (genStr Z) σ) := {x | ptOf Z x ∈ T}

variable (Z) in

def bdCx (σ : c.F →+* ℂ) : Set (genCx Z σ) := pullback.fst (genStr Z) (spMap σ) ⁻¹' (genBd Z : Set (gen Z))

variable (Z) in

theorem fst_ptOf {σ : c.F →+* ℂ} (x : CxPts (genStr Z) σ) :
    pullback.fst (genStr Z) (spMap σ) (ptOf Z x) = x.1 (IsLocalRing.closedPoint ℂ) := by
  exact congrArg (fun g : Sp ℂ ⟶ gen Z =>  g (IsLocalRing.closedPoint ℂ)) (pullback.lift_fst _ _ _)

theorem mem_ptsOf_bdCx {σ : c.F →+* ℂ} (x : CxPts (genStr Z) σ) :
    x ∈ ptsOf Z (bdCx Z σ) ↔ x.1 (IsLocalRing.closedPoint ℂ) ∈ (genBd Z : Set (gen Z)) := by
  simp only [ptsOf, bdCx, Set.mem_setOf_eq, Set.mem_preimage, fst_ptOf]

end GlobalTheory.HorComp

end
