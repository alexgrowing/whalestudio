import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GrNormCompCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.Conormal GlobalTheory.LieVB GlobalTheory.DualPull NumberField
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.TanSec

open Classical in

def tanMor {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (x : Sp R ⟶ S)
    (v : Sp (DualNumber R) ⟶ G.left) :
    (Scheme.Modules.pullback x).obj (omega G) ⟶ structureModule (Sp R) :=
  if h : v ≫ G.hom = (ReciprocityTheory.ChartRestriction.G.Pdiv.specO R (DualNumber R)).hom ≫ x ∧ sec (epsZero R) ≫ v = x ≫ unitSec G then
    baseMap (sec_hom (epsZero R)) h.1 h.2 ≫ (epsIso R).hom
  else 0

open Classical in

def secOf {X Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (M : X.Modules)
    (φ : (Scheme.Modules.pullback j).obj M ⟶ structureModule Y) : Γ(dual M, j ''ᵁ ⊤) :=
  if h : IsIso (theta j M) then
    ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app (dual M)).app ⊤
      ((inv (theta j M)).app ⊤ ((homGlobalEquiv _ _).symm φ))
  else 0

section Mdl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

instance isOpenImmersion_chart (Z : LocM.Mdl Y i₀) (a : Fin Z.m) : IsOpenImmersion (Z.chart a) :=
  (Z.U a).2.isOpenImmersion_fromSpec

theorem chart_image_top (Z : LocM.Mdl Y i₀) (a : Fin Z.m) : Z.chart a ''ᵁ ⊤ = (Z.U a).1 := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  exact (Z.U a).2.opensRange_fromSpec

def om (Z : LocM.Mdl Y i₀) : Z.X.Modules := (Scheme.Modules.pullback Z.π).obj (omega (Y Z.i).t.G)

def sec (Z : LocM.Mdl Y i₀) (a : Fin Z.m) (v : Sp (DualNumber Γ(Z.X, (Z.U a).1)) ⟶ (Y Z.i).t.G.left) :
    Γ(dual (om Z), (Z.U a).1) :=
  resM (dual (om Z)) (chart_image_top Z a).ge
    (secOf (Z.chart a) (om Z)
      ((Scheme.Modules.pullbackComp (Z.chart a) Z.π).hom.app _ ≫ tanMor _ (Z.chart a ≫ Z.π) v))

def lieX (Z : LocM.Mdl Y i₀) {X : Scheme.{0}} (h : X ⟶ Z.X) : X.Modules :=
  (Scheme.Modules.pullback h).obj (dual (om Z))

def secX (Z : LocM.Mdl Y i₀) {X : Scheme.{0}} (h : X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw) (a : Fin Z.m)
    (i : Fin r) : Γ(lieX Z h, h ⁻¹ᵁ (Z.U a).1) :=
  GlobalTheory.QCoh.pullbackSections h _ le_rfl (sec Z a (Z.fr a (x i).1 (x i).2))

end Mdl

end GlobalTheory.TanSec
