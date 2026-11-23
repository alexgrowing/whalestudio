import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv
open GlobalTheory.DeRham (spOver spOver_comp)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Closed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

abbrev GeomTate (Dw : Datum H) {k : Type} [Field k] (t : SAB H (Sp k)) : Type :=
  TateIso Dw k (Over.mk (𝟙 (Sp k)) ⟶ t.G) (fun a g => g ≫ t.act.act a)
    (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))

variable {k : Type} [Field k]

def selfIso : SpAlg k k ≅ Over.mk (𝟙 (Sp k)) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ 𝟙 _ = spMap (RingHom.id k)
    rw [Category.comp_id, Cris.spMap_id])

variable {Dw : Datum H} {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k}
  (tw : GG.TorsionTower t.G) (I : GeomTate Dw t)

theorem latPt_pow (n : ℕ) (x : Dw.La) : (selfIso.hom ≫ I.ev (p ^ n) x) ^ p ^ n = 1 := by
  rw [← MonObj.comp_pow, (I.onto (p ^ n) (pow_pos (Fact.out : p.Prime).pos n) _).2 ⟨x, rfl⟩, MonObj.comp_one]

def latPt (n : ℕ) (x : Dw.La) : GG.A n →ₐ[k] k := tw.lift n _ (latPt_pow I n x)

theorem latPt_y (n : ℕ) (x : Dw.La) : spOver (latPt tw I n x) ≫ tw.y n = selfIso.hom ≫ I.ev (p ^ n) x :=
  tw.lift_y n _ _

theorem latPt_compat (n : ℕ) (x : Dw.La) :
    (latPt tw I (n + 1) x).comp (GG.mulP n : GG.A n →ₐ[k] GG.A (n + 1)) = latPt tw I n x := by
  refine tw.inj n k _ _ ?_
  rw [← spOver_comp, Category.assoc, tw.mulP_y, MonObj.comp_pow, latPt_y, latPt_y, ← MonObj.comp_pow, pow_succ,
    I.tower (p ^ n) p (pow_pos (Fact.out : p.Prime).pos n) (Fact.out : p.Prime).pos]

theorem latPt_add (n : ℕ) (x y : Dw.La) :
    toConv (latPt tw I n (x + y)) = toConv (latPt tw I n x) * toConv (latPt tw I n y) := by
  refine TorsionTower.pts_injective tw n k ?_
  rw [map_mul, TorsionTower.pts_apply, TorsionTower.pts_apply, TorsionTower.pts_apply]
  simp only [WithConv.ofConv_toConv, latPt_y, I.add, MonObj.comp_mul]

def tau : Dw.La →+ GG.Tate :=
  AddMonoidHom.mk' (fun x => ⟨fun n => latPt tw I n x, fun n => latPt_compat tw I n x⟩) fun x y =>
    TateOver.ext_conv fun n => latPt_add tw I n x y

@[simp] theorem tau_pt (x : Dw.La) (n : ℕ) : (tau tw I x).pt n = latPt tw I n x := rfl

variable (p) in

theorem zeta_prim (n : ℕ) : IsPrimitiveRoot (I.ζ (p ^ n) : k) (p ^ n) :=
  IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim _ (pow_pos (Fact.out : p.Prime).pos n))

variable (p) in

theorem zeta_succ_pow (n : ℕ) : (I.ζ (p ^ (n + 1)) : k) ^ p = I.ζ (p ^ n) := by
  rw [pow_succ, ← Units.val_pow_eq_pow_val,
    I.ζ_pow (p ^ n) p (pow_pos (Fact.out : p.Prime).pos n) (Fact.out : p.Prime).pos]

variable (p) in

theorem zeta_zero : (I.ζ (p ^ 0) : k) = 1 := by
  simpa using zeta_prim p I 0

variable (p) in

def eps : (mu p k).Tate := muTate k (fun n => (I.ζ (p ^ n) : k)) (zeta_zero p I) (zeta_succ_pow p I)

@[simp] theorem muRoot_eps (n : ℕ) : muRoot (eps p I) n = I.ζ (p ^ n) := muRoot_muTate ..

end GlobalTheory.GroupBplus.Closed
