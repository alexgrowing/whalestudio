import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic
open GlobalTheory.VB (IsVB IsFrame Chart det)

namespace GlobalTheory.Vert.FlagPairPull

open GlobalTheory.Vert.Model

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

section Zero

variable {Z : Model O} {r : ℕ}

theorem cls_div_mapIso {F G : Z.X.Modules} (β : F ≅ G) (hF : IsVB F r) (hG : IsVB G r) :
    (GenIso.div (Z := Z) (Z.genRes.mapIso β : Z.GenIso F G) hF hG).cls = 0 := by
  have := hF.isQuasicoherent
  have := hG.isQuasicoherent
  have hψ : (Z.genRes.mapIso β : Z.GenIso F G).inv = Z.genRes.map β.inv := rfl
  have H : VertDiv.IsSum (VertDiv.zero Z) (VertDiv.zero Z) (GenIso.div (Z := Z) (Z.genRes.mapIso β : Z.GenIso F G) hF hG) := by
    intro i j k
    obtain ⟨c, c'⟩ := k
    refine ⟨c.isFrame.detUnit (c'.isFrame.map_iso β.inv) (inf_le_right.trans inf_le_left)
      (inf_le_right.trans inf_le_right),
      (GenIso.eqn_div_of_hom hF hG hψ c c' le_rfl inf_le_right).trans ?_⟩
    change _ = _ * (resG _ _ 1 * resG _ _ 1)
    simp only [IsFrame.val_detUnit, map_one, mul_one, GlobalTheory.Twist.app_resM]
    rfl
  simpa using H.cls_eq

end Zero

section Pull

variable {B B₁ : Model O} {h : B₁.X ⟶ B.X} (hh : h ≫ B.str = B₁.str)

theorem pull_comm {F G F' G' : B.X.Modules} (a : F ⟶ G) (b : F' ⟶ G') (φF : B.GenIso F F')
    (φG : B.GenIso G G') (w : B.genRes.map a ≫ φG.hom = φF.hom ≫ B.genRes.map b) :
    B₁.genRes.map ((Scheme.Modules.pullback h).map a) ≫ (φG.pull hh).hom =
      (φF.pull hh).hom ≫ B₁.genRes.map ((Scheme.Modules.pullback h).map b) := by
  have n₁ := (GenIso.genPullIso hh).hom.naturality a
  have n₂ := (GenIso.genPullIso hh).inv.naturality b
  simp only [Functor.comp_map] at n₁ n₂
  simp only [GenIso.pull, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Category.assoc]
  rw [← n₂, reassoc_of% n₁, ← Functor.map_comp_assoc, w, Functor.map_comp_assoc]

variable {E E' : B.X.Modules} {φ : B.GenIso E E'} {N : ℕ}

def pairPull (P : FlagPair φ N) : FlagPair (φ.pull hh) N where
  fl := P.fl.pull h
  fl' := P.fl'.pull h
  gen i := (P.gen i).pull hh
  gen_ι i := (pull_comm hh _ _ _ _ (P.gen_ι i).symm).symm

end Pull

section Classes

variable {B B₁ : Model O} {h : B₁.X ⟶ B.X} (hh : h ≫ B.str = B₁.str)
variable {E E' : B.X.Modules} {φ : B.GenIso E E'} {N : ℕ}

theorem smallCls_root_pull (fl : Flag E N) (i : Fin N) :
    smallCls _ ((fl.pull h).isLB_root i) = smallPull h (smallCls _ (fl.isLB_root i)) := by
  rw [smallPull_smallCls h _ (pull_isLB (fl.isLB_root i) h)]
  refine ((smallCls_eq_iff _ _).2 ?_).symm
  exact ((fl.isVB_gr i).lbIso_det_pullback h).trans (pull_isLB (fl.isLB_root i) h)
    ((fl.isVB_gr i).pullback h).isLB_det ((fl.pull h).isLB_root i)
    (((fl.isVB_gr i).pullback h).lbIso_det_of_iso (fl.pullGrIso h i))

theorem grIso_pairPull (P : FlagPair φ N) (i : Fin N) :
    (pairPull hh P).grIso i = (B₁.genRes.mapIso (P.fl.pullGrIso h i)).symm ≪≫
      ((P.grIso i).pull hh ≪≫ B₁.genRes.mapIso (P.fl'.pullGrIso h i)) := by
  refine Iso.ext ?_
  rw [← cancel_epi (B₁.genRes.map ((P.fl.pull h).π i))]
  refine ((pairPull hh P).π_grIso_hom i).trans ?_
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv]
  have e : B₁.genRes.map ((P.fl.pull h).π i) ≫ B₁.genRes.map (P.fl.pullGrIso h i).inv =
      B₁.genRes.map ((Scheme.Modules.pullback h).map (P.fl.π i)) := by
    rw [← Functor.map_comp]
    exact congrArg B₁.genRes.map ((Iso.comp_inv_eq _).2 (Flag.map_π_pullGrIso _ _ _).symm)
  rw [reassoc_of% e, reassoc_of% (pull_comm hh _ _ _ _ (P.π_grIso_hom i)), ← Functor.map_comp,
    Flag.map_π_pullGrIso]
  rfl

theorem cls_div_pairPull (P : FlagPair φ N) (i : Fin N) :
    ((pairPull hh P).div i).cls = vPull hh (P.div i).cls := by
  rw [FlagPair.div, grIso_pairPull,
    GenIso.cls_div_trans (hE' := (P.fl.isVB_gr i).pullback h),
    GenIso.cls_div_trans (hE' := (P.fl'.isVB_gr i).pullback h), ← Functor.mapIso_symm,
    cls_div_mapIso, cls_div_mapIso, DivPull.cls_div_pull, zero_add, add_zero]
  rfl

end Classes

end GlobalTheory.Vert.FlagPairPull

section Main

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option linter.overlappingInstances false in

theorem GlobalTheory.Vert.FlagPairPull.exists_flagPair_pull : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B B₁ : GlobalTheory.Vert.Model O) (h : B₁.X ⟶ B.X) (hh : h ≫ B.str = B₁.str) (E E' : B.X.Modules) (φ : B.GenIso E E') (r : ℕ) (P : GlobalTheory.Vert.Model.FlagPair φ r), ∃ P₁ : GlobalTheory.Vert.Model.FlagPair (φ.pull hh) r, ∀ i, (P₁.toFPair p).x i = smallPull h ((P.toFPair p).x i) ∧ (P₁.toFPair p).x' i = smallPull h ((P.toFPair p).x' i) ∧ (P₁.toFPair p).Dv i = GlobalTheory.Vert.Model.vPullQ hh ((P.toFPair p).Dv i) := by
  intro O _ _ _ p _ _ _ B B₁ h hh E E' φ r P
  refine ⟨GlobalTheory.Vert.FlagPairPull.pairPull hh P, fun i =>
    ⟨GlobalTheory.Vert.FlagPairPull.smallCls_root_pull P.fl i,
      GlobalTheory.Vert.FlagPairPull.smallCls_root_pull P.fl' i, ?_⟩⟩
  change GlobalTheory.Vert.Model.toQ _ = GlobalTheory.Vert.Model.vPullQ hh (GlobalTheory.Vert.Model.toQ _)
  rw [GlobalTheory.Vert.Model.vPullQ_toQ, GlobalTheory.Vert.FlagPairPull.cls_div_pairPull]

end Main
