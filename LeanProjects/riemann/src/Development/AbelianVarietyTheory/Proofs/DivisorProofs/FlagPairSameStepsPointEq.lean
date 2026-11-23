import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Adj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPairPullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic
open GlobalTheory.VB (IsVB)

namespace GlobalTheory.Vert.FlagSame

open GlobalTheory.Vert.Model

section Flags

variable {X : Scheme.{0}} {E : X.Modules} {N : ℕ} {fl fl' : Flag E N}

theorem step_comm (i : Fin N) (e₀ : fl.F i.castSucc ≅ fl'.F i.castSucc)
    (e₁ : fl.F i.succ ≅ fl'.F i.succ) (h₀ : e₀.hom ≫ fl'.ι i.castSucc = fl.ι i.castSucc)
    (h₁ : e₁.hom ≫ fl'.ι i.succ = fl.ι i.succ) :
    fl.step i ≫ e₁.hom = e₀.hom ≫ fl'.step i := by
  rw [← cancel_mono (fl'.ι i.succ)]
  simp only [Category.assoc, h₁, Flag.step_ι, h₀]

def grMap (i : Fin N) (e₀ : fl.F i.castSucc ≅ fl'.F i.castSucc) (e₁ : fl.F i.succ ≅ fl'.F i.succ)
    (w : fl.step i ≫ e₁.hom = e₀.hom ≫ fl'.step i) : fl.gr i ≅ fl'.gr i :=
  cokernel.mapIso _ _ e₀ e₁ w

theorem π_grMap_hom (i : Fin N) (e₀ : fl.F i.castSucc ≅ fl'.F i.castSucc)
    (e₁ : fl.F i.succ ≅ fl'.F i.succ) (w : fl.step i ≫ e₁.hom = e₀.hom ≫ fl'.step i) :
    fl.π i ≫ (grMap i e₀ e₁ w).hom = e₁.hom ≫ fl'.π i := by
  simp [grMap, Flag.π, Flag.gr]

theorem smallCls_root_eq (i : Fin N) (e₀ : fl.F i.castSucc ≅ fl'.F i.castSucc)
    (e₁ : fl.F i.succ ≅ fl'.F i.succ) (w : fl.step i ≫ e₁.hom = e₀.hom ≫ fl'.step i) :
    smallCls _ (fl.isLB_root i) = smallCls _ (fl'.isLB_root i) :=
  (smallCls_eq_iff _ _).2 ((fl.isVB_gr i).lbIso_det_of_iso (grMap i e₀ e₁ w))

end Flags

section Pairs

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Model O}
  {E E' : B.X.Modules} {φ : B.GenIso E E'} {N : ℕ}

theorem gen_eq (P P' : FlagPair φ N) (j : Fin (N + 1)) (e : P.fl.F j ≅ P'.fl.F j)
    (he : e.hom ≫ P'.fl.ι j = P.fl.ι j) (e' : P.fl'.F j ≅ P'.fl'.F j)
    (he' : e'.hom ≫ P'.fl'.ι j = P.fl'.ι j) :
    P'.gen j = B.genRes.mapIso e.symm ≪≫ P.gen j ≪≫ B.genRes.mapIso e' := by
  refine (P'.gen_unique j _ ?_).symm
  have h1 : e.inv ≫ P.fl.ι j = P'.fl.ι j := by rw [← he, Iso.inv_hom_id_assoc]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [← Functor.map_comp, he', P.gen_ι, ← Functor.map_comp_assoc, h1]

theorem grIso_eq (P P' : FlagPair φ N) (i : Fin N) (β : P.fl.gr i ≅ P'.fl.gr i)
    (β' : P.fl'.gr i ≅ P'.fl'.gr i) (e₁ : P.fl.F i.succ ≅ P'.fl.F i.succ)
    (e₁' : P.fl'.F i.succ ≅ P'.fl'.F i.succ) (hβ : P.fl.π i ≫ β.hom = e₁.hom ≫ P'.fl.π i)
    (hβ' : P.fl'.π i ≫ β'.hom = e₁'.hom ≫ P'.fl'.π i)
    (hg : P'.gen i.succ = B.genRes.mapIso e₁.symm ≪≫ P.gen i.succ ≪≫ B.genRes.mapIso e₁') :
    P'.grIso i = (B.genRes.mapIso β).symm ≪≫ (P.grIso i ≪≫ B.genRes.mapIso β') := by
  refine Iso.ext ?_
  rw [← cancel_epi (B.genRes.map (P'.fl.π i)), P'.π_grIso_hom i, hg]
  have a : P'.fl.π i ≫ β.inv = e₁.inv ≫ P.fl.π i := by
    rw [Iso.comp_inv_eq, Category.assoc, hβ, Iso.inv_hom_id_assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
  rw [← Functor.map_comp_assoc, a, Functor.map_comp_assoc, reassoc_of% (P.π_grIso_hom i),
    ← Functor.map_comp, ← hβ', Functor.map_comp]

end Pairs

theorem cls_div_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Model O}
    {E E' : B.X.Modules} {φ : B.GenIso E E'} {N : ℕ} (P P' : FlagPair φ N) (i : Fin N)
    (e₀ : P.fl.F i.castSucc ≅ P'.fl.F i.castSucc) (e₁ : P.fl.F i.succ ≅ P'.fl.F i.succ)
    (he₁ : e₁.hom ≫ P'.fl.ι i.succ = P.fl.ι i.succ)
    (w : P.fl.step i ≫ e₁.hom = e₀.hom ≫ P'.fl.step i)
    (e₀' : P.fl'.F i.castSucc ≅ P'.fl'.F i.castSucc) (e₁' : P.fl'.F i.succ ≅ P'.fl'.F i.succ)
    (he₁' : e₁'.hom ≫ P'.fl'.ι i.succ = P.fl'.ι i.succ)
    (w' : P.fl'.step i ≫ e₁'.hom = e₀'.hom ≫ P'.fl'.step i) :
    (P.div i).cls = (P'.div i).cls := by
  have hg := gen_eq P P' i.succ e₁ he₁ e₁' he₁'
  simp only [FlagPair.div]
  rw [    grIso_eq P P' i _ _ e₁ e₁' (π_grMap_hom i e₀ e₁ w) (π_grMap_hom i e₀' e₁' w') hg,
    GenIso.cls_div_trans (hE' := P.fl.isVB_gr i),
    GenIso.cls_div_trans (hE' := P.fl'.isVB_gr i), ← Functor.mapIso_symm,
    GlobalTheory.Vert.FlagPairPull.cls_div_mapIso, GlobalTheory.Vert.FlagPairPull.cls_div_mapIso, zero_add, add_zero]

end GlobalTheory.Vert.FlagSame

section Main

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option linter.overlappingInstances false in

theorem GlobalTheory.Vert.FlagSame.toFPair_eq_of_sameStep : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B : GlobalTheory.Vert.Model O) (E E' : B.X.Modules) (φ : B.GenIso E E') (r : ℕ) (P P' : GlobalTheory.Vert.Model.FlagPair φ r) (i : Fin r), P.fl.SameStep P'.fl i.castSucc → P.fl.SameStep P'.fl i.succ → P.fl'.SameStep P'.fl' i.castSucc → P.fl'.SameStep P'.fl' i.succ → (P.toFPair p).x i = (P'.toFPair p).x i ∧ (P.toFPair p).x' i = (P'.toFPair p).x' i ∧ (P.toFPair p).Dv i = (P'.toFPair p).Dv i := by
  intro O _ _ _ p _ _ _ B E E' φ r P P' i h₀ h₁ h₀' h₁'
  obtain ⟨e₀, he₀⟩ := h₀
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₀', he₀'⟩ := h₀'
  obtain ⟨e₁', he₁'⟩ := h₁'
  have w := GlobalTheory.Vert.FlagSame.step_comm i e₀ e₁ he₀ he₁
  have w' := GlobalTheory.Vert.FlagSame.step_comm i e₀' e₁' he₀' he₁'
  refine ⟨GlobalTheory.Vert.FlagSame.smallCls_root_eq i e₀ e₁ w,
    GlobalTheory.Vert.FlagSame.smallCls_root_eq i e₀' e₁' w', ?_⟩
  exact congrArg GlobalTheory.Vert.Model.toQ
    (GlobalTheory.Vert.FlagSame.cls_div_eq P P' i e₀ e₁ he₁ w e₀' e₁' he₁' w')

end Main
