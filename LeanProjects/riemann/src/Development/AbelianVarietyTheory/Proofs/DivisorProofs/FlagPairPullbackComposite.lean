import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.Vert.PullTwice

variable {X Y Z W : Scheme.{0}}

def compIso (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (h : a ≫ b = c) :
    Scheme.Modules.pullback b ⋙ Scheme.Modules.pullback a ≅ Scheme.Modules.pullback c :=
  Scheme.Modules.pullbackComp a b ≪≫ Scheme.Modules.pullbackCongr h

theorem compIso_assoc (a : X ⟶ Y) (b : Y ⟶ Z) (d : Z ⟶ W) (ab : X ⟶ Z) (bd : Y ⟶ W)
    (abd : X ⟶ W) (h₁ : a ≫ b = ab) (h₂ : b ≫ d = bd) (h₃ : ab ≫ d = abd) (h₄ : a ≫ bd = abd)
    (M : W.Modules) :
    (compIso a b ab h₁).hom.app ((Scheme.Modules.pullback d).obj M) ≫
        (compIso ab d abd h₃).hom.app M =
      (Scheme.Modules.pullback a).map ((compIso b d bd h₂).hom.app M) ≫
        (compIso a bd abd h₄).hom.app M := by
  subst h₁ h₂ h₃
  have H := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity a b d) M
  simp at H
  simp [compIso, Scheme.Modules.pullbackCongr]
  rw [← cancel_epi ((Scheme.Modules.pullbackComp a (b ≫ d)).inv.app M ≫
    (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b d).inv.app M))]
  simp only [Category.assoc]
  rw [H]
  simp [← Functor.map_comp_assoc]

open GlobalTheory.Vert.Model GlobalTheory.Vert.Model.GenIso

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem genPullIso_eq {Z Z₁ : Model O} {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str)
    (y : Z₁.gen.toScheme ⟶ Z.X) (hy₁ : Z₁.gen.ι ≫ f = y) (hy₂ : genMap hf ≫ Z.gen.ι = y) :
    genPullIso hf = compIso Z₁.gen.ι f y hy₁ ≪≫ (compIso (genMap hf) Z.gen.ι y hy₂).symm := by
  subst hy₁
  refine Iso.ext (NatTrans.ext (funext fun M => ?_))
  simp only [genPullIso, compIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Iso.trans_inv,
    Category.assoc]
  congr 1

theorem genMap_comp_ι {Z Z₁ : Model O} {f : Z₁.X ⟶ Z.X} (hf : f ≫ Z.str = Z₁.str) :
    genMap hf ≫ Z.gen.ι = Z₁.gen.ι ≫ f := by
  simp [genMap]

variable {B B₁ B₂ : Model O} {f : B₁.X ⟶ B.X} (hf : f ≫ B.str = B₁.str) {h : B₂.X ⟶ B₁.X}
  (hh : h ≫ B₁.str = B₂.str) {c : B₂.X ⟶ B.X} (hc : c ≫ B.str = B₂.str) (hfc : h ≫ f = c)

include hfc in
theorem genMap_comp : genMap hh ≫ genMap hf = genMap hc := by
  rw [← cancel_mono B.gen.ι, Category.assoc, genMap_comp_ι, ← Category.assoc, genMap_comp_ι,
    genMap_comp_ι, Category.assoc, hfc]

include hfc in
theorem theta (M : B.X.Modules) :
    (genPullIso hh).hom.app ((Scheme.Modules.pullback f).obj M) ≫
      (Scheme.Modules.pullback (genMap hh)).map ((genPullIso hf).hom.app M) ≫
        (compIso (genMap hh) (genMap hf) (genMap hc) (genMap_comp hf hh hc hfc)).hom.app
          ((Scheme.Modules.pullback B.gen.ι).obj M) =
    (Scheme.Modules.pullback B₂.gen.ι).map ((compIso h f c hfc).hom.app M) ≫
      (genPullIso hc).hom.app M := by
  have hx : genMap hh ≫ B₁.gen.ι = B₂.gen.ι ≫ h := genMap_comp_ι hh
  have hxw : (B₂.gen.ι ≫ h) ≫ f = B₂.gen.ι ≫ c := by rw [Category.assoc, hfc]
  have hyw : genMap hh ≫ (B₁.gen.ι ≫ f) = B₂.gen.ι ≫ c := by
    rw [← Category.assoc, hx, hxw]
  have A1 := compIso_assoc B₂.gen.ι h f _ c _ rfl hfc hxw rfl M
  have A2 := compIso_assoc (genMap hh) B₁.gen.ι f _ _ _ hx rfl hxw hyw M
  have A3 := compIso_assoc (genMap hh) (genMap hf) B.gen.ι _ _ _ (genMap_comp hf hh hc hfc)
    (genMap_comp_ι hf) (genMap_comp_ι hc) hyw M
  rw [genPullIso_eq hf _ rfl (genMap_comp_ι hf), genPullIso_eq hh _ rfl hx,
    genPullIso_eq hc _ rfl (genMap_comp_ι hc)]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc, Functor.map_comp]
  rw [← cancel_mono ((compIso (genMap hc) B.gen.ι _ (genMap_comp_ι hc)).hom.app M)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [A3]
  simp only [← Functor.map_comp_assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← A2, Iso.inv_hom_id_app_assoc, A1]

include hfc in
theorem pull_pull_hom {E E' : B.X.Modules} (φ : B.GenIso E E') :
    ((φ.pull hf).pull hh).hom ≫ B₂.genRes.map ((compIso h f c hfc).hom.app E') =
      B₂.genRes.map ((compIso h f c hfc).hom.app E) ≫ (φ.pull hc).hom := by
  have T := theta hf hh hc hfc E
  have T' : (Scheme.Modules.pullback B₂.gen.ι).map ((compIso h f c hfc).hom.app E') =
      (genPullIso hh).hom.app ((Scheme.Modules.pullback f).obj E') ≫
        (Scheme.Modules.pullback (genMap hh)).map ((genPullIso hf).hom.app E') ≫
          (compIso (genMap hh) (genMap hf) (genMap hc) (genMap_comp hf hh hc hfc)).hom.app
            ((Scheme.Modules.pullback B.gen.ι).obj E') ≫ (genPullIso hc).inv.app E' := by
    rw [reassoc_of% (theta hf hh hc hfc E'), Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  simp only [GenIso.pull, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Category.assoc, Functor.map_comp]
  rw [T', ← reassoc_of% T]
  have N := (compIso (genMap hh) (genMap hf) (genMap hc) (genMap_comp hf hh hc hfc)).hom.naturality
    φ.hom
  simp only [Functor.comp_map] at N
  rw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc _ ((genPullIso hf).inv.app E'),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% N]

end GlobalTheory.Vert.PullTwice

open GlobalTheory.Vert.PullTwice in

theorem GlobalTheory.Vert.Model.FlagPair.exists_pull_comp : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p] (B B₁ B₂ : GlobalTheory.Vert.Model O) (f : B₁.X ⟶ B.X) (hf : f ≫ B.str = B₁.str) (h : B₂.X ⟶ B₁.X) (hh : h ≫ B₁.str = B₂.str) (c : B₂.X ⟶ B.X) (hc : c ≫ B.str = B₂.str), h ≫ f = c → ∀ (E E' : B.X.Modules) (φ : B.GenIso E E') (r : ℕ) (P : GlobalTheory.Vert.Model.FlagPair ((φ.pull hf).pull hh) r), ∃ P' : GlobalTheory.Vert.Model.FlagPair (φ.pull hc) r, ∀ i, (P'.toFPair p).x i = (P.toFPair p).x i ∧ (P'.toFPair p).x' i = (P.toFPair p).x' i ∧ (P'.toFPair p).Dv i = (P.toFPair p).Dv i := by
  intro O _ _ _ p _ _ _ B B₁ B₂ f hf h hh c hc hfc E E' φ r P
  have key : ∀ i, (P.gen i).hom ≫ B₂.genRes.map (P.fl'.ι i ≫ (compIso h f c hfc).hom.app E') =
      B₂.genRes.map (P.fl.ι i ≫ (compIso h f c hfc).hom.app E) ≫ (φ.pull hc).hom := fun i => by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, ← pull_pull_hom hf hh hc hfc φ,
      reassoc_of% (P.gen_ι i)]
  exact ⟨{ fl := P.fl.ofIso ((compIso h f c hfc).app E)
           fl' := P.fl'.ofIso ((compIso h f c hfc).app E')
           gen := P.gen
           gen_ι := key }, fun i => ⟨rfl, rfl, rfl⟩⟩
