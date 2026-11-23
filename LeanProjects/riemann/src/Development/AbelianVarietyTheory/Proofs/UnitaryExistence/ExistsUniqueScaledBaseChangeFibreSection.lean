import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric

noncomputable section

namespace GlobalTheory.Frames.SecPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem exists_pull_linComb {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (φ' : K → (Z ⟶ X)) (ε : K → ℤ) (h : Z ⟶ Y) (e : (fun k => h ≫ φ k) = φ') (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε), ∀ (j : K → L.ι)
      (hle : (LB.LinComb L φ' ε).U j ≤ h ⁻¹ᵁ (LB.LinComb L φ ε).U j), (h.appLE _ _ hle).hom (s.f j) = s'.f j := by
  subst e
  exact ⟨DVR.pullSec L φ ε s h, fun _ _ => rfl⟩

theorem lbSec_ext {X : Scheme.{0}} {L : LB X} {s t : LB.Sec L} (h : ∀ i, s.f i = t.f i) : s = t := by
  cases s; cases t
  congr 1
  exact funext h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem ppx_chart_le {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hs : pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i := by
  intro p hp
  have hp' : ∀ k, p ∈ (snd (Over.mk x') Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _) :=
    Set.mem_iInter.1 hp
  have e := congrArg (fun f : Gx x' ⟶ Xo.univ.t.G.left => f.base p) hs
  show pm.base p ∈ ⋂ k, (snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U (i k) : Set _)
  refine Set.mem_iInter.2 fun k => ?_
  show (pm ≫ (snd (Over.mk x) Xo.univ.t.G).left).base p ∈ (Xo.univ.t.PP.L.U (i k) : Set _)
  rw [e]
  exact hp' k

theorem res_res_top {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (g : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom g) =
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom g := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem scal_res {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (i j : (PPx x).ι) :
    ((Gx x).presheaf.map (homOfLE (inf_le_left : (PPx x).U i ⊓ (PPx x).U j ≤ (PPx x).U i)).op).hom (scal x a i) =
      ((Gx x).presheaf.map (homOfLE (inf_le_right : (PPx x).U i ⊓ (PPx x).U j ≤ (PPx x).U j)).op).hom
        (scal x a j) := by
  simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun]
  rw [res_res_top, res_res_top]

def gxMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X)
    (h : spMap ψ ≫ x = x') : Gx x' ⟶ Gx x :=
  ((Over.homMk (spMap ψ) h : Over.mk x' ⟶ Over.mk x) ▷ Xo.univ.t.G).left

theorem gxMap_snd {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X)
    (h : spMap ψ ≫ x = x') :
    gxMap ψ x x' h ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left := by
  unfold gxMap
  rw [← Over.comp_left, whiskerRight_snd]

theorem gxMap_fst {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X)
    (h : spMap ψ ≫ x = x') :
    gxMap ψ x x' h ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap ψ := by
  unfold gxMap
  rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  rfl

theorem gx_hom_ext {S : Type} [CommRing S] {W : Scheme.{0}} {x : Sp S ⟶ Xo.X} (f₁ f₂ : W ⟶ Gx x)
    (h₁ : f₁ ≫ (fst (Over.mk x) Xo.univ.t.G).left = f₂ ≫ (fst (Over.mk x) Xo.univ.t.G).left)
    (h₂ : f₁ ≫ (snd (Over.mk x) Xo.univ.t.G).left = f₂ ≫ (snd (Over.mk x) Xo.univ.t.G).left) : f₁ = f₂ :=
  Over.tensorObj_ext f₁ f₂ h₁ h₂

def scalSec {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (s : LB.Sec (PPx x)) : LB.Sec (PPx x) where
  f i := scal x a i * s.f i
  compat i j := by
    rw [map_mul, map_mul, s.compat i j, scal_res x a i j]
    ring

theorem existsUnique_secBC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (a : S) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X), x' = spMap φ ≫ x → ∀ s : LB.Sec (PPx x), ∃! s' : LB.Sec (PPx x'), SecBC φ a x x' s s' := by
  intro E _ _ _ H Dw l Xo S T _ _ φ a x x' hx s
  have hs := gxMap_snd φ x x' hx.symm
  have hf := gxMap_fst φ x x' hx.symm
  obtain ⟨s', hs'⟩ := exists_pull_linComb Xo.univ.t.PP.L (K := Fin 1)
    (fun _ => (snd (Over.mk x) Xo.univ.t.G).left) (fun _ => (snd (Over.mk x') Xo.univ.t.G).left) _
    (gxMap φ x x' hx.symm) (funext fun _ => hs) (scalSec x a s)
  refine ⟨s', ⟨_, hs, hf, hs'⟩, ?_⟩
  rintro t ⟨pm, ps, pf, ht⟩
  obtain rfl : pm = gxMap φ x x' hx.symm :=
    gx_hom_ext _ _ (pf.trans hf.symm) (ps.trans hs.symm)
  exact lbSec_ext fun i => (ht i (ppx_chart_le _ hs i)).symm.trans (hs' i (ppx_chart_le _ hs i))

end GlobalTheory.Frames.SecPull
