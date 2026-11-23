import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExOfHodgeWt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvTrans

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X Y : Scheme.{0}} {t : SAB H Y} {p : X ⟶ Y} {G' : Over X} [GrpObj G'] {ψ : G'.left ⟶ t.G.left}

open Classical in

def trv (hψ : IsPullback ψ G'.hom t.G.hom p) (g : G'.left ⟶ G'.left) {R : Type} [CommRing R] (q : Sp R ⟶ X)
    (v : Sp (DualNumber R) ⟶ t.G.left) : Sp (DualNumber R) ⟶ t.G.left :=
  if h : v ≫ t.G.hom = (spMap (algebraMap R (DualNumber R)) ≫ q) ≫ p then hψ.lift v _ h ≫ g ≫ ψ else v

variable (hψ : IsPullback ψ G'.hom t.G.hom p) {R R' : Type} [CommRing R] [CommRing R']

theorem trv_eq (g : G'.left ⟶ G'.left) (q : Sp R ⟶ X) {v : Sp (DualNumber R) ⟶ t.G.left}
    (w : Sp (DualNumber R) ⟶ G'.left) (hw : w ≫ ψ = v) (hw' : w ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ q) :
    trv hψ g q v = w ≫ g ≫ ψ := by
  have h : v ≫ t.G.hom = (spMap (algebraMap R (DualNumber R)) ≫ q) ≫ p := by
    rw [← hw, Category.assoc, hψ.w, ← Category.assoc, hw']
  rw [trv, dif_pos h]
  congr 1
  exact hψ.hom_ext (by rw [hψ.lift_fst, hw]) (by rw [hψ.lift_snd, hw'])

include hψ in

theorem exists_lift (q : Sp R ⟶ X) {v : Sp (DualNumber R) ⟶ t.G.left}
    (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    ∃ w : Sp (DualNumber R) ⟶ G'.left, w ≫ ψ = v ∧ w ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ q :=
  ⟨hψ.lift v _ (by rw [hv, Category.assoc]), hψ.lift_fst _ _ _, hψ.lift_snd _ _ _⟩

theorem trv_over (g : G'.left ⟶ G'.left) {b : X ⟶ X} (hg : g ≫ G'.hom = G'.hom ≫ b) (q : Sp R ⟶ X)
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ g q v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ (q ≫ b) ≫ p := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  rw [trv_eq hψ g q w hw hw', Category.assoc, Category.assoc, hψ.w, reassoc_of% hg, reassoc_of% hw']
  simp only [Category.assoc]

theorem trv_map (g : G'.left ⟶ G'.left) (σ : R →+* R') (q : Sp R ⟶ X) {v : Sp (DualNumber R) ⟶ t.G.left}
    (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ g (spMap σ ≫ q) (spMap (dualMap σ) ≫ v) = spMap (dualMap σ) ≫ trv hψ g q v := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  have e : spMap (dualMap σ) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R' (DualNumber R')) ≫ spMap σ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
  rw [trv_eq hψ g q w hw hw', trv_eq hψ g (spMap σ ≫ q) (spMap (dualMap σ) ≫ w) (by rw [Category.assoc, hw])
    (by rw [Category.assoc, hw', ← Category.assoc, e, Category.assoc])]
  simp only [Category.assoc]

theorem trv_comp (g₁ g₂ : G'.left ⟶ G'.left) {b₁ : X ⟶ X} (hg₁ : g₁ ≫ G'.hom = G'.hom ≫ b₁) (q : Sp R ⟶ X)
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ (g₁ ≫ g₂) q v = trv hψ g₂ (q ≫ b₁) (trv hψ g₁ q v) := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  rw [trv_eq hψ _ q w hw hw', trv_eq hψ g₁ q w hw hw', trv_eq hψ g₂ (q ≫ b₁) (w ≫ g₁) (Category.assoc _ _ _)
    (by rw [Category.assoc, hg₁, reassoc_of% hw'])]
  simp only [Category.assoc]

theorem trv_eq_self (g : G'.left ⟶ G'.left) (q : Sp R ⟶ X)
    (hg : ∀ w : Sp (DualNumber R) ⟶ G'.left, w ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ q → w ≫ g = w)
    {v : Sp (DualNumber R) ⟶ t.G.left} (hv : v ≫ t.G.hom = spMap (algebraMap R (DualNumber R)) ≫ q ≫ p) :
    trv hψ g q v = v := by
  obtain ⟨w, hw, hw'⟩ := exists_lift hψ q hv
  rw [trv_eq hψ g q w hw hw', ← Category.assoc, hg w hw', hw]

end GlobalTheory.EqvTrans
