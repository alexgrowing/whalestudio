import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasChartsOfForallIsAffineOpen

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open GlobalTheory.CompanionTheory.Ar.GR

namespace PositivityTheory.PrwZar.QiP

variable {R : Type} [CommRing R] {F : Type} [CommRing F] [Algebra R F]

theorem spMap_comp {S T : Type} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]
    (φ : F →ₐ[R] S) (ψ : S →ₐ[R] T) : spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  simp [spMap, ← Spec.map_comp]
  rfl

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {h : sp (R₀ := R) F ⟶ G}

def mulPt (hs : IsFinFlatSub G F h) {S : Type} [CommRing S] [Algebra R S] (φ φ' : F →ₐ[R] S) : F →ₐ[R] S :=
  (hs.mul S φ φ').choose

theorem mulPt_spec (hs : IsFinFlatSub G F h) {S : Type} [CommRing S] [Algebra R S] (φ φ' : F →ₐ[R] S) :
    spMap (mulPt hs φ φ') ≫ h = (spMap φ ≫ h) * (spMap φ' ≫ h) :=
  (hs.mul S φ φ').choose_spec

def onePt (hs : IsFinFlatSub G F h) (S : Type) [CommRing S] [Algebra R S] : F →ₐ[R] S :=
  (hs.one S).choose

theorem onePt_spec (hs : IsFinFlatSub G F h) (S : Type) [CommRing S] [Algebra R S] :
    spMap (onePt hs S) ≫ h = 1 :=
  (hs.one S).choose_spec

theorem pt_ext (hs : IsFinFlatSub G F h) {S : Type} [CommRing S] [Algebra R S] {φ φ' : F →ₐ[R] S}
    (e : spMap φ ≫ h = spMap φ' ≫ h) : φ = φ' :=
  hs.mono S φ φ' e

def powPt (hs : IsFinFlatSub G F h) {S : Type} [CommRing S] [Algebra R S] (φ : F →ₐ[R] S) : ℕ → (F →ₐ[R] S)
  | 0 => onePt hs S
  | n + 1 => mulPt hs (powPt hs φ n) φ

theorem powPt_spec (hs : IsFinFlatSub G F h) {S : Type} [CommRing S] [Algebra R S] (φ : F →ₐ[R] S) (n : ℕ) :
    spMap (powPt hs φ n) ≫ h = (spMap φ ≫ h) ^ n := by
  induction n with
  | zero => rw [pow_zero]; exact onePt_spec hs S
  | succ n ih => rw [pow_succ, ← ih]; exact mulPt_spec hs _ _

variable {S T : Type} [CommRing S] [Algebra R S] [CommRing T] [Algebra R T]

theorem comp_mulPt (hs : IsFinFlatSub G F h) (ψ : S →ₐ[R] T) (φ φ' : F →ₐ[R] S) :
    ψ.comp (mulPt hs φ φ') = mulPt hs (ψ.comp φ) (ψ.comp φ') := by
  apply pt_ext hs
  rw [mulPt_spec, ← spMap_comp, ← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc, Category.assoc,
    mulPt_spec, MonObj.comp_mul]

theorem comp_onePt (hs : IsFinFlatSub G F h) (ψ : S →ₐ[R] T) : ψ.comp (onePt hs S) = onePt hs T := by
  apply pt_ext hs
  rw [onePt_spec, ← spMap_comp, Category.assoc, onePt_spec, MonObj.comp_one]

theorem comp_powPt (hs : IsFinFlatSub G F h) (ψ : S →ₐ[R] T) (φ : F →ₐ[R] S) (n : ℕ) :
    ψ.comp (powPt hs φ n) = powPt hs (ψ.comp φ) n := by
  apply pt_ext hs
  rw [powPt_spec, ← spMap_comp, Category.assoc, powPt_spec, MonObj.comp_pow, ← Category.assoc, spMap_comp]

theorem powPt_mul (hs : IsFinFlatSub G F h) (φ : F →ₐ[R] S) (a b : ℕ) :
    powPt hs φ (a * b) = powPt hs (powPt hs φ a) b := by
  apply pt_ext hs
  rw [powPt_spec, powPt_spec, powPt_spec, pow_mul]

theorem mulPt_onePt (hs : IsFinFlatSub G F h) (φ : F →ₐ[R] S) : mulPt hs (onePt hs S) φ = φ := by
  apply pt_ext hs
  rw [mulPt_spec, onePt_spec, _root_.one_mul]

theorem mulPt_onePt' (hs : IsFinFlatSub G F h) (φ : F →ₐ[R] S) : mulPt hs φ (onePt hs S) = φ := by
  apply pt_ext hs
  rw [mulPt_spec, onePt_spec, _root_.mul_one]

end PositivityTheory.PrwZar.QiP
