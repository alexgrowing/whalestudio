import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LieVB (omega unitSec dUnit sec sec_hom)
open GlobalTheory.CxForm (relCot dRel)
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.RelCotAb

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

def shear : A ⊗ A ⟶ A ⊗ A := lift (fst A A) ((fst A A)⁻¹ * snd A A)

def unshear : A ⊗ A ⟶ A ⊗ A := lift (fst A A) (fst A A * snd A A)

def unitPair : A ⟶ A ⊗ A := lift (𝟙 A) (toUnit A ≫ η[A])

theorem lift_id_id_left : (lift (𝟙 A) (𝟙 A)).left = pullback.diagonal A.hom :=
  pullback.hom_ext (by simp [pullback.diagonal]) (by simp [pullback.diagonal])

theorem shear_fst : shear A ≫ fst A A = fst A A := lift_fst _ _

theorem unshear_fst : unshear A ≫ fst A A = fst A A := lift_fst _ _

theorem shear_unshear : shear A ≫ unshear A = 𝟙 _ := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · simp [shear, unshear]
  · simp [shear, unshear, comp_mul, ← mul_assoc]

theorem unshear_shear : unshear A ≫ shear A = 𝟙 _ := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · simp [shear, unshear]
  · simp [shear, unshear, comp_mul, GrpObj.comp_inv, ← mul_assoc]

theorem diag_shear : lift (𝟙 A) (𝟙 A) ≫ shear A = unitPair A := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · simp [shear, unitPair]
  · simp [shear, unitPair, comp_mul, GrpObj.comp_inv, Hom.one_def]

theorem unitPair_unshear : unitPair A ≫ unshear A = lift (𝟙 A) (𝟙 A) := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · simp [unshear, unitPair]
  · simp [unshear, unitPair, comp_mul, ← Hom.one_def]

end GlobalTheory.RelCotAb

namespace GlobalTheory.RelCotAb

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

theorem unitPair_fst : (unitPair A).left ≫ pullback.fst A.hom A.hom = 𝟙 A.left :=
  congrArg Over.Hom.left (lift_fst (𝟙 A) (toUnit A ≫ η[A]))

theorem unitPair_snd : (unitPair A).left ≫ pullback.snd A.hom A.hom = A.hom ≫ unitSec A :=
  (congrArg (·.left) (lift_snd (𝟙 A) (toUnit A ≫ η[A]))).trans (by simp [unitSec, sec])

theorem shear_left_fst : (shear A).left ≫ pullback.fst A.hom A.hom = pullback.fst A.hom A.hom :=
  congrArg (·.left) (shear_fst A)

theorem unshear_left_fst : (unshear A).left ≫ pullback.fst A.hom A.hom = pullback.fst A.hom A.hom :=
  congrArg (·.left) (unshear_fst A)

theorem diag_shear_left : pullback.diagonal A.hom ≫ (shear A).left = (unitPair A).left := by
  rw [← lift_id_id_left]; exact congrArg (·.left) (diag_shear A)

theorem unitPair_unshear_left : (unitPair A).left ≫ (unshear A).left = pullback.diagonal A.hom := by
  rw [← lift_id_id_left]; exact congrArg (·.left) (unitPair_unshear A)

variable [QuasiSeparated A.hom]

instance quasiCompact_unitPair : QuasiCompact (unitPair A).left :=
  have : QuasiCompact ((unitPair A).left ≫ pullback.fst A.hom A.hom) := unitPair_fst A ▸ inferInstance
  .of_comp _ (pullback.fst A.hom A.hom)

def baseIso : (Scheme.Modules.pullback A.hom).obj (omega A) ≅ Conormal.conormal (unitPair A).left :=
  @asIso _ _ _ _ (Conormal.baseMap (unitPair_fst A) pullback.condition.symm (unitPair_snd A))
    (Conormal.isIso_baseMap (sec_hom η[A]) (unitPair_fst A) (IsPullback.of_hasPullback A.hom A.hom).flip
      (unitPair_snd A))

def shearIso : Conormal.conormal (unitPair A).left ≅ Conormal.conormal (pullback.diagonal A.hom) where
  hom := Conormal.map (pullback.diagonal_fst A.hom) (shear_left_fst A) (diag_shear_left A)
  inv := Conormal.map (unitPair_fst A) (unshear_left_fst A) (unitPair_unshear_left A)
  hom_inv_id := by
    rw [Conormal.map_comp (unitPair_fst A) _ _ _ _ _ _ (congrArg (·.left) (unshear_shear A)) (by simp) (by simp)]
    exact Conormal.map_id _ rfl _ _
  inv_hom_id := by
    rw [Conormal.map_comp (pullback.diagonal_fst A.hom) _ _ _ _ _ _ (congrArg (·.left) (shear_unshear A)) (by simp) (by simp)]
    exact Conormal.map_id _ rfl _ _

def relCotIso : (Scheme.Modules.pullback A.hom).obj (omega A) ≅ relCot A.hom := baseIso A ≪≫ shearIso A

end GlobalTheory.RelCotAb

namespace GlobalTheory.RelCotAb

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [QuasiSeparated A.hom]

abbrev divMap : pullback A.hom A.hom ⟶ A.left := (shear A).left ≫ pullback.snd A.hom A.hom

theorem relCotIso_hom_d {V : S.Opens} {W : A.left.Opens} (hU : V ≤ unitSec A ⁻¹ᵁ W) {T : A.left.Opens}
    (hT : T ≤ A.hom ⁻¹ᵁ V) {W' : (pullback A.hom A.hom).Opens} (hW' : T ≤ pullback.diagonal A.hom ⁻¹ᵁ W')
    (k : W' ≤ divMap A ⁻¹ᵁ W) (a : Γ(A.left, W)) :
    (relCotIso A).hom.app T (pullbackSections A.hom (omega A) hT (dUnit A hU a)) =
      Conormal.d (pullback.diagonal_fst A.hom) hW' ((divMap A).appLE W W' k a) := by
  have h₁ : T ≤ (unitPair A).left ⁻¹ᵁ (pullback.snd A.hom A.hom ⁻¹ᵁ W) :=
    (Conormal.le_preimage_of_comp (unitPair_snd A)).2 (hT.trans (A.hom.preimage_mono hU))
  have k' : W' ≤ (shear A).left ⁻¹ᵁ (pullback.snd A.hom A.hom ⁻¹ᵁ W) := k
  change (shearIso A).hom.app T ((baseIso A).hom.app T _) = _
  erw [Conormal.baseMap_d (sec_hom η[A]) (unitPair_fst A) pullback.condition.symm (unitPair_snd A) hU hT h₁
    le_rfl a]
  erw [Conormal.map_d (unitPair_fst A) (pullback.diagonal_fst A.hom) (shear_left_fst A) (diag_shear_left A)
    h₁ hW' k']
  exact congrArg _ (Conormal.appLE_appLE rfl _ _ _ a)

end GlobalTheory.RelCotAb

namespace GlobalTheory.RelCotAb

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

theorem lift_divMap {T : Scheme.{0}} {y₀ : T ⟶ S} (x y t : Over.mk y₀ ⟶ A) (h : x * t = y) :
    pullback.lift x.left y.left (by rw [Over.w x, Over.w y]) ≫ divMap A = t.left := by
  have e : lift x y ≫ shear A ≫ snd A A = t := by
    rw [shear, lift_snd, comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, ← h, inv_mul_cancel_left]
  exact congrArg Over.Hom.left e

variable {k : Type} [CommRing k] {p : S ⟶ Sp k} {σ : k →+* ℂ}

def pairPt (x y : CxPts (A.hom ≫ p) σ) (h : x.1 ≫ A.hom = y.1 ≫ A.hom) :
    CxPts (pullback.fst A.hom A.hom ≫ A.hom ≫ p) σ :=
  ⟨pullback.lift x.1 y.1 h, by rw [pullback.lift_fst_assoc]; exact x.2⟩

end GlobalTheory.RelCotAb
