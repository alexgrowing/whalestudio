import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.HopfLaurent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecTrivSqZeroExtIsPushoutStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqZeroPointOfCotangentLinearMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentFormOfSqZeroPointLinearNaturalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqZeroPointEqOfCotangentFormEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupScheStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCotangentFrameSmoothGroupSchemeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TanRepr

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap]
  rw [← Spec.map_comp]
  rfl

variable {R : Type} [CommRing R]

section Base

variable (R) (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

def baseMap : TrivSqZeroExt R M →+* TrivSqZeroExt B M where
  toFun x := ((algebraMap R B x.fst, x.snd) : TrivSqZeroExt B M)
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext
    · change algebraMap R B (x * y).fst = algebraMap R B x.fst * algebraMap R B y.fst
      rw [TrivSqZeroExt.fst_mul, map_mul]
    · change (x * y).snd = (algebraMap R B x.fst) • y.snd + MulOpposite.op (algebraMap R B y.fst) • x.snd
      rw [TrivSqZeroExt.snd_mul, op_smul_eq_smul, op_smul_eq_smul, algebraMap_smul, algebraMap_smul]
  map_zero' := by ext <;> simp
  map_add' x y := by
    ext
    · change algebraMap R B (x + y).fst = algebraMap R B x.fst + algebraMap R B y.fst
      rw [TrivSqZeroExt.fst_add, map_add]
    · rfl

theorem baseMap_isSum : IsSum (baseMap R B M) (algebraMap R B) id :=
  ⟨fun _ => rfl, fun _ => TrivSqZeroExt.ext (by change algebraMap R B 0 = 0; simp) rfl⟩

end Base

open GlobalTheory.SqZeroPt

section Pts

variable (A : Over (Sp R)) [GrpObj A]
variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

theorem fst_comp_baseMap : (TrivSqZeroExt.fstHom B B M).toRingHom.comp (baseMap R B M) =
    (algebraMap R B).comp (TrivSqZeroExt.fstHom R R M).toRingHom := by
  ext x; rfl

theorem baseMap_comp_algebraMap : (baseMap R B M).comp (algebraMap R (TrivSqZeroExt R M)) =
    (TrivSqZeroExt.inlHom B M).comp (algebraMap R B) := by
  refine RingHom.ext fun x => ?_
  rw [RingHom.comp_apply, TrivSqZeroExt.algebraMap_eq_inl, (baseMap_isSum R B M).1]
  rfl

theorem unit_w : (show Sp R ⟶ A.left from η[A].left) ≫ A.hom = 𝟙 (Sp R) := by
  have := Over.w η[A]
  simpa using this

theorem fst_baseMap_left (v : TM R M ⟶ A) (h : zeroSec R M ≫ v = η[A]) :
    spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ spMap (baseMap R B M) ≫ v.left =
      spMap (algebraMap R B) ≫ (show Sp R ⟶ A.left from η[A].left) := by
  rw [← Category.assoc, spMap_comp', fst_comp_baseMap, ← spMap_comp', Category.assoc]
  congr 1
  exact congrArg Over.Hom.left h

theorem left_eq (v₁ v₂ : TM R M ⟶ A) (h₁ : zeroSec R M ≫ v₁ = η[A]) (h₂ : zeroSec R M ≫ v₂ = η[A])
    (e : spMap (baseMap R B M) ≫ v₁.left = spMap (baseMap R B M) ≫ v₂.left) : v₁ = v₂ := by
  obtain ⟨z₀, _, hu⟩ := GlobalTheory.T.spec_trivSqZeroExt_isPushout R B M (baseMap R B M) (baseMap_isSum R B M) A.left
    (show Sp R ⟶ A.left from η[A].left) (spMap (baseMap R B M) ≫ v₁.left) (fst_baseMap_left A v₁ h₁)
  have a₁ := hu v₁.left ⟨congrArg Over.Hom.left h₁, rfl⟩
  have a₂ := hu v₂.left ⟨congrArg Over.Hom.left h₂, e.symm⟩
  exact Over.OverMorphism.ext (a₁.trans a₂.symm)

theorem lifts_baseMap (v : TM R M ⟶ A) (h : zeroSec R M ≫ v = η[A]) :
    Lifts A.hom (unitPt A B) (spMap (baseMap R B M) ≫ v.left) := by
  refine ⟨?_, fst_baseMap_left A v h⟩
  rw [Category.assoc, Over.w v]
  change spMap (baseMap R B M) ≫ spMap (algebraMap R (TrivSqZeroExt R M)) = _
  rw [spMap_comp', baseMap_comp_algebraMap]

theorem exists_of_lifts (z : Sp (TrivSqZeroExt B M) ⟶ A.left) (hz : Lifts A.hom (unitPt A B) z) :
    ∃ (v : TM R M ⟶ A) (_ : zeroSec R M ≫ v = η[A]), spMap (baseMap R B M) ≫ v.left = z := by
  obtain ⟨h₁, h₂⟩ := hz
  obtain ⟨z₀, ⟨a₁, a₂⟩, -⟩ := GlobalTheory.T.spec_trivSqZeroExt_isPushout R B M (baseMap R B M) (baseMap_isSum R B M) A.left
    (show Sp R ⟶ A.left from η[A].left) z h₂
  have hb : spMap (TrivSqZeroExt.fstHom B B M).toRingHom ≫ z ≫ A.hom =
      spMap (algebraMap R B) ≫ 𝟙 (Sp R) := by
    rw [← Category.assoc, h₂, unitPt, Category.assoc, unit_w]
  obtain ⟨y, -, hu⟩ := GlobalTheory.T.spec_trivSqZeroExt_isPushout R B M (baseMap R B M) (baseMap_isSum R B M) (Sp R)
    (𝟙 (Sp R)) (z ≫ A.hom) hb
  have e₁ := hu (z₀ ≫ A.hom) ⟨by rw [← Category.assoc, a₁, unit_w], by rw [← Category.assoc, a₂]⟩
  have e₂ := hu (spMap (algebraMap R (TrivSqZeroExt R M))) ⟨by
      rw [spMap_comp']
      have : (TrivSqZeroExt.fstHom R R M).toRingHom.comp (algebraMap R (TrivSqZeroExt R M)) =
          RingHom.id R := by ext x; rfl
      rw [this]; simp only [spMap]; first | (rw [CommRingCat.ofHom_id, Spec.map_id]) | simp, by
      rw [spMap_comp', baseMap_comp_algebraMap, h₁]⟩
  refine ⟨Over.homMk z₀ (e₁.trans e₂.symm), Over.OverMorphism.ext a₁, a₂⟩

def phiLin (v : TM R M ⟶ A) (h : zeroSec R M ≫ v = η[A]) : Wmod A →ₗ[R] M where
  toFun := Phi v h
  map_add' := map_add _
  map_smul' r w := (GlobalTheory.T.cotangentFormOfSqZeroPoint_linear_natural R A M v h).1 r w

theorem phiLin_congr {v₁ v₂ : TM R M ⟶ A} (h₁ : zeroSec R M ≫ v₁ = η[A])
    (h₂ : zeroSec R M ≫ v₂ = η[A]) (e : v₁ = v₂) : phiLin A v₁ h₁ = phiLin A v₂ h₂ := by
  subst e; rfl

open Classical in

def phiOf (z : Sp (TrivSqZeroExt B M) ⟶ A.left) : Wmod A →ₗ[R] M :=
  if hz : ∃ (v : TM R M ⟶ A) (_ : zeroSec R M ≫ v = η[A]), spMap (baseMap R B M) ≫ v.left = z then
    phiLin A hz.choose hz.choose_spec.choose
  else 0

theorem phiOf_eq (v : TM R M ⟶ A) (h : zeroSec R M ≫ v = η[A]) :
    phiOf A (spMap (baseMap R B M) ≫ v.left) = phiLin A v h := by
  have hz : ∃ (v' : TM R M ⟶ A) (_ : zeroSec R M ≫ v' = η[A]),
      spMap (baseMap R B M) ≫ v'.left = spMap (baseMap R B M) ≫ v.left := ⟨v, h, rfl⟩
  rw [phiOf, dif_pos hz]
  exact phiLin_congr A _ _ (left_eq A _ _ hz.choose_spec.choose h hz.choose_spec.choose_spec)

theorem cotangentAtUnit_tangentBijection (hq : (GlobalTheory.LieVB.omega A).IsQuasicoherent) (l : Wmod A →ₗ[R] M) :
    ∃! z : Sp (TrivSqZeroExt B M) ⟶ A.left, Lifts A.hom (unitPt A B) z ∧ phiOf A z = l := by
  obtain ⟨v, h, hv⟩ := GlobalTheory.T.exists_sqZeroPoint_of_cotangent_linearMap R A hq M l
  refine ⟨spMap (baseMap R B M) ≫ v.left, ⟨lifts_baseMap A v h,
    (phiOf_eq A v h).trans (LinearMap.ext hv)⟩, fun z' ⟨hl, hp⟩ => ?_⟩
  obtain ⟨v', h', rfl⟩ := exists_of_lifts A z' hl
  rw [phiOf_eq A v' h'] at hp
  have e : v' = v := GlobalTheory.T.sqZeroPoint_eq_of_cotangentForm_eq R A hq M v' v h' h fun w => by
    change phiLin A v' h' w = _
    rw [hp, hv]
  rw [e]

end Pts

section Nat

variable (A : Over (Sp R)) [GrpObj A]
variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
variable {B' M' : Type} [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M']
  [IsCentralScalar B' M'] [Module R M'] [IsScalarTower R B' M'] [Module Rᵐᵒᵖ M'] [IsCentralScalar R M']

theorem cotangentAtUnit_tangentBijection_naturality (α : B →ₐ[R] B') (f : M →ₗ[R] M') (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M')
    (hβ : IsSum β α f) (z : Sp (TrivSqZeroExt B M) ⟶ A.left) (hz : Lifts A.hom (unitPt A B) z) :
    phiOf A (spMap β ≫ z) = f ∘ₗ phiOf A z := by
  obtain ⟨v, h, rfl⟩ := exists_of_lifts A z hz
  let g : TrivSqZeroExt R M →+* TrivSqZeroExt R M' := (TrivSqZeroExt.map f).toRingHom
  have hg : IsSum g id f := ⟨fun r => TrivSqZeroExt.map_inl f r, fun m => TrivSqZeroExt.map_inr f m⟩
  have hw : (spMap g ≫ v.left) ≫ A.hom = (TM R M').hom := by
    rw [Category.assoc, Over.w v]
    change spMap g ≫ spMap (algebraMap R (TrivSqZeroExt R M)) = spMap (algebraMap R (TrivSqZeroExt R M'))
    rw [spMap_comp']
    exact congrArg spMap (TrivSqZeroExt.map f).comp_algebraMap
  let v' : TM R M' ⟶ A := Over.homMk (spMap g ≫ v.left) hw
  have h' : zeroSec R M' ≫ v' = η[A] := by
    apply Over.OverMorphism.ext
    change spMap (TrivSqZeroExt.fstHom R R M').toRingHom ≫ spMap g ≫ v.left = η[A].left
    rw [← Category.assoc, spMap_comp']
    have : (TrivSqZeroExt.fstHom R R M').toRingHom.comp g = (TrivSqZeroExt.fstHom R R M).toRingHom := by
      ext x; simp [g]
    rw [this]
    exact congrArg Over.Hom.left h
  have hc : (baseMap R B' M').comp g = β.comp (baseMap R B M) := by
    refine RingHom.ext fun x => ?_
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
    simp only [RingHom.comp_apply, map_add, hg.1, hg.2, (baseMap_isSum R B M).1, (baseMap_isSum R B M).2,
      (baseMap_isSum R B' M').1, (baseMap_isSum R B' M').2, hβ.1, hβ.2, id, AlgHom.commutes]
  have e : spMap β ≫ spMap (baseMap R B M) ≫ v.left = spMap (baseMap R B' M') ≫ v'.left := by
    change _ = spMap (baseMap R B' M') ≫ spMap g ≫ v.left
    rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', hc]
  rw [e, phiOf_eq A v' h', phiOf_eq A v h]
  ext w
  exact (GlobalTheory.T.cotangentFormOfSqZeroPoint_linear_natural R A M v h).2 M' f g hg v' h' rfl w

end Nat

def tanRep (A : Over (Sp R)) [GrpObj A] (hq : (GlobalTheory.LieVB.omega A).IsQuasicoherent) :
    TanRep A (Wmod A) where
  Φ := @fun B M _ _ _ _ _ _ _ _ z =>
    letI := opModule R M; haveI := opModule_central R M; phiOf A z
  bij := @fun B M _ _ _ _ _ _ _ _ l => by
    letI := opModule R M; haveI := opModule_central R M
    exact cotangentAtUnit_tangentBijection A hq l
  nat := @fun B M _ _ _ _ _ _ _ _ B' M' _ _ _ _ _ _ _ _ α f β hβ z hz => by
    letI := opModule R M; haveI := opModule_central R M
    letI := opModule R M'; haveI := opModule_central R M'
    exact cotangentAtUnit_tangentBijection_naturality A α f β hβ z hz

theorem exists_tanRep : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], Smooth A.hom →
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module R W), Module.Finite R W ∧ Module.Projective R W ∧
      Nonempty (TanRep A W) := by
  intro R _ A _ hs
  haveI := hs
  have hfr := GlobalTheory.T.exists_cotangent_frame_smooth_groupScheme R A
  have hq : (GlobalTheory.LieVB.omega A).IsQuasicoherent := GlobalTheory.OmegaGlobal.isQuasicoherent_of_frames hfr
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.finite_projective_cotangentGlobalSections_groupScheme R A hfr
  exact ⟨Wmod A, inferInstance, inferInstance, hfin, hproj, ⟨tanRep A hq⟩⟩

end GlobalTheory.TanRepr
