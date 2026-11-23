import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.HopfLaurent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueRingHomOfSqZeroExtPointAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationSqZeroPointsUnitToPointStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanForms

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem sp_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (Sp A) := by
  simp only [spMap]; exact Spec.map_id _

theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

section Der
variable {R B M : Type} [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
  [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M]

def derHom (d : Derivation R B M) : B →+* TrivSqZeroExt B M where
  toFun b := TrivSqZeroExt.inl b + TrivSqZeroExt.inr (d b)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [Derivation.leibniz, op_smul_eq_smul]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

@[simp] theorem derHom_fst (d : Derivation R B M) (b : B) : (derHom d b).fst = b := by simp [derHom]
@[simp] theorem derHom_snd (d : Derivation R B M) (b : B) : (derHom d b).snd = d b := by simp [derHom]

theorem derHom_alg (d : Derivation R B M) (r : R) :
    derHom d (algebraMap R B r) = TrivSqZeroExt.inl (algebraMap R B r) := by
  ext <;> simp

def derOf (c : B →+* TrivSqZeroExt B M) (h1 : ∀ b, (c b).fst = b)
    (h2 : ∀ r, c (algebraMap R B r) = TrivSqZeroExt.inl (algebraMap R B r)) : Derivation R B M where
  toFun b := (c b).snd
  map_add' a b := by
    show (c (a + b)).snd = (c a).snd + (c b).snd
    rw [map_add]; rfl
  map_smul' r b := by
    simp only [RingHom.id_apply, Algebra.smul_def, map_mul, h2, TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.snd_inl, op_smul_eq_smul, smul_zero, add_zero]
    rw [algebraMap_smul]
  map_one_eq_zero' := by simp
  leibniz' a b := by
    show (c (a * b)).snd = a • (c b).snd + b • (c a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, h1, h1, op_smul_eq_smul]

theorem derHom_derOf (c : B →+* TrivSqZeroExt B M) (h1 : ∀ b, (c b).fst = b)
    (h2 : ∀ r, c (algebraMap R B r) = TrivSqZeroExt.inl (algebraMap R B r)) : derHom (derOf c h1 h2) = c := by
  ext b
  · simp [h1]
  · simp [derOf]

end Der

section Sum
variable {B M B' M' : Type} [CommRing B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M]
  [CommRing B'] [AddCommGroup M'] [Module B' M'] [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M']

def sumHom (α : B →+* B') (f : M →+ M') (hf : ∀ (b : B) (m : M), f (b • m) = α b • f m) :
    TrivSqZeroExt B M →+* TrivSqZeroExt B' M' where
  toFun x := TrivSqZeroExt.inl (α x.fst) + TrivSqZeroExt.inr (f x.snd)
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext
    · simp
    · simp [hf, op_smul_eq_smul]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

theorem sumHom_isSum (α : B →+* B') (f : M →+ M') (hf : ∀ (b : B) (m : M), f (b • m) = α b • f m) :
    IsSum (sumHom α f hf) α f :=
  ⟨fun b ↦ by ext <;> simp [sumHom], fun m ↦ by ext <;> simp [sumHom]⟩

@[simp] theorem sumHom_fst (α : B →+* B') (f : M →+ M') (hf : ∀ (b : B) (m : M), f (b • m) = α b • f m)
    (x : TrivSqZeroExt B M) : (sumHom α f hf x).fst = α x.fst := by simp [sumHom]

@[simp] theorem sumHom_snd (α : B →+* B') (f : M →+ M') (hf : ∀ (b : B) (m : M), f (b • m) = α b • f m)
    (x : TrivSqZeroExt B M) : (sumHom α f hf x).snd = f x.snd := by simp [sumHom]

end Sum

@[reducible] def opMod (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] : Module Bᵐᵒᵖ M :=
  Module.compHom _ ((RingHom.id B).fromOpposite mul_comm)

section Main
variable {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]

abbrev TrTy : Type 1 := ∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M]
  [IsCentralScalar B M], (Sp B ⟶ A.left) → (Sp (TrivSqZeroExt B M) ⟶ A.left) → (Sp (TrivSqZeroExt B M) ⟶ A.left)

def TrBij (τ : TrTy A) : Prop := ∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
  [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (P : Sp B ⟶ A.left), P ≫ A.hom = spMap (algebraMap R B) →
  Set.BijOn (τ B M P) {z | Lifts A.hom (unitPt A B) z} {z | Lifts A.hom P z}

def TrNat (τ : TrTy A) : Prop := ∀ (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M]
  [Module Bᵐᵒᵖ M] [IsCentralScalar B M] (B' M' : Type) [CommRing B'] [Algebra R B'] [AddCommGroup M'] [Module B' M']
  [Module B'ᵐᵒᵖ M'] [IsCentralScalar B' M'] (α : B →ₐ[R] B') (f : M → M') (β : TrivSqZeroExt B M →+* TrivSqZeroExt B' M'),
  IsSum β α f → ∀ (P : Sp B ⟶ A.left), P ≫ A.hom = spMap (algebraMap R B) → ∀ z, Lifts A.hom (unitPt A B) z →
  Lifts A.hom (unitPt A B') (spMap β ≫ z) ∧ τ B' M' (spMap (α : B →+* B') ≫ P) (spMap β ≫ z) = spMap β ≫ τ B M P z

variable (U : A.left.affineOpens) {M : Type} [AddCommGroup M] [Module (Sec A.hom U.1) M]
  [Module (Sec A.hom U.1)ᵐᵒᵖ M] [IsCentralScalar (Sec A.hom U.1) M] [Module R M] [IsScalarTower R (Sec A.hom U.1) M]

def pt (d : Derivation R (Sec A.hom U.1) M) : Sp (TrivSqZeroExt (Sec A.hom U.1) M) ⟶ A.left :=
  spMap (derHom d) ≫ affPt A.hom U

theorem pt_lifts (d : Derivation R (Sec A.hom U.1) M) : Lifts A.hom (affPt A.hom U) (pt A U d) := by
  constructor
  · rw [pt, Category.assoc, affPt_w, sp_comp]
    congr 1
    refine RingHom.ext fun r ↦ ?_
    simp only [RingHom.comp_apply, derHom_alg]; rfl
  · rw [pt, ← Category.assoc, sp_comp]
    have : (TrivSqZeroExt.fstHom (Sec A.hom U.1) (Sec A.hom U.1) M).toRingHom.comp (derHom d) = RingHom.id _ := by
      ext b; simp
    rw [this, sp_id, Category.id_comp]

theorem lifts_pt (z : Sp (TrivSqZeroExt (Sec A.hom U.1) M) ⟶ A.left) (hz : Lifts A.hom (affPt A.hom U) z) :
    ∃ d : Derivation R (Sec A.hom U.1) M, pt A U d = z := by
  obtain ⟨c, ⟨hc1, hc2⟩, -⟩ := GlobalTheory.T.existsUnique_ringHom_of_sqZeroExt_point_affine R A.left A.hom U (Sec A.hom U.1) M (RingHom.id _) z
    (by rw [sp_id, Category.id_comp]; exact hz.2)
  have h2 : c.comp (algebraMap R (Sec A.hom U.1)) =
      (TrivSqZeroExt.inlHom (Sec A.hom U.1) M).comp (algebraMap R (Sec A.hom U.1)) := by
    apply sp_inj
    rw [← sp_comp, ← affPt_w, ← Category.assoc, hc1]
    exact hz.1
  have hc2' : ∀ b, (c b).fst = b := hc2
  have h2' : ∀ r, c (algebraMap R (Sec A.hom U.1) r) = TrivSqZeroExt.inl (algebraMap R (Sec A.hom U.1) r) :=
    fun r ↦ RingHom.congr_fun h2 r
  refine ⟨derOf c hc2' h2', ?_⟩
  rw [pt, derHom_derOf, hc1]

theorem pt_inj (d d' : Derivation R (Sec A.hom U.1) M) (h : pt A U d = pt A U d') : d = d' := by
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.existsUnique_ringHom_of_sqZeroExt_point_affine R A.left A.hom U (Sec A.hom U.1) M (RingHom.id _) (pt A U d)
    (by rw [sp_id, Category.id_comp]; exact (pt_lifts A U d).2)
  have e1 := hc (derHom d) ⟨rfl, fun b ↦ derHom_fst d b⟩
  have e2 := hc (derHom d') ⟨h.symm, fun b ↦ derHom_fst d' b⟩
  ext b
  have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun (e1.trans e2.symm) b)
  simpa using this

variable (τ : TrTy A)

def back (y : Sp (TrivSqZeroExt (Sec A.hom U.1) M) ⟶ A.left) : Sp (TrivSqZeroExt (Sec A.hom U.1) M) ⟶ A.left :=
  @Function.invFunOn _ _ ⟨y⟩ (τ (Sec A.hom U.1) M (affPt A.hom U)) {z | Lifts A.hom (unitPt A (Sec A.hom U.1)) z} y

variable {A τ}

theorem back_spec (hb : TrBij A τ) (y : Sp (TrivSqZeroExt (Sec A.hom U.1) M) ⟶ A.left)
    (hy : Lifts A.hom (affPt A.hom U) y) :
    Lifts A.hom (unitPt A (Sec A.hom U.1)) (back A U τ y) ∧ τ (Sec A.hom U.1) M (affPt A.hom U) (back A U τ y) = y := by
  haveI : Nonempty (Sp (TrivSqZeroExt (Sec A.hom U.1) M) ⟶ A.left) := ⟨y⟩
  have h := (hb (Sec A.hom U.1) M (affPt A.hom U) (affPt_w A.hom U)).surjOn hy
  exact ⟨Function.invFunOn_mem h, Function.invFunOn_eq h⟩

theorem back_eq (hb : TrBij A τ) (z : Sp (TrivSqZeroExt (Sec A.hom U.1) M) ⟶ A.left)
    (hz : Lifts A.hom (unitPt A (Sec A.hom U.1)) z) (y : Sp (TrivSqZeroExt (Sec A.hom U.1) M) ⟶ A.left)
    (h : τ (Sec A.hom U.1) M (affPt A.hom U) z = y) : back A U τ y = z := by
  have H := hb (Sec A.hom U.1) M (affPt A.hom U) (affPt_w A.hom U)
  have hy : Lifts A.hom (affPt A.hom U) y := h ▸ H.mapsTo hz
  exact H.injOn (back_spec U hb y hy).1 hz ((back_spec U hb y hy).2.trans h.symm)

end Main

section Forms
variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {W : Type} [AddCommGroup W] [Module R W]

def eU (tr : TanRep A W) (τ : TrTy A) (U : A.left.affineOpens) : W →ₗ[R] Ω[Sec A.hom U.1⁄R] :=
  letI := opMod (Sec A.hom U.1) Ω[Sec A.hom U.1⁄R]
  haveI : IsCentralScalar (Sec A.hom U.1) Ω[Sec A.hom U.1⁄R] := ⟨fun _ _ ↦ rfl⟩
  tr.Φ (back A U τ (pt A U (D R (Sec A.hom U.1))))

variable (tr : TanRep A W) {τ : TrTy A} (hb : TrBij A τ) (hn : TrNat A τ) (U : A.left.affineOpens)
  {M : Type} [AddCommGroup M] [Module (Sec A.hom U.1) M] [Module (Sec A.hom U.1)ᵐᵒᵖ M]
  [IsCentralScalar (Sec A.hom U.1) M] [Module R M] [IsScalarTower R (Sec A.hom U.1) M]
include hb hn

theorem key (ψ : Ω[Sec A.hom U.1⁄R] →ₗ[Sec A.hom U.1] M) :
    tr.Φ (back A U τ (pt A U (ψ.compDer (D R (Sec A.hom U.1))))) = (ψ.restrictScalars R) ∘ₗ eU tr τ U := by
  letI := opMod (Sec A.hom U.1) Ω[Sec A.hom U.1⁄R]
  haveI : IsCentralScalar (Sec A.hom U.1) Ω[Sec A.hom U.1⁄R] := ⟨fun _ _ ↦ rfl⟩
  obtain ⟨hz0, hτz0⟩ := back_spec (τ := τ) U hb (pt A U (D R (Sec A.hom U.1))) (pt_lifts A U _)
  let β := sumHom (RingHom.id (Sec A.hom U.1)) ψ.toAddMonoidHom (fun b m ↦ ψ.map_smul b m)
  have hβ : IsSum β (AlgHom.id R (Sec A.hom U.1)) ψ :=
    sumHom_isSum (RingHom.id (Sec A.hom U.1)) ψ.toAddMonoidHom (fun b m ↦ ψ.map_smul b m)
  obtain ⟨hl, hnat⟩ := hn (Sec A.hom U.1) Ω[Sec A.hom U.1⁄R] (Sec A.hom U.1) M (AlgHom.id R _) ψ β hβ
    (affPt A.hom U) (affPt_w A.hom U) _ hz0
  have hpt : spMap β ≫ pt A U (D R (Sec A.hom U.1)) = pt A U (ψ.compDer (D R (Sec A.hom U.1))) := by
    rw [pt, pt, ← Category.assoc, sp_comp]
    congr 2
    refine RingHom.ext fun b ↦ ?_
    rw [RingHom.comp_apply, show derHom (D R (Sec A.hom U.1)) b =
      TrivSqZeroExt.inl b + TrivSqZeroExt.inr (D R (Sec A.hom U.1) b) from rfl, map_add, hβ.1, hβ.2]
    rfl
  have hb' : back A U τ (pt A U (ψ.compDer (D R (Sec A.hom U.1)))) =
      spMap β ≫ back A U τ (pt A U (D R (Sec A.hom U.1))) := by
    apply back_eq U hb _ hl
    have hid : spMap ((AlgHom.id R (Sec A.hom U.1) : Sec A.hom U.1 →+* Sec A.hom U.1)) ≫ affPt A.hom U =
        affPt A.hom U := by
      rw [show ((AlgHom.id R (Sec A.hom U.1) : Sec A.hom U.1 →+* Sec A.hom U.1)) = RingHom.id _ from rfl, sp_id,
        Category.id_comp]
    rw [hid] at hnat
    rw [hnat, hτz0, hpt]
  rw [hb']
  exact tr.nat (AlgHom.id R _) (ψ.restrictScalars R) β hβ _ hz0

theorem exists_lift (g : W →ₗ[R] M) :
    ∃ ψ : Ω[Sec A.hom U.1⁄R] →ₗ[Sec A.hom U.1] M, (ψ.restrictScalars R) ∘ₗ eU tr τ U = g := by
  obtain ⟨z, ⟨hz, hzg⟩, -⟩ := tr.bij (B := Sec A.hom U.1) (M := M) g
  have hy := (hb (Sec A.hom U.1) M (affPt A.hom U) (affPt_w A.hom U)).mapsTo hz
  obtain ⟨d, hd⟩ := lifts_pt A U _ hy
  refine ⟨d.liftKaehlerDifferential, ?_⟩
  rw [← key tr hb hn U, Derivation.liftKaehlerDifferential_comp, hd, back_eq U hb z hz _ rfl, hzg]

theorem lift_unique (ψ ψ' : Ω[Sec A.hom U.1⁄R] →ₗ[Sec A.hom U.1] M)
    (h : (ψ.restrictScalars R) ∘ₗ eU tr τ U = (ψ'.restrictScalars R) ∘ₗ eU tr τ U) : ψ = ψ' := by
  rw [← key tr hb hn U, ← key tr hb hn U] at h
  have s1 := back_spec U hb _ (pt_lifts A U (ψ.compDer (D R (Sec A.hom U.1))))
  have s2 := back_spec U hb _ (pt_lifts A U (ψ'.compDer (D R (Sec A.hom U.1))))
  obtain ⟨_, _, hu⟩ := tr.bij (B := Sec A.hom U.1) (M := M)
    (tr.Φ (back A U τ (pt A U (ψ.compDer (D R (Sec A.hom U.1))))))
  have e := (hu _ ⟨s1.1, rfl⟩).trans (hu _ ⟨s2.1, h.symm⟩).symm
  have e' : pt A U (ψ.compDer (D R (Sec A.hom U.1))) = pt A U (ψ'.compDer (D R (Sec A.hom U.1))) := by
    rw [← s1.2, ← s2.2, e]
  exact Derivation.liftKaehlerDifferential_unique _ _ (pt_inj A U _ _ e')

theorem eU_isBaseChange : IsBaseChange (Sec A.hom U.1) (eU tr τ U) := by
  refine IsBaseChange.of_lift_unique _ fun Q _ _ _ _ g ↦ ?_
  letI : AddCommGroup Q := Module.addCommMonoidToAddCommGroup (Sec A.hom U.1)
  letI := opMod (Sec A.hom U.1) Q
  haveI : IsCentralScalar (Sec A.hom U.1) Q := ⟨fun _ _ ↦ rfl⟩
  obtain ⟨ψ, hψ⟩ := exists_lift tr hb hn U g
  exact ⟨ψ, hψ, fun ψ' h ↦ lift_unique tr hb hn U ψ' ψ (h.trans hψ.symm)⟩

theorem eU_nat {T T' : AffOp A.left} (a : T ⟶ T') (w : W) :
    eU tr τ T'.unop w = p1 (OAff A.hom) a (eU tr τ T.unop w) := by
  letI := opMod (Sec A.hom T.unop.1) Ω[Sec A.hom T.unop.1⁄R]
  haveI : IsCentralScalar (Sec A.hom T.unop.1) Ω[Sec A.hom T.unop.1⁄R] := ⟨fun _ _ ↦ rfl⟩
  letI := opMod (Sec A.hom T'.unop.1) Ω[Sec A.hom T'.unop.1⁄R]
  haveI : IsCentralScalar (Sec A.hom T'.unop.1) Ω[Sec A.hom T'.unop.1⁄R] := ⟨fun _ _ ↦ rfl⟩
  have hle : T'.unop.1 ≤ T.unop.1 := leOfHom a.unop
  let α : Sec A.hom T.unop.1 →ₐ[R] Sec A.hom T'.unop.1 := Sec.res A.hom hle
  let f : Ω[Sec A.hom T.unop.1⁄R] →ₗ[R] Ω[Sec A.hom T'.unop.1⁄R] := p1 (OAff A.hom) a
  have hf : ∀ (b : Sec A.hom T.unop.1) (m : Ω[Sec A.hom T.unop.1⁄R]), f.toAddMonoidHom (b • m) =
      (α : Sec A.hom T.unop.1 →+* Sec A.hom T'.unop.1) b • f.toAddMonoidHom m :=
    fun b m ↦ oneFormsMapOfFunctorMorphism_smul (OAff A.hom) a b m
  have hfD : ∀ b : Sec A.hom T.unop.1, f (D R _ b) = D R _ (α b) := fun b ↦ p1_D (OAff A.hom) a b
  let β := sumHom (α : Sec A.hom T.unop.1 →+* Sec A.hom T'.unop.1) f.toAddMonoidHom hf
  have hβ : IsSum β α f := sumHom_isSum _ f.toAddMonoidHom hf
  obtain ⟨hz0, hτz0⟩ := back_spec (τ := τ) T.unop hb (pt A T.unop (D R (Sec A.hom T.unop.1))) (pt_lifts A T.unop _)
  obtain ⟨hl, hnat⟩ := hn (Sec A.hom T.unop.1) Ω[Sec A.hom T.unop.1⁄R] (Sec A.hom T'.unop.1)
    Ω[Sec A.hom T'.unop.1⁄R] α f β hβ (affPt A.hom T.unop) (affPt_w A.hom T.unop) _ hz0
  have hres : spMap (α : Sec A.hom T.unop.1 →+* Sec A.hom T'.unop.1) ≫ affPt A.hom T.unop = affPt A.hom T'.unop :=
    affPt_res A.hom hle
  have hpt : spMap β ≫ pt A T.unop (D R (Sec A.hom T.unop.1)) = pt A T'.unop (D R (Sec A.hom T'.unop.1)) := by
    have hc : β.comp (derHom (D R (Sec A.hom T.unop.1))) =
        (derHom (D R (Sec A.hom T'.unop.1))).comp (α : Sec A.hom T.unop.1 →+* Sec A.hom T'.unop.1) := by
      refine RingHom.ext fun b ↦ ?_
      rw [RingHom.comp_apply, show derHom (D R (Sec A.hom T.unop.1)) b =
        TrivSqZeroExt.inl b + TrivSqZeroExt.inr (D R (Sec A.hom T.unop.1) b) from rfl, map_add, hβ.1, hβ.2, hfD]
      rfl
    rw [pt, pt, ← Category.assoc, sp_comp, hc, ← sp_comp, Category.assoc, hres]
  rw [hres] at hnat
  have hb' : back A T'.unop τ (pt A T'.unop (D R (Sec A.hom T'.unop.1))) =
      spMap β ≫ back A T.unop τ (pt A T.unop (D R (Sec A.hom T.unop.1))) := by
    apply back_eq T'.unop hb _ hl
    rw [hnat, hτz0, hpt]
  show tr.Φ (back A T'.unop τ (pt A T'.unop (D R (Sec A.hom T'.unop.1)))) w =
    f (tr.Φ (back A T.unop τ (pt A T.unop (D R (Sec A.hom T.unop.1)))) w)
  rw [hb', tr.nat α f β hβ _ hz0]
  rfl

end Forms

theorem exists_globForm_isBaseChange : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], ∀ (W : Type)
    [AddCommGroup W] [Module R W], TanRep A W → ∃ j : W →ₗ[R] GlobForm A.hom, ∀ T : AffOp A.left,
    ∃ e : W →ₗ[R] Ω[(OAff A.hom).obj T⁄R], (∀ w, e w = (j w).1 T) ∧ IsBaseChange ((OAff A.hom).obj T) e := by
  intro R _ A _ W _ _ tr
  obtain ⟨τ, hb, hn⟩ := GlobalTheory.T.exists_translation_sqZeroPoints_unit_to_point R A
  let j : W →ₗ[R] GlobForm A.hom :=
    { toFun := fun w ↦ ⟨fun T ↦ eU tr τ T.unop w, fun T T' a ↦ eU_nat tr hb hn a w⟩
      map_add' := fun w w' ↦ Subtype.ext (funext fun T ↦ map_add (eU tr τ T.unop) w w')
      map_smul' := fun r w ↦ Subtype.ext (funext fun T ↦ map_smul (eU tr τ T.unop) r w) }
  exact ⟨j, fun T ↦ ⟨eU tr τ T.unop, fun w ↦ rfl, eU_isBaseChange tr hb hn T.unop⟩⟩

end GlobalTheory.TanForms
