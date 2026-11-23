import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtOmPHtEval
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MemPrimitiveTensorsIffIsPrimitiveElem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.KernelNoTorsion

namespace GlobalTheory.MuConst

variable (S : Scheme.{0}) (N : ℕ)

def torsPts (T : Over S) : Subgroup (T ⟶ Gm S) := (powMonoidHom N).ker

theorem mem_torsPts {T : Over S} (x : T ⟶ Gm S) : x ∈ torsPts S N T ↔ x ^ N = 1 := Iff.rfl

def torsFunctor : (Over S)ᵒᵖ ⥤ GrpCat.{0} where
  obj T := GrpCat.of (torsPts S N T.unop)
  map {T T'} f := GrpCat.ofHom
    { toFun := fun x => ⟨f.unop ≫ x.1, by
        rw [mem_torsPts, ← MonObj.comp_pow, (mem_torsPts S N x.1).1 x.2, MonObj.comp_one]⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' := fun x y => Subtype.ext (MonObj.comp_mul _ _ _) }
  map_id T := by ext x; exact Category.id_comp _
  map_comp f g := by ext x; exact Category.assoc _ _ _

def torsRep : (torsFunctor S N ⋙ forget _).RepresentableBy (torsion (Gm S) N) where
  homEquiv {T} :=
    { toFun := fun x => (⟨x ≫ torsion.ι (Gm S) N, by
        rw [mem_torsPts, ← MonObj.comp_pow, torsionι_pow, MonObj.comp_one]⟩ : torsPts S N T)
      invFun := fun y => torsionLift (y : torsPts S N T).1 (y : torsPts S N T).2
      left_inv := fun x => torsion_hom_ext (torsionLift_ι _ _)
      right_inv := fun y => Subtype.ext (torsionLift_ι _ _) }
  homEquiv_comp f x := Subtype.ext (Category.assoc _ _ _)

instance grpTors : GrpObj (torsion (Gm S) N) := GrpObj.ofRepresentableBy _ _ (torsRep S N)

theorem mul_ι {T : Over S} (x y : T ⟶ torsion (Gm S) N) :
    (x * y) ≫ torsion.ι (Gm S) N = (x ≫ torsion.ι (Gm S) N) * (y ≫ torsion.ι (Gm S) N) :=
  congrArg Subtype.val (((yonedaGrpObjIsoOfRepresentableBy _ _ (torsRep S N)).hom.app (op T)).hom.map_mul x y)

instance isCommMonObj_tors : IsCommMonObj (torsion (Gm S) N) := by
  refine (isCommMonObj_iff_isMulCommutative _).mpr fun T => ⟨⟨fun x y => ?_⟩⟩
  apply torsion_hom_ext
  rw [mul_ι, mul_ι, mul_comm]

variable [NeZero N]

abbrev cstRing : CommRingCat.{0} := CommRingCat.of (GlobalTheory.CartierDual ZU (AddMonoidAlgebra ZU (ZMod N)))

abbrev cstAff : Over (Spec ZU) := (Spec (cstRing N)).asOver (Spec ZU)

def cst : Over S := (Over.pullback (toZ S)).obj (cstAff N)

instance grpCst : GrpObj (cst S N) := Functor.grpObjObj

instance isCommMonObj_cst : IsCommMonObj (cst S N) :=
  inferInstanceAs (IsCommMonObj ((Over.pullback (toZ S)).obj (cstAff N)))

def delta (a : ZMod N) : GlobalTheory.CartierDual ZU.{0} (AddMonoidAlgebra ZU.{0} (ZMod N)) :=
  (GlobalTheory.CartierDual.addMonoidAlgebraEquiv ZU.{0} (ZMod N)).symm (Pi.single a 1)

theorem delta_mul (a b : ZMod N) : delta N a * delta N b = if a = b then delta N a else 0 := by
  unfold delta
  rw [← map_mul]
  split_ifs with h
  · subst h
    congr 1
    funext x
    simp only [Pi.mul_apply, Pi.single_apply]
    split_ifs <;> simp
  · rw [← map_zero (GlobalTheory.CartierDual.addMonoidAlgebraEquiv ZU.{0} (ZMod N)).symm]
    congr 1
    funext x
    simp only [Pi.mul_apply, Pi.single_apply, Pi.zero_apply]
    split_ifs with h1 h2 <;> simp_all

theorem sum_delta : ∑ a : ZMod N, delta N a = 1 := by
  unfold delta
  rw [← map_sum, ← map_one (GlobalTheory.CartierDual.addMonoidAlgebraEquiv ZU.{0} (ZMod N)).symm]
  congr 1
  funext x
  simp [Finset.sum_apply, Pi.single_apply]

abbrev powRing : Type :=
  AddMonoidAlgebra ZU.{0} (ULift.{0} ℤ) ⊗[ZU.{0}] GlobalTheory.CartierDual ZU.{0} (AddMonoidAlgebra ZU.{0} (ZMod N))

def powElt (k : ℤ) : powRing N :=
  ∑ a : ZMod N, AddMonoidAlgebra.single (ULift.up (k * (a.val : ℤ))) (1 : ZU.{0}) ⊗ₜ delta N a

theorem powElt_zero : powElt N 0 = 1 := by
  simp only [powElt, zero_mul]
  rw [← TensorProduct.tmul_sum, sum_delta]
  rfl

theorem powElt_add (k l : ℤ) : powElt N (k + l) = powElt N k * powElt N l := by
  simp only [powElt, Finset.sum_mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
    AddMonoidAlgebra.single_mul_single, mul_one]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun b _ hb => by rw [delta_mul, if_neg (Ne.symm hb), TensorProduct.tmul_zero])
    (fun h => (h (Finset.mem_univ a)).elim), delta_mul, if_pos rfl]
  congr 2
  ext
  simp [add_mul]

def powHom : Multiplicative (ULift.{0} ℤ) →* powRing N where
  toFun x := powElt N (Multiplicative.toAdd x).down
  map_one' := powElt_zero N
  map_mul' x y := powElt_add N _ _

def powRingHom : AddMonoidAlgebra ZU.{0} (ULift.{0} ℤ) →ₐ[ZU.{0}] powRing N :=
  AddMonoidAlgebra.lift _ _ _ (powHom N)

def powAff : splitTorusAff ZU.{0} (ULift.{0} ℤ) ⊗ cstAff N ⟶ splitTorusAff ZU.{0} (ULift.{0} ℤ) :=
  Over.homMk ((pullbackSpecIso ZU.{0} (AddMonoidAlgebra ZU.{0} (ULift.{0} ℤ))
      (GlobalTheory.CartierDual ZU.{0} (AddMonoidAlgebra ZU.{0} (ZMod N)))).hom ≫
    Spec.map (CommRingCat.ofHom (powRingHom N).toRingHom)) (by
    have h1 := pullbackSpecIso_hom_fst ZU.{0} (AddMonoidAlgebra ZU.{0} (ULift.{0} ℤ))
      (GlobalTheory.CartierDual ZU.{0} (AddMonoidAlgebra ZU.{0} (ZMod N)))
    have h2 : Spec.map (CommRingCat.ofHom (powRingHom N).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ZU.{0} (AddMonoidAlgebra ZU.{0} (ULift.{0} ℤ)))) =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := ZU.{0})
          (A := AddMonoidAlgebra ZU.{0} (ULift.{0} ℤ))
          (B := GlobalTheory.CartierDual ZU.{0} (AddMonoidAlgebra ZU.{0} (ZMod N))))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ZU.{0} (AddMonoidAlgebra ZU.{0} (ULift.{0} ℤ)))) := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext x
      change (powRingHom N) (algebraMap _ _ x) =
        (algebraMap _ _ x) ⊗ₜ[ZU.{0}] (1 : GlobalTheory.CartierDual ZU.{0} (AddMonoidAlgebra ZU.{0} (ZMod N)))
      rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
    exact (Category.assoc _ _ _).trans ((congrArg _ h2).trans ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ _) h1))))

def powS : Gm S ⊗ cst S N ⟶ Gm S :=
  (Functor.Monoidal.μIso (Over.pullback (toZ S)) (splitTorusAff ZU.{0} (ULift.{0} ℤ)) (cstAff N)).hom ≫
    (Over.pullback (toZ S)).map (powAff N)

def ev : torsion (Gm S) N ⊗ cst S N ⟶ Gm S := (torsion.ι (Gm S) N ▷ cst S N) ≫ powS S N

abbrev muCst : Over S := torsion (Gm S) N ⊗ cst S N

def pair : muCst S N ⊗ muCst S N ⟶ Gm S :=
  (lift (fst _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _) ≫ ev S N) *
    (lift (snd _ _ ≫ fst _ _) (fst _ _ ≫ snd _ _) ≫ ev S N)⁻¹

def incl : torsion (Gm S) N ⟶ muCst S N := lift (𝟙 _) (toUnit _ ≫ η[cst S N])

section Props

open GlobalTheory.HTSheaf

variable (N : ℕ)

theorem one_ι {T : Over S} : (1 : T ⟶ torsion (Gm S) N) ≫ torsion.ι (Gm S) N = 1 :=
  congrArg Subtype.val (((yonedaGrpObjIsoOfRepresentableBy _ _ (torsRep S N)).hom.app (op T)).hom.map_one)

instance isMonHom_ι : IsMonHom (torsion.ι (Gm S) N) where
  one_hom := by
    have h := one_ι S N (T := 𝟙_ (Over S))
    rwa [Hom.one_def, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp, Category.id_comp] at h
  mul_hom := by
    have h := mul_ι S N (fst (torsion (Gm S) N) (torsion (Gm S) N)) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]
    congr 1

variable [NeZero N]

theorem incl_fst : incl S N ≫ fst _ _ = 𝟙 _ := lift_fst _ _

theorem incl_snd : incl S N ≫ snd _ _ = 1 := (lift_snd _ _).trans (Hom.one_def).symm

instance isMonHom_incl : IsMonHom (incl S N) := by
  unfold incl
  infer_instance

end Props

end GlobalTheory.MuConst
