import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveCohomologySheaves
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.CechFunctor

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Topology

universe w' u

namespace GroundTheory.Arith.SchemeCoh

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

section Scalars

variable [IsIntegral X]

lemma sectionValue_restrictTop (V : X.Opens) (y : V) (r : Γ(X, ⊤)) :
    sectionValue V y (restrictTop V r) = X.germToFunctionField ⊤ r := by
  rw [restrictTop, sectionValue_res le_top y r, sectionValue_eq]

lemma sectionValue_scalar (V : X.Opens) (y : V) (c : k) :
    sectionValue V y (restrictTop V (scalarRingHom X c)) = algebraMap k X.functionField c := by
  rw [sectionValue_restrictTop, algebraMap_functionField]

variable [IsLocallyNoetherian X] [IsNormalScheme X]

lemma PrimeDivisor.valuation_algebraMap_scalar_le_one (Z : PrimeDivisor X) (c : k) :
    Z.valuation (algebraMap k X.functionField c) ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply k (X.presheaf.stalk Z.point) X.functionField]
  exact Z.valuation_algebraMap_le_one _

lemma mul_mem_pointSubgroup (D : WeilDivisor X) (x : X) (c : k) {f : X.functionField}
    (hf : f ∈ pointSubgroup D x) : algebraMap k X.functionField c * f ∈ pointSubgroup D x := by
  rw [mem_pointSubgroup_iff] at hf ⊢
  intro h
  rw [map_mul]
  calc _ ≤ 1 * WithZero.exp (D (PrimeDivisor.ofPoint x h)) :=
        mul_le_mul' ((PrimeDivisor.ofPoint x h).valuation_algebraMap_scalar_le_one c) (hf h)
    _ = _ := one_mul _

end Scalars

section Endo

variable [IsIntegral X]

lemma mul_mem_constSections (c : k) {V : X.Opens} (t : constSections V) :
    (fun y => algebraMap k X.functionField c * t.1 y) ∈ constSections V := by
  intro y
  obtain ⟨W, hyW, h⟩ := t.2 y
  exact ⟨W, hyW, fun z hz => by simp only [h z hz]⟩

noncomputable def constSmul (c : k) : constSheaf X ⟶ constSheaf X :=
  ⟨{ app := fun _ => AddCommGrpCat.ofHom
        { toFun := fun t => ⟨fun y => algebraMap k X.functionField c * t.1 y,
            mul_mem_constSections c t⟩
          map_zero' := Subtype.ext (funext fun _ => mul_zero _)
          map_add' := fun _ _ => Subtype.ext (funext fun _ => mul_add _ _ _) }
     naturality := fun _ _ _ => rfl }⟩

variable [IsNoetherian X] [IsNormalScheme X] (D : WeilDivisor X)

noncomputable def quotMul (c : k) (x : X) :
    X.functionField ⧸ pointSubgroup D x →+ X.functionField ⧸ pointSubgroup D x :=
  QuotientAddGroup.map _ _ (AddMonoidHom.mulLeft (algebraMap k X.functionField c))
    (fun _ hf => mul_mem_pointSubgroup D x c hf)

lemma quotMul_mk (c : k) (x : X) (f : X.functionField) :
    quotMul D c x (QuotientAddGroup.mk f) = QuotientAddGroup.mk (algebraMap k X.functionField c * f) :=
  rfl

lemma quotMul_mem_quotSections (c : k) {V : X.Opens} (a : quotSections D V) :
    (fun z : V => quotMul D c z.1 (a.1 z)) ∈ quotSections D V := by
  intro y
  obtain ⟨W, hyW, h⟩ := a.2 y
  refine ⟨W, hyW, h.subset ?_⟩
  rintro z ⟨hzW, hz⟩
  exact ⟨hzW, fun h0 => hz (by simp only [h0, map_zero])⟩

noncomputable def quotSmul (c : k) : quotSheaf D ⟶ quotSheaf D :=
  ⟨{ app := fun _ => AddCommGrpCat.ofHom
        { toFun := fun a => ⟨fun z => quotMul D c z.1 (a.1 z), quotMul_mem_quotSections D c a⟩
          map_zero' := Subtype.ext (funext fun _ => map_zero _)
          map_add' := fun _ _ => Subtype.ext (funext fun _ => map_add _ _ _) }
     naturality := fun _ _ _ => rfl }⟩

noncomputable def divisorSeqSmul (c : k) : divisorSeq D ⟶ divisorSeq D where
  τ₁ := modulesAbMap (smulHom (divisorSheaf D) (scalarRingHom X c))
  τ₂ := constSmul c
  τ₃ := quotSmul D c
  comm₁₂ := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.ext
    intro t
    apply Subtype.ext
    funext y
    change sectionValue V.unop y (restrictTop V.unop (scalarRingHom X c)) *
      (show divisorSections D V.unop from t).1 y = _
    rw [sectionValue_scalar]
    rfl
  comm₂₃ := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply AddCommGrpCat.ext
    intro t
    rfl

end Endo

noncomputable instance globalAlgebra : Algebra k Γ(X, ⊤) := (scalarRingHom X).toAlgebra

section H0

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
  [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})]

variable (k) in

def globalL (D : WeilDivisor X) : Submodule k X.functionField where
  carrier := {f | ∀ Z : PrimeDivisor X, Z.valuation f ≤ WithZero.exp (D Z)}
  zero_mem' := fun Z => by simp
  add_mem' {f g} hf hg := fun Z => (Valuation.map_add _ _ _).trans (max_le (hf Z) (hg Z))
  smul_mem' c {f} hf := fun Z => by
    rw [Algebra.smul_def, map_mul]
    calc _ ≤ 1 * WithZero.exp (D Z) :=
          mul_le_mul' (Z.valuation_algebraMap_scalar_le_one c) (hf Z)
      _ = _ := one_mul _

omit [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u})] in
lemma mem_globalL (D : WeilDivisor X) (f : X.functionField) :
    f ∈ globalL k D ↔ ∀ Z : PrimeDivisor X, Z.valuation f ≤ WithZero.exp (D Z) := Iff.rfl

variable (k) in

noncomputable def divisorSectionsTopEquiv (D : WeilDivisor X) :
    divisorSections D ⊤ ≃+ globalL k D where
  toFun t := ⟨t.1 ⟨genericPoint X, trivial⟩, fun Z => by
    rw [divisorSections_apply_eq D t ⟨genericPoint X, trivial⟩ ⟨Z.point, trivial⟩]
    exact t.2.2 ⟨Z.point, trivial⟩ Z.2⟩
  invFun f := ⟨fun _ => f.1, fun _ => ⟨⊤, trivial, fun _ _ => rfl⟩,
    fun y hy => f.2 (PrimeDivisor.ofPoint y.1 hy)⟩
  left_inv t := Subtype.ext (funext fun y => divisorSections_apply_eq D t _ _)
  right_inv _ := rfl
  map_add' _ _ := rfl

variable (k) in

noncomputable def divisorH0AddEquiv (D : WeilDivisor X) :
    Sheaf.H.{w'} (modulesAb (divisorSheaf D)) 0 ≃+ globalL k D :=
  (Sheaf.H.equiv₀ (modulesAb (divisorSheaf D)) isTerminalTop).trans (divisorSectionsTopEquiv k D)

lemma divisorH0AddEquiv_apply (D : WeilDivisor X) (x : Sheaf.H.{w'} (modulesAb (divisorSheaf D)) 0)
    (y : (⊤ : X.Opens)) :
    (divisorH0AddEquiv k D x : X.functionField) =
      (show divisorSections D ⊤ from Sheaf.H.equiv₀ _ isTerminalTop x).1 y :=
  divisorSections_apply_eq D _ _ _

variable (k) in

noncomputable def divisorH0Equiv (D : WeilDivisor X) :
    Sheaf.H.{w'} (modulesAb (divisorSheaf D)) 0 ≃ₗ[k] globalL k D where
  toAddEquiv := divisorH0AddEquiv k D
  map_smul' c x := by
    apply Subtype.ext
    change (divisorH0AddEquiv k D (c • x) : X.functionField) =
      algebraMap k X.functionField c * (divisorH0AddEquiv k D x : X.functionField)
    rw [divisorH0AddEquiv_apply D _ ⟨genericPoint X, trivial⟩,
      divisorH0AddEquiv_apply D _ ⟨genericPoint X, trivial⟩, H.smul_def,
      ← Sheaf.H.equiv₀_naturality]
    change sectionValue ⊤ _ (restrictTop ⊤ (scalarRingHom X c)) * _ = _
    rw [sectionValue_scalar]

end H0

end GroundTheory.Arith.SchemeCoh
