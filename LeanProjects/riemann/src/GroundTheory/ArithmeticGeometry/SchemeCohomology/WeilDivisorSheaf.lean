import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.WeilDivisorLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

variable {X : Scheme.{u}}

noncomputable def sectionValue [IsIntegral X] (V : X.Opens) (y : V) :
    Γ(X, V) →+* X.functionField :=
  (algebraMap (X.presheaf.stalk y) X.functionField).comp (X.presheaf.germ V y y.2).hom

lemma sectionValue_eq [IsIntegral X] (V : X.Opens) (y : V) (r : Γ(X, V)) :
    sectionValue V y r = (haveI : Nonempty V := ⟨y⟩; X.germToFunctionField V r) := by
  have : Nonempty V := ⟨y⟩
  exact Scheme.algebraMap_germ_eq_germToFunctionField X y.2 r

lemma sectionValue_res [IsIntegral X] {V W : X.Opens} (h : W ≤ V) (y : W) (r : Γ(X, V)) :
    sectionValue W y (X.presheaf.map (homOfLE h).op r) = sectionValue V ⟨y.1, h y.2⟩ r := by
  simp only [sectionValue, RingHom.comp_apply]
  congr 1
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

lemma sectionValue_const [IsIntegral X] (V : X.Opens) (y z : V) (r : Γ(X, V)) :
    sectionValue V y r = sectionValue V z r := by
  rw [sectionValue_eq, sectionValue_eq]

def PrimeDivisor.ofPoint (y : X) (hy : ringKrullDim (X.presheaf.stalk y) = 1) : PrimeDivisor X :=
  ⟨y, hy⟩

@[simp] lemma PrimeDivisor.point_ofPoint (y : X) (hy : ringKrullDim (X.presheaf.stalk y) = 1) :
    (PrimeDivisor.ofPoint y hy).point = y := rfl

section

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

def divisorPredicate (D : WeilDivisor X) :
    TopCat.LocalPredicate (X := X.carrier) (fun _ => X.functionField) where
  pred {V} f := (∀ y : V, ∃ W : X.Opens, y.1 ∈ W ∧ ∀ z : V, z.1 ∈ W → f z = f y) ∧
    ∀ (y : V) (hy : ringKrullDim (X.presheaf.stalk y.1) = 1),
      (PrimeDivisor.ofPoint y.1 hy).valuation (f y) ≤ WithZero.exp (D (PrimeDivisor.ofPoint y.1 hy))
  res {V W} i f h := by
    refine ⟨fun y => ?_, fun y hy => h.2 (i y) hy⟩
    obtain ⟨W', hyW', hW'⟩ := h.1 (i y)
    exact ⟨W', hyW', fun z hz => hW' (i z) hz⟩
  locality {V} f w := by
    refine ⟨fun y => ?_, fun y hy => ?_⟩
    · obtain ⟨W, hyW, i, hW⟩ := w y
      obtain ⟨W', hyW', hW'⟩ := hW.1 ⟨y.1, hyW⟩
      refine ⟨W ⊓ W', ⟨hyW, hyW'⟩, fun z hz => ?_⟩
      exact hW' ⟨z.1, hz.1⟩ hz.2
    · obtain ⟨W, hyW, i, hW⟩ := w y
      exact hW.2 ⟨y.1, hyW⟩ hy

lemma PrimeDivisor.valuation_algebraMap_le_one (Z : PrimeDivisor X)
    (a : X.presheaf.stalk Z.point) : Z.valuation (algebraMap _ X.functionField a) ≤ 1 := by
  have := Z.isDedekindDomain_stalk
  simp only [PrimeDivisor.valuation]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _

def divisorSections (D : WeilDivisor X) (V : X.Opens) : AddSubgroup (V → X.functionField) where
  carrier := {f | (divisorPredicate D).pred f}
  zero_mem' := ⟨fun _ => ⟨⊤, trivial, fun _ _ => rfl⟩, fun y hy => by simp⟩
  add_mem' {f g} hf hg := by
    refine ⟨fun y => ?_, fun y hy => ?_⟩
    · obtain ⟨W₁, hy₁, h₁⟩ := hf.1 y
      obtain ⟨W₂, hy₂, h₂⟩ := hg.1 y
      exact ⟨W₁ ⊓ W₂, ⟨hy₁, hy₂⟩, fun z hz => by
        simp only [Pi.add_apply, h₁ z hz.1, h₂ z hz.2]⟩
    · exact (Valuation.map_add _ _ _).trans (max_le (hf.2 y hy) (hg.2 y hy))
  neg_mem' {f} hf := by
    refine ⟨fun y => ?_, fun y hy => ?_⟩
    · obtain ⟨W, hyW, h⟩ := hf.1 y
      exact ⟨W, hyW, fun z hz => by simp only [Pi.neg_apply, h z hz]⟩
    · simp only [Pi.neg_apply, Valuation.map_neg]
      exact hf.2 y hy

lemma smul_mem_divisorSections (D : WeilDivisor X) (V : X.Opens) (r : Γ(X, V))
    {f : V → X.functionField} (hf : f ∈ divisorSections D V) :
    (fun y => sectionValue V y r * f y) ∈ divisorSections D V := by
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · obtain ⟨W, hyW, h⟩ := hf.1 y
    exact ⟨W, hyW, fun z hz => by simp only [h z hz, sectionValue_const V z y r]⟩
  · simp only [map_mul]
    calc _ ≤ 1 * WithZero.exp (D (PrimeDivisor.ofPoint y.1 hy)) :=
          mul_le_mul' ((PrimeDivisor.ofPoint y.1 hy).valuation_algebraMap_le_one
            (X.presheaf.germ V y.1 y.2 r)) (hf.2 y hy)
      _ = _ := one_mul _

noncomputable instance (D : WeilDivisor X) (V : X.Opens) :
    Module Γ(X, V) (divisorSections D V) where
  smul r f := ⟨fun y => sectionValue V y r * f.1 y, smul_mem_divisorSections D V r f.2⟩
  one_smul f := Subtype.ext (funext fun y => by
    change sectionValue V y 1 * f.1 y = f.1 y
    rw [map_one, one_mul])
  mul_smul r s f := Subtype.ext (funext fun y => by
    change sectionValue V y (r * s) * f.1 y = sectionValue V y r * (sectionValue V y s * f.1 y)
    rw [map_mul, mul_assoc])
  smul_zero r := Subtype.ext (funext fun y => by
    change sectionValue V y r * 0 = 0
    rw [mul_zero])
  smul_add r f g := Subtype.ext (funext fun y => by
    change sectionValue V y r * (f.1 y + g.1 y) = sectionValue V y r * f.1 y +
      sectionValue V y r * g.1 y
    rw [mul_add])
  add_smul r s f := Subtype.ext (funext fun y => by
    change sectionValue V y (r + s) * f.1 y = sectionValue V y r * f.1 y +
      sectionValue V y s * f.1 y
    rw [map_add, add_mul])
  zero_smul f := Subtype.ext (funext fun y => by
    change sectionValue V y 0 * f.1 y = 0
    rw [map_zero, zero_mul])

lemma divisorSections_smul_apply (D : WeilDivisor X) (V : X.Opens) (r : Γ(X, V))
    (f : divisorSections D V) (y : V) : (r • f).1 y = sectionValue V y r * f.1 y := rfl

def divisorSectionsRes (D : WeilDivisor X) {V W : X.Opens} (h : W ≤ V) :
    divisorSections D V →+ divisorSections D W where
  toFun f := ⟨fun y => f.1 ⟨y.1, h y.2⟩, (divisorPredicate D).res (homOfLE h) f.1 f.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable def divisorPresheaf (D : WeilDivisor X) : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := AddCommGrpCat.of (divisorSections D V.unop)
  map i := AddCommGrpCat.ofHom (divisorSectionsRes D i.unop.le)
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable instance (D : WeilDivisor X) (V : (Opens X)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj V) ((divisorPresheaf D).obj V) :=
  inferInstanceAs (Module Γ(X, V.unop) (divisorSections D V.unop))

noncomputable def divisorPresheafOfModules (D : WeilDivisor X) :
    PresheafOfModules X.ringCatSheaf.obj :=
  PresheafOfModules.ofPresheaf (divisorPresheaf D) (fun {V W} i r f => by
    apply Subtype.ext
    funext y
    exact congrArg (· * f.1 ⟨y.1, i.unop.le y.2⟩)
      (sectionValue_res i.unop.le y (show Γ(X, V.unop) from r)).symm)

theorem divisorPresheaf_isSheaf (D : WeilDivisor X) :
    TopCat.Presheaf.IsSheaf (X := X.carrier) (divisorPresheaf D) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat)]
  refine TopCat.Presheaf.isSheaf_of_iso ?_
    (TopCat.subpresheafToTypes.isSheaf (divisorPredicate D))
  refine NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun f => ⟨f.1, f.2⟩
      invFun := fun f => ⟨f.1, f.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }) ?_
  intro V W i
  rfl

noncomputable def divisorSheaf (D : WeilDivisor X) : X.Modules :=
  SheafOfModules.mk (divisorPresheafOfModules D) (divisorPresheaf_isSheaf D)

lemma PrimeDivisor.valuation_le_exp_iff (Z : PrimeDivisor X) {f : X.functionField} (hf : f ≠ 0)
    (n : ℤ) : Z.valuation f ≤ WithZero.exp n ↔ -n ≤ Z.ord f := by
  have hv0 : Z.valuation f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  rw [← WithZero.log_le_iff_le_exp hv0, PrimeDivisor.ord]
  omega

lemma divisorSections_apply_eq (D : WeilDivisor X) {V : X.Opens} (t : divisorSections D V)
    (y z : V) : t.1 y = t.1 z := by
  obtain ⟨Wy, hyW, hy⟩ := t.2.1 y
  obtain ⟨Wz, hzW, hz⟩ := t.2.1 z
  obtain ⟨w, hw⟩ := nonempty_preirreducible_inter (Wy ⊓ V).isOpen (Wz ⊓ V).isOpen
    ⟨y.1, hyW, y.2⟩ ⟨z.1, hzW, z.2⟩
  rw [← hy ⟨w, hw.1.2⟩ hw.1.1, hz ⟨w, hw.1.2⟩ hw.2.1]

end

section Basis

variable [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

end Basis

end GroundTheory.Arith.SchemeCoh
