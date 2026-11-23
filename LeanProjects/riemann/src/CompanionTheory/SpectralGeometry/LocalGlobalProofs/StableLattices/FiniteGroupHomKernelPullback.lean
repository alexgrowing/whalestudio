import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TrzCob
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.KerPull
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.KerPull.Kernel

section General

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {A A' H : C} [GrpObj A] [GrpObj A']
  {q : A ⟶ A'} [IsMonHom q] {i : H ⟶ A}

theorem mono_of_isKernel (hp : IsPullback i (toUnit H) q η[A']) : Mono i :=
  ⟨fun _ _ e => hp.hom_ext e (toUnit_unique _ _)⟩

def kerLift (hp : IsPullback i (toUnit H) q η[A']) {W : C} (f : W ⟶ A) (hf : f ≫ q = 1) : W ⟶ H :=
  hp.lift f (toUnit W) (by rw [hf, Hom.one_def])

@[reassoc (attr := simp)]
theorem kerLift_comp (hp : IsPullback i (toUnit H) q η[A']) {W : C} (f : W ⟶ A) (hf : f ≫ q = 1) :
    kerLift hp f hf ≫ i = f :=
  hp.lift_fst ..

theorem comp_kills (hp : IsPullback i (toUnit H) q η[A']) {W : C} (x : W ⟶ H) : (x ≫ i) ≫ q = 1 := by
  rw [Category.assoc, hp.w, ← Category.assoc, toUnit_unique (x ≫ toUnit H) (toUnit W), Hom.one_def]

@[instance_reducible]
def grpObjOfIsKernel (hp : IsPullback i (toUnit H) q η[A']) : GrpObj H :=
  have := mono_of_isKernel hp
  { one := kerLift hp η[A] (by rw [IsMonHom.one_hom, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp])
    mul := kerLift hp (fst H H ≫ i * snd H H ≫ i) (by
      rw [MonObj.mul_comp, comp_kills hp, comp_kills hp, _root_.mul_one])
    inv := kerLift hp (i ≫ ι[A]) (by
      have e : i ≫ q = 1 := by simpa using comp_kills hp (𝟙 H)
      have h : (i⁻¹ * i) ≫ q = 1 := by rw [inv_mul_cancel, MonObj.one_comp]
      rw [MonObj.mul_comp, e, _root_.mul_one] at h
      exact h)
    one_mul := by
      rw [← cancel_mono i]
      simp [MonObj.comp_mul]
      rw [toUnit_unique (fst (𝟙_ C) H) (toUnit _), ← Hom.one_def, _root_.one_mul, leftUnitor_hom]
    mul_one := by
      rw [← cancel_mono i]
      simp [MonObj.comp_mul]
      rw [toUnit_unique (snd H (𝟙_ C)) (toUnit _), ← Hom.one_def, _root_.mul_one, rightUnitor_hom]
    mul_assoc := by
      rw [← cancel_mono i]
      simp [MonObj.comp_mul]
      exact _root_.mul_assoc _ _ _
    left_inv := by
      rw [← cancel_mono i]
      simp [MonObj.comp_mul]
      rw [← Hom.one_def]
      exact inv_mul_cancel i
    right_inv := by
      rw [← cancel_mono i]
      simp [MonObj.comp_mul]
      rw [← Hom.one_def]
      exact mul_inv_cancel i }

theorem isMonHom_of_isKernel (hp : IsPullback i (toUnit H) q η[A']) :
    letI := grpObjOfIsKernel hp
    IsMonHom i := by
  letI := grpObjOfIsKernel hp
  refine { one_hom := kerLift_comp hp _ _, mul_hom := ?_ }
  refine (kerLift_comp hp _ _).trans ?_
  rw [Hom.mul_def]
  simp

theorem isCommMonObj_of_isKernel [BraidedCategory C] [IsCommMonObj A]
    (hp : IsPullback i (toUnit H) q η[A']) :
    letI := grpObjOfIsKernel hp
    IsCommMonObj H := by
  letI := grpObjOfIsKernel hp
  have := mono_of_isKernel hp
  have := isMonHom_of_isKernel hp
  refine (isCommMonObj_iff_isMulCommutative _).mpr fun T => ⟨⟨fun x y => ?_⟩⟩
  rw [← cancel_mono i, MonObj.mul_comp, MonObj.mul_comp, mul_comm]

end General

theorem exists_finite_kernel : ∀ (k : Type) [Field k] (A A' : Over (Sp k)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → ∀ (q : A ⟶ A'), IsMonHom q → IsFinite q.left →
    ∃ (H : Over (Sp k)) (_ : GrpObj H) (_ : IsCommMonObj H) (i : H ⟶ A), IsMonHom i ∧ IsFinite H.hom ∧
      IsPullback i (toUnit _) q η[A'] := by
  intro k _ A A' _ _ hA q hq hf
  have := hA.comm
  have hp : IsPullback (pullback.fst q η[A']) (toUnit (pullback q η[A'])) q η[A'] := by
    rw [toUnit_unique (toUnit _) (pullback.snd q η[A'])]
    exact IsPullback.of_hasPullback _ _
  refine ⟨pullback q η[A'], grpObjOfIsKernel hp, isCommMonObj_of_isKernel hp, pullback.fst _ _,
    isMonHom_of_isKernel hp, ?_, hp⟩
  have hl := hp.map (Over.forget _)
  have h1 : IsFinite (toUnit (pullback q η[A'])).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) hl hf
  have h2 : (pullback q η[A']).hom = (toUnit (pullback q η[A'])).left ≫ (𝟙_ (Over (Sp k))).hom :=
    (Over.w _).symm
  rw [h2]
  exact inferInstanceAs (IsFinite (_ ≫ 𝟙 _))
end GlobalTheory.CompanionTheory.KerPull.Kernel
