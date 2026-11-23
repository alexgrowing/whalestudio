import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct
open GlobalTheory.GrpTangent

namespace GlobalTheory.SerreLie

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isLieComb_one_iff (c : R) (v x : epsR R ⟶ G) :
    IsLieComb ![c] ![v] x ↔ x = GrpTangent.epsScale c ≫ v := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have h : u 0 = GrpTangent.epsScale c ≫ v := Over.OverMorphism.ext (hu 0)
    simp [h]
  · rintro rfl
    refine ⟨![GrpTangent.epsScale c ≫ v], fun i => ?_, by simp⟩
    fin_cases i
    rfl

variable [IsCommMonObj G] {O : Type} [CommRing O] [Algebra O R]

def multiples (a : OAct O G) {v : epsR R ⟶ G} (hv : IsTangent v)
    (ha : ∀ c, v ≫ a.act c = GrpTangent.epsScale (algebraMap O R c) ≫ v) : R →ₗ[O] Pts a (epsR R) where
  toFun r := Pts.mk a (GrpTangent.epsScale r ≫ v)
  map_add' r s := Pts.ext (epsScale_add_comp r s hv)
  map_smul' c r := Pts.ext (by
    simp only [Pts.hom_mk, RingHom.id_apply, Pts.hom_smul, Category.assoc, ha]
    rw [epsScale_mul_assoc, Algebra.smul_def, mul_comm])

theorem hom_multiples (a : OAct O G) {v : epsR R ⟶ G} (hv : IsTangent v)
    (ha : ∀ c, v ≫ a.act c = GrpTangent.epsScale (algebraMap O R c) ≫ v) (r : R) :
    (multiples a hv ha r).hom = GrpTangent.epsScale r ≫ v := rfl

omit [Algebra O R] in
theorem pre_eq_zero_iff (a : OAct O G) (x : Pts a (epsR R)) :
    Pts.pre a (toUnit (epsR R) ≫ epsZero R) x = 0 ↔ IsTangent x.hom := by
  rw [isTangent_iff]
  constructor
  · intro h
    have h1 : (toUnit (epsR R) ≫ epsZero R) ≫ x.hom = 1 := congrArg Pts.hom h
    have h2 := congrArg (epsZero R ≫ ·) h1
    simp only [← Category.assoc, MonObj.comp_one] at h2
    rwa [toUnit_unique (epsZero R ≫ toUnit _) (𝟙 _), Category.id_comp] at h2
  · intro h
    exact Pts.ext (by rw [Pts.hom_pre, Category.assoc, h, MonObj.comp_one]; rfl)

omit [Algebra O R] in
theorem isTangent_sub_pre (a : OAct O G) (x : Pts a (epsR R)) :
    IsTangent (x - Pts.pre a (toUnit (epsR R) ≫ epsZero R) x).hom := by
  rw [← pre_eq_zero_iff, map_sub, sub_eq_zero]
  apply Pts.ext
  simp only [Pts.hom_pre, ← Category.assoc]
  rw [Category.assoc (toUnit _) (epsZero R) (toUnit _),
    toUnit_unique (epsZero R ≫ toUnit _) (𝟙 _), Category.comp_id]

theorem exists_retraction (a : OAct O G) {v : epsR R ⟶ G} (hv : IsLieBasis ![v])
    (ha : ∀ c, v ≫ a.act c = GrpTangent.epsScale (algebraMap O R c) ≫ v) :
    ∃ ρ : Pts a (epsR R) →ₗ[O] R, ρ ∘ₗ multiples a (hv.1 0) ha = LinearMap.id ∧
      multiples a (hv.1 0) ha ∘ₗ ρ = LinearMap.id - Pts.pre a (toUnit (epsR R) ≫ epsZero R) := by
  have hinj : Function.Injective (multiples a (hv.1 0) ha) := fun r s h => by
    have h' : GrpTangent.epsScale r ≫ v = GrpTangent.epsScale s ≫ v := congrArg Pts.hom h
    have := (hv.2 _ (isTangent_epsScale r (hv.1 0))).unique
      ((isLieComb_one_iff r v _).2 rfl) ((isLieComb_one_iff s v _).2 h')
    exact congrFun this 0
  have hsur : ∀ x : Pts a (epsR R), ∃ r, multiples a (hv.1 0) ha r =
      (LinearMap.id - Pts.pre a (toUnit (epsR R) ≫ epsZero R) : _ →ₗ[O] _) x := fun x => by
    obtain ⟨c, hc, -⟩ := hv.2 _ (isTangent_sub_pre a x)
    have e : c = ![c 0] := by ext i; fin_cases i; rfl
    rw [e, isLieComb_one_iff] at hc
    exact ⟨c 0, Pts.ext hc.symm⟩
  choose ρ hρ using hsur
  refine ⟨⟨⟨ρ, fun x y => hinj ?_⟩, fun c x => hinj ?_⟩, LinearMap.ext fun r => hinj ?_,
    LinearMap.ext hρ⟩
  · rw [map_add, hρ, hρ, hρ, map_add]
  · simp only [RingHom.id_apply, map_smul, hρ]
  · change multiples a (hv.1 0) ha (ρ _) = _
    rw [hρ, LinearMap.sub_apply, (pre_eq_zero_iff a (multiples a (hv.1 0) ha r)).2
      (isTangent_epsScale r (hv.1 0)), sub_zero]
    rfl

theorem exists_lie_tensor : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (O : Type) [CommRing O] [Algebra O R] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (t : IsTensor A b G a M) (v : epsR R ⟶ G), IsLieBasis ![v] → (∀ c, IsLieComb ![algebraMap O R c] ![v] (v ≫ a.act c)) → ∃ Φ : R ⊗[O] M → (epsR R ⟶ A), Function.Injective Φ ∧ (∀ x, IsTangent x ↔ x ∈ Set.range Φ) ∧ (∀ y z, Φ (y + z) = Φ y * Φ z) ∧ (∀ (c : R) y, IsLieComb ![c] ![Φ y] (Φ (c • y))) ∧ (∀ m, Φ (1 ⊗ₜ m) = v ≫ t.tmul m) ∧ ∀ (φ : M →ₗ[O] M) y, Φ (φ.baseChange R y) = Φ y ≫ t.mapLeft t φ := by
  intro R _ G _ _ O _ _ M _ _ _ _ A _ _ a b t v hv ha'
  have ha : ∀ c, v ≫ a.act c = GrpTangent.epsScale (algebraMap O R c) ≫ v :=
    fun c => (isLieComb_one_iff _ _ _).1 (ha' c)
  obtain ⟨ρ, h₁, h₂⟩ := exists_retraction a hv ha
  set j := multiples a (hv.1 0) ha with hj
  let Ψ : R ⊗[O] M →ₗ[O] Pts b (epsR R) :=
    (t.equiv _).toLinearMap ∘ₗ j.lTensor M ∘ₗ (TensorProduct.comm O R M).toLinearMap
  have hΨ : ∀ (r : R) (m : M), (Ψ (r ⊗ₜ m)).hom = GrpTangent.epsScale r ≫ v ≫ t.tmul m := fun r m => by
    simp [Ψ, hj, hom_multiples]
  refine ⟨fun y => (Ψ y).hom, fun y z h => ?_, fun x => ⟨fun hx => ?_, ?_⟩, fun y z => ?_,
    fun c y => ?_, fun m => ?_, fun φ y => ?_⟩
  · have h' : j.lTensor M (TensorProduct.comm O R M y) = j.lTensor M (TensorProduct.comm O R M z) :=
      (t.equiv _).injective (Pts.ext h)
    have h'' := congrArg (ρ.lTensor M) h'
    simp only [← LinearMap.lTensor_comp_apply, h₁, LinearMap.lTensor_id, LinearMap.id_apply] at h''
    exact (TensorProduct.comm O R M).injective h''
  · obtain ⟨z, hz⟩ := (t.equiv (epsR R)).surjective (Pts.mk b x)
    have h0 : (Pts.pre a (toUnit (epsR R) ≫ epsZero R)).lTensor M z = 0 := by
      apply (t.equiv _).injective
      rw [t.natural, hz, map_zero]
      exact (pre_eq_zero_iff b _).2 hx
    refine ⟨(TensorProduct.comm O R M).symm (ρ.lTensor M z), ?_⟩
    simp only [Ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [← LinearMap.lTensor_comp_apply, h₂, LinearMap.lTensor_sub, LinearMap.sub_apply, h0,
      sub_zero, LinearMap.lTensor_id, LinearMap.id_apply, hz, Pts.hom_mk]
  · rintro ⟨y, rfl⟩
    rw [← pre_eq_zero_iff]
    induction y with
    | zero => simp
    | tmul r m =>
      rw [pre_eq_zero_iff, hΨ]
      exact isTangent_epsScale r (isTangent_comp (hv.1 0) _)
    | add y z hy hz => rw [map_add, map_add, hy, hz, add_zero]
  · simp only [map_add, Pts.hom_add]
  · rw [isLieComb_one_iff]
    induction y with
    | zero => simp
    | tmul r m =>
      simp only [TensorProduct.smul_tmul', hΨ, smul_eq_mul]
      rw [epsScale_mul_assoc]
    | add y z hy hz =>
      simp only [smul_add, map_add, Pts.hom_add, MonObj.comp_mul] at hy hz ⊢
      rw [hy, hz]
  · simp only [hΨ, epsScale_one, Category.id_comp]
  · induction y with
    | zero => simp
    | tmul r m => simp only [LinearMap.baseChange_tmul, hΨ, Category.assoc, IsTensor.tmul_mapLeft]
    | add y z hy hz =>
      simp only [map_add, Pts.hom_add, MonObj.mul_comp] at hy hz ⊢
      rw [hy, hz]

end GlobalTheory.SerreLie
