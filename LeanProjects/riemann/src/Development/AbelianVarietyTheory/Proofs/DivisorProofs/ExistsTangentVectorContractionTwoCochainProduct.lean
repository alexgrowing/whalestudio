import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.ContrMor

variable {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]
  {D : Type} [CommRing D] [Algebra R D] {D' : Type} [CommRing D'] [Algebra R D']

theorem specOverOfAlgHom_pointWithZeroSecondCoord (φ : D →ₐ[R] D') (x : Pt A D) : spOver φ ≫ pt0 B x = pt0 B (spOver φ ≫ x) := by
  simp [pt0, comp_lift, MonObj.comp_one]

theorem spOver_fst_ptV (v : epsR R ⟶ B) (hv : IsTangent v) (x : Pt A D) :
    spOver (TrivSqZeroExt.fstHom R D D) ≫ ptV v x = pt0 B x := by
  have k : spOver (TrivSqZeroExt.fstHom R D D) ≫ spOver (EpsWeil.epsMap R D) =
      toUnit _ ≫ GrpTangent.epsZero R := by
    refine Over.OverMorphism.ext ?_
    rw [spOver_comp, PDiv.spOver_left, Over.comp_left, Over.toUnit_left]
    refine Eq.trans (congrArg spMap (RingHom.ext fun a ↦ ?_)) (Cris.spMap_comp
      (TrivSqZeroExt.fstHom R R R).toRingHom (algebraMap R D))
    simp [EpsWeil.epsMap, DualNumber.lift_apply_apply, TrivSqZeroExt.algebraMap_eq_inl']
  ext1
  · simp only [ptV, pt0, comp_lift, lift_fst, ← Category.assoc, spOver_comp]
    rw [show (TrivSqZeroExt.fstHom R D D).comp (TrivSqZeroExt.inlAlgHom R D D) = AlgHom.id R D from
      AlgHom.ext fun _ ↦ rfl, PDiv.spOver_id, Category.id_comp]
  · simp only [ptV, pt0, comp_lift, lift_snd]
    rw [← Category.assoc, k, Category.assoc, (GrpTangent.isTangent_iff v).1 hv, MonObj.comp_one]

theorem spOver_epsHom_ptV (v : epsR R ⟶ B) (φ : D →ₐ[R] D') (x : Pt A D) :
    spOver (epsHom φ) ≫ ptV v x = ptV v (spOver φ ≫ x) := by
  ext1
  · simp only [ptV, comp_lift, lift_fst, ← Category.assoc, spOver_comp]
    congr 2
    ext c <;> simp [epsHom, DualNumber.lift_apply_apply]
  · simp only [ptV, comp_lift, lift_snd, ← Category.assoc, spOver_comp]
    congr 2
    ext <;> simp only [AlgHom.comp_apply, EpsWeil.epsMap, epsHom, DualNumber.lift_apply_eps]

def sHom (x : Pt A D) : trivAt (pt0 B x) ⟶ thickAt B x :=
  (epsExt R D).secHom (pt0 B x).w (epsExt R D).i (epsExt R D).π_i

def iHom (v : epsR R ⟶ B) (hv : IsTangent v) (x : Pt A D) : trivAt (ptV v x) ⟶ thickAt B x :=
  Thick.trivHom (AlgHom.id R _) (by
    have := congrArg Over.Hom.left (spOver_fst_ptV v hv x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

def aHom (φ : D →ₐ[R] D') (x : Pt A D) : trivAt (pt0 B x) ⟶ trivAt (pt0 B (spOver φ ≫ x)) :=
  Thick.trivHom φ (by
    have := congrArg Over.Hom.left (specOverOfAlgHom_pointWithZeroSecondCoord (B := B) φ x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

def bHom (v : epsR R ⟶ B) (φ : D →ₐ[R] D') (x : Pt A D) :
    trivAt (ptV v x) ⟶ trivAt (ptV v (spOver φ ≫ x)) :=
  Thick.trivHom (epsHom φ) (by
    have := congrArg Over.Hom.left (spOver_epsHom_ptV v φ x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

def τHom (φ : D →ₐ[R] D') (x : Pt A D) : thickAt B x ⟶ thickAt B (spOver φ ≫ x) :=
  (epsExt R D).thickHom (epsExt R D') (epsHom φ) φ
    (fun c ↦ by simp [epsHom, DualNumber.lift_apply_apply]) _ _ (by
    have := congrArg Over.Hom.left (specOverOfAlgHom_pointWithZeroSecondCoord (B := B) φ x)
    rw [Over.comp_left, PDiv.spOver_left] at this
    exact this)

end GlobalTheory.PtExt.ContrMor

namespace GlobalTheory.PtExt.ContrMor

theorem exists_contr : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (v : epsR R ⟶ B), IsTangent v → (∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D), ∃ (s : trivAt (pt0 B x) ⟶ thickAt B x) (i : trivAt (ptV v x) ⟶ thickAt B x) (s' : trivAt (pt0 B (spOver φ ≫ x)) ⟶ thickAt B (spOver φ ≫ x)) (i' : trivAt (ptV v (spOver φ ≫ x)) ⟶ thickAt B (spOver φ ≫ x)) (a : trivAt (pt0 B x) ⟶ trivAt (pt0 B (spOver φ ≫ x))) (b : trivAt (ptV v x) ⟶ trivAt (ptV v (spOver φ ≫ x))) (τ : thickAt B x ⟶ thickAt B (spOver φ ≫ x)), (∀ r, s.φ r = TrivSqZeroExt.inl r) ∧ (∀ r, i.φ r = r) ∧ (∀ r, s'.φ r = TrivSqZeroExt.inl r) ∧ (∀ r, i'.φ r = r) ∧ (∀ r, a.φ r = φ r) ∧ (∀ r, b.φ r = epsHom φ r) ∧ (∀ r, τ.φ r = epsHom φ r)) ∧ ∀ z : C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), ∃ κ : Fn1 A, IsContr z v κ := by
  intro R _ A B _ _ v hv
  refine ⟨fun D _ _ D' _ _ φ x ↦ ⟨sHom x, iHom v hv x, sHom _, iHom v hv _, aHom φ x, bHom v φ x, τHom φ x,
    fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩, fun z ↦ ?_⟩
  refine ⟨fun D _ _ D' _ _ φ x ↦ TrivSqZeroExt.snd (R := D')
    (z _ _ _ (sHom x) (τHom φ x) - z _ _ _ (aHom φ x) (sHom _) - z _ _ _ (iHom v hv x) (τHom φ x) +
      z _ _ _ (bHom v φ x) (iHom v hv _)), ?_⟩
  intro D _ _ D' _ _ φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ
  obtain rfl : s = sHom x := Thick.hom_ext fun r ↦ (hs r).trans rfl
  obtain rfl : i = iHom v hv x := Thick.hom_ext fun r ↦ (hi r).trans rfl
  obtain rfl : s' = sHom _ := Thick.hom_ext fun r ↦ (hs' r).trans rfl
  obtain rfl : i' = iHom v hv _ := Thick.hom_ext fun r ↦ (hi' r).trans rfl
  obtain rfl : a = aHom φ x := Thick.hom_ext fun r ↦ (ha r).trans rfl
  obtain rfl : b = bHom v φ x := Thick.hom_ext fun r ↦ (hb r).trans rfl
  obtain rfl : τ = τHom φ x := Thick.hom_ext fun r ↦ (hτ r).trans rfl
  rfl

end GlobalTheory.PtExt.ContrMor
