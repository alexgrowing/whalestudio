import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FrameFibre

section Push

variable {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

def push (hφ : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') : Over.mk (T.hom ≫ f) ⟶ G :=
  Over.homMk (x.left ≫ φ) (by
    have h1 := hφ.1.w
    have h2 := Over.w x
    simp only [Over.mk_hom, Category.assoc, Functor.id_obj, Functor.const_obj_obj, Over.mk_left]
    rw [h1, ← Category.assoc, h2])

theorem push_mul (hφ : IsGrpPullback G' G f φ) {T : Over S'} (x y : T ⟶ G') :
    push hφ (x * y) = push hφ x * push hφ y := by
  apply Over.OverMorphism.ext
  exact (hφ.2 T x y (push hφ x) (push hφ y) rfl rfl).symm

theorem push_one (hφ : IsGrpPullback G' G f φ) (T : Over S') :
    push hφ (1 : T ⟶ G') = 1 := by
  have h := push_mul hφ (1 : T ⟶ G') 1
  rw [_root_.mul_one] at h
  exact left_eq_mul.mp h

end Push

theorem spec_fst_dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom B B B).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualMap f)) =
      Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  simp [dualMap]

theorem spec_alg_dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    Spec.map (CommRingCat.ofHom (dualMap f)) ≫ Spec.map (CommRingCat.ofHom (algebraMap A (DualNumber A))) =
      Spec.map (CommRingCat.ofHom (algebraMap B (DualNumber B))) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem spec_epsMul_dualMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (c : A) :
    Spec.map (CommRingCat.ofHom (epsMul (f c))) ≫ Spec.map (CommRingCat.ofHom (dualMap f)) =
      Spec.map (CommRingCat.ofHom (dualMap f)) ≫ Spec.map (CommRingCat.ofHom (epsMul c)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  ext <;> simp [dualMap, epsMul, mul_comm]

theorem exists_linear_of_pullback {X : Scheme.{0}} {R : Type} [CommRing R] {G' : Over (Sp R)} [GrpObj G']
    {G : Over X} [GrpObj G] {h : Sp R ⟶ X} {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G h φ) {g : ℕ}
    (M : LieModel G' (𝟙 (Sp R)) (Fin g → R)) (ψ : R →+* ℂ) {Vz : Type} [AddCommGroup Vz] [Module ℂ Vz]
    (MR : LieModel G (spMap ψ ≫ h) Vz) :
    ∃ Θ : (Fin g → ℂ) →ₗ[ℂ] Vz, ∀ x : Fin g → R,
      (MR.pt (Θ (fun e => ψ (x e)))).left = spMap (dualMap ψ) ≫ (M.pt x).left ≫ φ := by
  let c : epsAt (spMap ψ ≫ h) ⟶ Over.mk ((epsAt (𝟙 (Sp R))).hom ≫ h) :=
    Over.homMk (spMap (dualMap ψ)) (by
      have key := spec_alg_dualMap ψ
      simp only [Over.mk_hom, Category.comp_id]
      rw [← Category.assoc, key, Category.assoc])
  let w : (Fin g → R) → (epsAt (spMap ψ ≫ h) ⟶ G) := fun x => c ≫ push hφ (M.pt x)
  have wl : ∀ x, (w x).left = spMap (dualMap ψ) ≫ (M.pt x).left ≫ φ := fun _ => rfl
  have wt : ∀ x, IsTanAt G (spMap ψ ≫ h) (w x) := by
    intro x
    let c0 : Over.mk (spMap ψ ≫ h) ⟶ Over.mk ((Over.mk (𝟙 (Sp R))).hom ≫ h) :=
      Over.homMk (spMap ψ) (by simp)
    have h0 : c0 ≫ push hφ (1 : Over.mk (𝟙 (Sp R)) ⟶ G') = 1 := by
      rw [push_one]; exact MonObj.comp_one c0
    have h1 : spMap ψ ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G').left ≫ φ = (1 : Over.mk (spMap ψ ≫ h) ⟶ G).left :=
      congrArg CommaMorphism.left h0
    have h2 := M.tan x
    unfold IsTanAt at h2 ⊢
    rw [wl, ← h1, ← h2, ← Category.assoc, spec_fst_dualMap ψ]
    simp only [Category.assoc]
  choose j hj using fun x => MR.onto (w x) (wt x)
  have jadd : ∀ x y, j (x + y) = j x + j y := by
    intro x y
    apply MR.inj
    rw [MR.add, hj, hj, hj]
    simp only [w, M.add, push_mul, MonObj.comp_mul]
  have jsmul : ∀ (a : R) x, j (a • x) = ψ a • j x := by
    intro a x
    apply MR.inj
    apply Over.OverMorphism.ext
    rw [MR.smul, hj, hj, wl, wl, M.smul, ← Category.assoc (Spec.map _) (spMap (dualMap ψ)),
      spec_epsMul_dualMap]
    simp only [Category.assoc]
  let J : (Fin g → R) →+ Vz := AddMonoidHom.mk' j jadd
  refine ⟨∑ i, (LinearMap.proj i : (Fin g → ℂ) →ₗ[ℂ] ℂ).smulRight (j (Pi.single i 1)), fun x => ?_⟩
  have hΘ : (∑ i, (LinearMap.proj i : (Fin g → ℂ) →ₗ[ℂ] ℂ).smulRight (j (Pi.single i 1)))
      (fun e => ψ (x e)) = j x := by
    have hx : x = ∑ i, x i • (Pi.single i 1 : Fin g → R) := by
      conv_lhs => rw [← Finset.univ_sum_single x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    have hJ : J x = ∑ i, J (x i • (Pi.single i 1 : Fin g → R)) := by
      conv_lhs => rw [hx]
      exact map_sum J _ _
    have hJ' : j x = ∑ i, ψ (x i) • j (Pi.single i 1) := by
      refine hJ.trans (Finset.sum_congr rfl fun i _ => jsmul _ _)
    rw [hJ']
    simp [LinearMap.sum_apply]
  rw [hΘ, hj, wl]

theorem exists_linear_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (t' : SAB H (Sp R)) (h : Sp R ⟶ X) (m : SABMap t' t h) (g : ℕ) (M : LieModel t'.G (𝟙 (Sp R)) (Fin g → R)) (ψ : R →+* ℂ) (Vz : Type) [AddCommGroup Vz] [Module ℂ Vz] (MR : LieModel t.G (spMap ψ ≫ h) Vz), ∃ Θ : (Fin g → ℂ) →ₗ[ℂ] Vz, ∀ x : Fin g → R, (MR.pt (Θ (fun e => ψ (x e)))).left = spMap (dualMap ψ) ≫ (M.pt x).left ≫ m.φ := by
  intro E _ _ _ H X t R _ t' h m g M ψ Vz _ _ MR
  exact exists_linear_of_pullback m.cart M ψ MR

end GlobalTheory.CompanionTheory.Ar.FrameFibre
