import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

section

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G B T : Over S} {G' B' : Over S'} [GrpObj G] [GrpObj B] [GrpObj G']
  [GrpObj B'] {φ : G'.left ⟶ G.left} {β : B'.left ⟶ B.left}

theorem exists_imageHom (hG : IsGrpPullback G' G f φ) (hB : IsGrpPullback B' B f β) (q : G' ⟶ B') [IsMonHom q]
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (xe : Z ⟶ G'.left) (x₀ : T ⟶ G) (h₀ : xe ≫ φ = r ≫ x₀.left) :
    ∃ (Y : Over S) (R : Y ⟶ T) (Φ : (T ⟶ G) → (Y ⟶ B)), Φ 1 = 1 ∧ (∀ x y, Φ (x * y) = Φ x * Φ y) ∧
      (∀ x, Φ x⁻¹ = (Φ x)⁻¹) ∧
      (∀ x b, (∀ ye : Z ⟶ G'.left, ye ≫ φ = r ≫ x.left → ye ≫ q.left ≫ β = r ≫ b.left) → Φ x = R ≫ b) ∧
      ∀ b, Φ x₀ = R ≫ b → xe ≫ q.left ≫ β = r ≫ b.left := by
  have hc : r ≫ T.hom = (xe ≫ G'.hom) ≫ f := by
    rw [Category.assoc, ← hG.1.w, reassoc_of% h₀, Over.w]
  obtain ⟨eG, heG⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hG _ _ hc
  obtain ⟨eB, heB⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hB _ _ hc
  let R : Over.mk (r ≫ T.hom) ⟶ T := Over.homMk r rfl
  refine ⟨_, R, fun x => eB (eG.symm (R ≫ x) ≫ q), ?_, fun x y => ?_, fun x => ?_, fun x b h => ?_,
    fun b h => ?_⟩
  · simp only [MonObj.comp_one, map_one, MonObj.one_comp]
  · simp only [MonObj.comp_mul, map_mul, MonObj.mul_comp]
  · simp only [GrpObj.comp_inv, map_inv, GrpObj.inv_comp]
  · apply Over.OverMorphism.ext
    refine (heB _).trans ((Category.assoc _ _ _).trans (h _ ?_))
    refine (heG _).symm.trans ?_
    rw [MulEquiv.apply_symm_apply]
    rfl
  · let xe' : Over.mk (xe ≫ G'.hom) ⟶ G' := Over.homMk xe rfl
    have h₁ : eG xe' = R ≫ x₀ := Over.OverMorphism.ext ((heG _).trans h₀)
    have h₂ : eB (xe' ≫ q) = R ≫ b := by
      rw [← h]
      beta_reduce
      rw [← h₁, MulEquiv.symm_apply_apply]
    exact (Category.assoc _ _ _).symm.trans ((heB (xe' ≫ q)).symm.trans (congrArg (fun z => z.left) h₂))

end

theorem image_one_mul_inv : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (W : Type) [CommRing W] [Algebra V W] (x x' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G) (b b' : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ G)).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ ((1 : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W))) ⟶ a.B)).left) ∧ ((∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b).left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b').left) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x * x').left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b * b').left) ∧ (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of W)) (xe : Z ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (fstG _ e G).left = r ≫ (x⁻¹).left → xe ≫ (t.l e).Q.q.left ≫ a.b e = r ≫ (b⁻¹).left)) := by
  intro V _ _ _ A G _ _ s t a W _ _ x x' b b'
  have hG := fun e => isGrpPullback_pullback G (thick V (IsLocalRing.maximalIdeal V) e)
  have hB := fun e => (a.b_pb e).1
  have hq := fun e => (t.l e).Q.q_hom
  refine ⟨fun e Z r xe h => ?_, fun h₁ h₂ => ⟨fun e Z r xe h => ?_, fun e Z r xe h => ?_⟩⟩
  · obtain ⟨Y, R, Φ, e₁, -, -, -, k⟩ := exists_imageHom (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (hG e)
      (hB e) (t.l e).Q.q r xe _ h
    exact k 1 (by rw [e₁, MonObj.comp_one])
  · obtain ⟨Y, R, Φ, -, e₂, -, l, k⟩ := exists_imageHom (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (hG e)
      (hB e) (t.l e).Q.q r xe _ h
    exact k _ (by rw [e₂, l x b (h₁ e Z r), l x' b' (h₂ e Z r), MonObj.comp_mul])
  · obtain ⟨Y, R, Φ, -, -, e₃, l, k⟩ := exists_imageHom (T := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))) (hG e)
      (hB e) (t.l e).Q.q r xe _ h
    exact k _ (by rw [e₃, l x b (h₁ e Z r), GrpObj.comp_inv])

end GlobalTheory.UU
