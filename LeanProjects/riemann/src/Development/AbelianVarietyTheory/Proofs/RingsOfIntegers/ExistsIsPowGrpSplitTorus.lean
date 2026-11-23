import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace SplitTorusPow

variable {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']

noncomputable def torusMap (S : Scheme.{0}) (φ : X →+ X') : splitTorus S X' ⟶ splitTorus S X :=
  (splitTorusPointsEquiv S X (splitTorus S X')).symm
    ((splitTorusPointsEquiv S X' (splitTorus S X') (𝟙 _)).comp (AddMonoidHom.toMultiplicative φ))

theorem torusMap_char (φ : X →+ X') (χ : X) :
    (torusMap S φ).left.appTop.hom (charUnit S X χ).val = (charUnit S X' (φ χ)).val := by
  rw [← splitTorusPointsEquiv_val, torusMap, MulEquiv.apply_symm_apply]
  change (splitTorusPointsEquiv S X' (splitTorus S X') (𝟙 _) (Multiplicative.ofAdd (φ χ))).val = _
  rw [splitTorusPointsEquiv_val]
  simp

theorem points_comp_torusMap (φ : X →+ X') {Z : Over S} (t : Z ⟶ splitTorus S X') :
    splitTorusPointsEquiv S X Z (t ≫ torusMap S φ) =
      (splitTorusPointsEquiv S X' Z t).comp (AddMonoidHom.toMultiplicative φ) := by
  refine MonoidHom.ext fun χ => Units.ext ?_
  change (splitTorusPointsEquiv S X Z (t ≫ torusMap S φ) (Multiplicative.ofAdd χ.toAdd)).val =
    (splitTorusPointsEquiv S X' Z t (Multiplicative.ofAdd (φ χ.toAdd))).val
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, ← torusMap_char, Over.comp_left,
    Scheme.Hom.comp_appTop]
  rfl

theorem mul_comp_torusMap (φ : X →+ X') {Z : Over S} (a b : Z ⟶ splitTorus S X') :
    (a * b) ≫ torusMap S φ = (a ≫ torusMap S φ) * (b ≫ torusMap S φ) := by
  apply (splitTorusPointsEquiv S X Z).injective
  rw [map_mul, points_comp_torusMap, points_comp_torusMap, points_comp_torusMap, map_mul,
    MonoidHom.mul_comp]

theorem isMonHom_torusMap (φ : X →+ X') : IsMonHom (torusMap S φ) where
  one_hom := by
    have h : (1 : 𝟙_ (Over S) ⟶ splitTorus S X') ≫ torusMap S φ = 1 := by
      apply (splitTorusPointsEquiv S X _).injective
      rw [points_comp_torusMap, map_one, map_one, MonoidHom.one_comp]
    simpa [Hom.one_def] using h
  mul_hom := by
    have h := mul_comp_torusMap (S := S) φ (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]
    congr 1

def incl {j : ℕ} (xe : X' ≃+ (Fin j → X)) (i : Fin j) : X →+ X' :=
  xe.symm.toAddMonoidHom.comp (AddMonoidHom.single (fun _ => X) i)

theorem incl_apply {j : ℕ} (xe : X' ≃+ (Fin j → X)) (i : Fin j) (χ : X) :
    incl xe i χ = xe.symm (Pi.single i χ) := rfl

theorem sum_incl {j : ℕ} (xe : X' ≃+ (Fin j → X)) (x : X') : ∑ i, incl xe i (xe x i) = x := by
  simp only [incl_apply]
  rw [← map_sum, Finset.univ_sum_single, AddEquiv.symm_apply_apply]

theorem hom_ext_incl {M : Type} [CommGroup M] {j : ℕ} (xe : X' ≃+ (Fin j → X))
    {u v : Multiplicative X' →* M}
    (h : ∀ i, u.comp (AddMonoidHom.toMultiplicative (incl xe i)) =
      v.comp (AddMonoidHom.toMultiplicative (incl xe i))) : u = v := by
  refine MonoidHom.ext fun x => ?_
  have e : x = ∏ i, Multiplicative.ofAdd (incl xe i (xe x.toAdd i)) := by
    rw [← ofAdd_sum, sum_incl]; rfl
  rw [e, map_prod, map_prod]
  exact Finset.prod_congr rfl fun i _ =>
    DFunLike.congr_fun (h i) (Multiplicative.ofAdd (xe x.toAdd i))

theorem exists_hom_incl {M : Type} [CommGroup M] {j : ℕ} (xe : X' ≃+ (Fin j → X))
    (w : Fin j → (Multiplicative X →* M)) :
    ∃ u : Multiplicative X' →* M,
      ∀ i, u.comp (AddMonoidHom.toMultiplicative (incl xe i)) = w i := by
  refine ⟨∏ i, (w i).comp (AddMonoidHom.toMultiplicative
    ((Pi.evalAddMonoidHom (fun _ => X) i).comp xe.toAddMonoidHom)), fun i => ?_⟩
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.comp_apply, MonoidHom.finset_prod_apply, Finset.prod_eq_single i]
  · simp [incl_apply]
  · intro k _ hk
    simp [incl_apply, Pi.single_eq_of_ne hk]
  · simp

noncomputable def isPowGrp (S : Scheme.{0}) {j : ℕ} (xe : X' ≃+ (Fin j → X)) :
    IsPowGrp (splitTorus S X') (splitTorus S X) j where
  pr i := torusMap S (incl xe i)
  hom i := isMonHom_torusMap _
  lim := mkFanLimit _
    (fun s => (splitTorusPointsEquiv S X' s.pt).symm
      (exists_hom_incl xe fun i => splitTorusPointsEquiv S X s.pt (s.proj i)).choose)
    (fun s i => by
      apply (splitTorusPointsEquiv S X s.pt).injective
      refine (points_comp_torusMap (incl xe i) _).trans ?_
      rw [MulEquiv.apply_symm_apply]
      exact (exists_hom_incl xe fun i => splitTorusPointsEquiv S X s.pt (s.proj i)).choose_spec i)
    (fun s m hm => by
      apply (splitTorusPointsEquiv S X' s.pt).injective
      rw [MulEquiv.apply_symm_apply]
      refine hom_ext_incl xe fun i => ?_
      rw [(exists_hom_incl xe fun i => splitTorusPointsEquiv S X s.pt (s.proj i)).choose_spec i,
        ← hm i]
      exact (points_comp_torusMap (incl xe i) m).symm)

end SplitTorusPow

theorem exists_isPowGrp_splitTorus : ∀ (S : Scheme.{0}) (X X' : Type) [AddCommGroup X] [AddCommGroup X'] (j : ℕ) (xe : X' ≃+ (Fin j → X)), ∃ p : IsPowGrp (splitTorus S X') (splitTorus S X) j, ∀ (i : Fin j) (χ : X), res (fun x _ => show (p.pr i).left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial) (pullU (p.pr i).left ⊤ (charUnit S X χ)) = charUnit S X' (xe.symm (Pi.single i χ)) := by
  intro S X X' _ _ j xe
  refine ⟨SplitTorusPow.isPowGrp S xe, fun i χ => ?_⟩
  ext1
  rw [← SplitTorusPow.incl_apply, ← SplitTorusPow.torusMap_char]
  change ((splitTorus S X').left.presheaf.map (𝟙 _)).hom
    ((SplitTorusPow.torusMap S (SplitTorusPow.incl xe i)).left.appTop.hom (charUnit S X χ).val) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

end GlobalTheory
