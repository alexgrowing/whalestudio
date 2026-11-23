import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ThickeningDetermines in

theorem sec_eq_zero_of_thickenings_of_section (R : Type) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥) (H : Over (Spec (CommRingCat.of R)))
    [Smooth H.hom] [GeometricallyConnected H.hom] (e : 𝟙_ _ ⟶ H) (N : LB H.left) (hN : N.IsLB)
    (s : LB.Sec N) (hs : ∀ (n : ℕ) j, ((fstG I n H).left.app _).hom (s.f j) = 0) (j) :
    s.f j = 0 := by
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres H.hom
  have key := isIso_of_isClosedImmersion_of_thickenings R I hI H e (fun p ↦ inferInstance)
  refine eq_zero_of_secIdeal_eq_bot hN s ?_ j
  have := key _ (secIdeal hN s).subschemeι fun n ↦ by
    have : IsClosedImmersion (thick R I n) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : QuasiCompact (fstG I n H).left :=
      inferInstanceAs (QuasiCompact (pullback.fst H.hom (thick R I n)))
    exact ⟨IsClosedImmersion.lift _ (fstG I n H).left (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact secIdeal_le_ker hN s _ (hs n)), IsClosedImmersion.lift_fac _ _ _⟩
  rw [← Scheme.IdealSheafData.ker_subschemeι (secIdeal hN s)]
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.1 this

theorem app_sec_eq_zero_of_sval {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type}
    [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (d : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y)
    (h : ∀ (z : Z) (J), Good L z J → sval d r z J = 0) (j) : (r.app _).hom (d.f j) = 0 := by
  apply TopCat.Presheaf.section_ext Z.sheaf _
  intro z hz
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have e := sec_trans d r z (j := j) hz (Good.mem hI φ r)
  have e' : gs r z (LB.wchart L φ j) (d.f j) = 0 :=
    e.trans ((congrArg _ (h z I hI)).trans (mul_zero _))
  exact ((gs_eq r z _ hz _).symm.trans e').trans (map_zero _).symm

theorem sec_eq_zero_of_sval_finite_level : ∀ (R : Type) [CommRing R] (I : Ideal R) (T B : Over (Spec (CommRingCat.of R))) [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] [GrpObj B] [Smooth B.hom] [GeometricallyConnected B.hom], (∀ r ∈ I, scal T.hom r ∈ Ideal.jacobson (⊥ : Ideal Γ(T.left, ⊤))) → ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → ((T ⊗ B).left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ (T ⊗ B).hom) → ∀ (z : Z) (J), Good L z J → sval d r z J = 0) → ∀ j, d.f j = 0 := by
  intro R _ I T B _ _ _ _ _ hI X L hL K _ φ ε d hd j
  let ψ : CommRingCat.of R ⟶ Γ(T.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ T.hom.appTop
  have hψ : T.left.isoSpec.hom ≫ Spec.map ψ = T.hom := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  let H : Over (Spec (CommRingCat.of Γ(T.left, ⊤))) :=
    Over.mk (pullback.fst T.hom B.hom ≫ T.left.isoSpec.hom)
  have : Smooth H.hom := inferInstanceAs (Smooth (pullback.fst T.hom B.hom ≫ T.left.isoSpec.hom))
  have : GeometricallyConnected H.hom :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_iso (IsPullback.of_hasPullback T.hom B.hom).flip (Iso.refl _) (Iso.refl _)
        T.left.isoSpec (Iso.refl _) (fst' := pullback.snd T.hom B.hom) (snd' := H.hom)
        (f' := B.hom) (g' := Spec.map ψ) (by simp) (Category.id_comp _).symm (by simp)
        (by simp [hψ])) ‹GeometricallyConnected B.hom›
  let σ : T ⟶ T ⊗ B := lift (𝟙 T) (toUnit T ≫ η[B])
  have hσ : σ.left ≫ pullback.fst T.hom B.hom = 𝟙 _ :=
    congrArg CommaMorphism.left (lift_fst (𝟙 T) (toUnit T ≫ η[B]))
  let e : 𝟙_ _ ⟶ H := Over.homMk (T.left.isoSpec.inv ≫ σ.left) (by
    change (T.left.isoSpec.inv ≫ σ.left) ≫ pullback.fst T.hom B.hom ≫ T.left.isoSpec.hom = 𝟙 _
    rw [Category.assoc, reassoc_of% hσ, Iso.inv_hom_id])
  refine sec_eq_zero_of_thickenings_of_section Γ(T.left, ⊤) (I.map ψ.hom)
    (Ideal.map_le_iff_le_comap.2 hI) H e (LB.LinComb L φ ε) (DVR.linComb_isLB L hL φ ε) d
    (fun n j ↦ app_sec_eq_zero_of_sval hL d _ (hd n _ _ ⟨pullback.snd H.hom (thick _ (I.map ψ.hom) n) ≫
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((I.map ψ.hom) ^ (n + 1)) ψ.hom
          (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map))), ?_⟩) j) j
  change _ = pullback.fst H.hom (thick _ (I.map ψ.hom) n) ≫ pullback.fst T.hom B.hom ≫ T.hom
  have h1 : pullback.fst T.hom B.hom ≫ T.hom = H.hom ≫ Spec.map ψ :=
    (congrArg (pullback.fst T.hom B.hom ≫ ·) hψ.symm).trans (Category.assoc _ _ _).symm
  rw [h1, pullback.condition_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  rfl

end GlobalTheory
