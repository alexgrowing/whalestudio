import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianDeRhamStructure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CommAlgFunctorCohomologyTwoEqZeroOfIsInitial

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.AbelianDeRhamStructure.Test

variable {R : Type} [CommRing R]

theorem isAb_sq {A : Over (Sp R)} [GrpObj A] (hA : IsAbelianScheme A) : IsAbelianScheme (A ⊗ A) := by
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rw [Over.tensorObj_hom, Limits.pullback.condition]
    infer_instance
  · rw [Over.tensorObj_hom, Limits.pullback.condition]
    infer_instance
  · rw [Over.tensorObj_hom, Limits.pullback.condition]
    exact GeometricallyConnected.comp _ _

theorem pull_one {Y A : Over (Sp R)} [GrpObj A] (c : FirstDeRham (A.hom ≫ 𝟙 _)) :
    pullOver (dp0 R) (𝟙 _) (1 : Y ⟶ A) c = 0 := by
  haveI : IsIso ((𝟙_ (Over (Sp R))).hom ≫ 𝟙 _) := inferInstanceAs (IsIso (𝟙 (Sp R) ≫ 𝟙 _))
  rw [Hom.one_def, ← pullOver_pullOver, firstDeRham_base_eq_zero _ (pullOver (dp0 R) (𝟙 _) η[A] c), map_zero]

theorem pull_id {A : Over (Sp R)} (c : FirstDeRham (A.hom ≫ 𝟙 _)) :
    pullOver (dp0 R) (𝟙 _) (𝟙 A) c = c := IsMor.pullCohomologyOne_id _ _

theorem allPrim (H : AbelianDeRhamFree) {A : Over (Sp R)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) : AllPrim (dp0 R) (𝟙 _) A := by
  have hg2 : SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
    have : SmoothOfRelativeDimension g (Limits.pullback.fst A.hom A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback A.hom A.hom).flip hg
    rw [Over.tensorObj_hom]
    exact smoothOfRelativeDimension_comp g g _ _
  obtain ⟨f1, p1, r1, -⟩ := H R A g hA hg
  obtain ⟨f2, p2, r2, -⟩ := H R (A ⊗ A) (g + g) (isAb_sq hA) hg2
  let r : FirstDeRham ((A ⊗ A).hom ≫ 𝟙 _) →ₗ[R] FirstDeRham (A.hom ≫ 𝟙 _) × FirstDeRham (A.hom ≫ 𝟙 _) :=
    (pullOver (dp0 R) (𝟙 _) (lift (𝟙 A) 1)).prod (pullOver (dp0 R) (𝟙 _) (lift 1 (𝟙 A)))
  have hv : ∀ x, r x = (pullOver (dp0 R) (𝟙 _) (lift (𝟙 A) 1) x, pullOver (dp0 R) (𝟙 _) (lift 1 (𝟙 A)) x) :=
    fun _ ↦ rfl
  have hr : ∀ a b, r (pullOver (dp0 R) (𝟙 _) (fst A A) a + pullOver (dp0 R) (𝟙 _) (snd A A) b) = (a, b) := by
    intro a b
    rw [hv]
    simp only [map_add, pullOver_pullOver, lift_fst, lift_snd, pull_one,
      pull_id, add_zero, zero_add]
  have hs : Function.Surjective r := fun x ↦ ⟨_, hr x.1 x.2⟩
  have hb : Function.Bijective r :=
    Module.bijective_of_surjective_of_rankAtStalk_eq hs fun m _ ↦ by
      rw [Module.rankAtStalk_prod, Pi.add_apply, r1, r2]; ring
  refine eq_top_iff.2 fun c _ ↦ (mem_prim_iff _ _ A c).2 (hb.1 ?_)
  rw [hr, hv]
  simp only [pullOver_pullOver, ← Hom.mul_def, _root_.mul_one, _root_.one_mul, pull_id]

theorem free_iff : AbelianDeRhamFree ↔ AbelianDeRham.Free :=
  ⟨fun H R _ A _ g hA hg ↦ ⟨allPrim H hA hg, H R A g hA hg⟩, fun H R _ A _ g hA hg ↦ (H R A g hA hg).2⟩

theorem of_abelianDeRham (H : AbelianDeRham) : AbelianDeRhamStructure :=
  ⟨free_iff.2 H.1, H.2.1, H.2.2.1⟩

theorem elliptic (H : AbelianDeRhamStructure) (k : Type) [Field k] (W : WeierstrassCurve k) [W.IsElliptic] :
    (∀ p : PrimeSpectrum k, Module.rankAtStalk (primDR (GlobalTheory.WeierstrassCurve.ellPolAV W).A) p = 2) ∧
    (∀ p : PrimeSpectrum k, Module.rankAtStalk (PrimitiveSubmodule (GlobalTheory.WeierstrassCurve.ellPolAV W).A) p = 1) ∧
    Module.finrank k (SecondDeRham ((GlobalTheory.WeierstrassCurve.ellPolAV W).A.hom ≫ 𝟙 _)) = 1 := by
  let P := GlobalTheory.WeierstrassCurve.ellPolAV W
  have hg : SmoothOfRelativeDimension 1 P.A.hom := P.smoothDim
  refine ⟨((free_iff.1 H.1).prim P.isAb hg).2.2, (H.2.1 k P.A 1 P.isAb hg).2.2.2.2, ?_⟩
  obtain ⟨f, p, r, e, -⟩ := H.1 k P.A 1 P.isAb hg
  have h2 : Module.finrank k (FirstDeRham (P.A.hom ≫ 𝟙 _)) = 2 := by
    have := r ⊥
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  rw [← e.finrank_eq, exteriorPower.finrank_eq, h2]
  rfl

theorem unit_baseChange (R' : Type) [CommRing R'] [Algebra R R']
    (φ : (𝟙_ (Over (Sp R'))).left ⟶ (𝟙_ (Over (Sp R))).left)
    (h : IsGrpPullback (𝟙_ (Over (Sp R'))) (𝟙_ (Over (Sp R))) (spMap (algebraMap R R')) φ) :
    (AbelianDeRham.bcMor h).IsBC ∧ PrimitiveSubmodule (𝟙_ (Over (Sp R'))) =
      Submodule.span R' ((AbelianDeRham.bcMor h).pull '' (PrimitiveSubmodule (𝟙_ (Over (Sp R))))) := by
  have : Subsingleton (primDR (𝟙_ (Over (Sp R)))) :=
    ⟨fun a b ↦ (primDR_unit a).trans (primDR_unit b).symm⟩
  have : Subsingleton (primDR (𝟙_ (Over (Sp R')))) :=
    ⟨fun a b ↦ (primDR_unit a).trans (primDR_unit b).symm⟩
  exact ⟨⟨fun a b _ ↦ Subsingleton.elim a b, fun c ↦ ⟨0, Subsingleton.elim _ _⟩⟩, Subsingleton.elim _ _⟩

end GlobalTheory.Published.AbelianDeRhamStructure.Test
