import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfLocallyRel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNegOriginSmoothLocus

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace WeierstrassCurve

theorem exists_point_equiv_smoothLocus {R : Type} [CommRing R] (W : WeierstrassCurve R)
    (U : (scheme W).Opens)
    (hU : ∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : IsUnimodularSol (W.map ρ) P),
      ⊤ ≤ ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P)
    (k : Type) [Field k] [Algebra R k] :
    ∃ c : (W.baseChange k).toProjective.Point ≃ (specOver R k ⟶ Over.mk (U.ι ≫ toSpec W)),
      ∀ p, (c p).left ≫ U.ι = (ofProjectivePoint W k p).left := by
  have hr : ∀ p, Set.range (ofProjectivePoint W k p).left ⊆ Set.range U.ι := by
    rintro @⟨⟨P⟩, hP⟩ _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (hU k (algebraMap R k) P (.of_nonsingular hP)).mpr hP (Set.mem_univ z)
  let c : (W.baseChange k).toProjective.Point → (specOver R k ⟶ Over.mk (U.ι ≫ toSpec W)) :=
    fun p => Over.homMk (IsOpenImmersion.lift U.ι _ (hr p))
      ((IsOpenImmersion.lift_fac_assoc U.ι _ (hr p) _).trans (Over.w (ofProjectivePoint W k p)))
  have hc : ∀ p, (c p).left ≫ U.ι = (ofProjectivePoint W k p).left := fun p =>
    IsOpenImmersion.lift_fac U.ι _ (hr p)
  refine ⟨Equiv.ofBijective c ⟨fun p q e => ?_, fun x => ?_⟩, hc⟩
  · refine ofProjectivePoint_injective W k (Over.OverMorphism.ext ?_)
    rw [← hc, ← hc, e]
  · obtain ⟨P, hP, e⟩ := exists_eq_ptHom W (algebraMap R k) (x.left ≫ U.ι)
      ((Category.assoc _ _ _).trans (Over.w x))
    have hns : (W.baseChange k).toProjective.Nonsingular P := (hU k _ P hP).mp (by
      rw [← e]
      intro y _
      exact (x.left y).2)
    refine ⟨⟨(WeierstrassCurve.Projective.nonsingularLift_iff P).mpr hns⟩,
      Over.OverMorphism.ext ?_⟩
    exact (cancel_mono U.ι).mp ((hc _).trans e.symm)

end WeierstrassCurve

open WeierstrassCurve in

theorem exists_grpObj_smoothLocus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (W : WeierstrassCurve R) (U : (GlobalTheory.WeierstrassCurve.scheme W).Opens), (∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P), ⊤ ≤ GlobalTheory.WeierstrassCurve.ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) → Smooth (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → GeometricallyIntegral (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W) → ∃ _ : GrpObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)), IsCommMonObj (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W)) ∧ (η[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.zero W ∧ (∀ (k : Type) [Field k] (ρ : R →+* k) (x y : Over.mk (Spec.map (CommRingCat.ofHom ρ)) ⟶ (Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))) (P Q : Fin 3 → k) (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P) (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) Q), x.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ P hP → y.left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ Q hQ → ∃ h : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.add P Q), (lift x y ≫ μ[(Over.mk (U.ι ≫ GlobalTheory.WeierstrassCurve.toSpec W))]).left ≫ U.ι = GlobalTheory.WeierstrassCurve.ptHom W ρ _ h) := by
  intro R _ _ _ W U hU hs hg
  classical
  obtain ⟨m, hm⟩ := exists_add_smoothLocus R W U hU hs hg
  obtain ⟨i, e, he, hi⟩ := exists_neg_origin_smoothLocus R W U hU
  let G : Over (Spec (.of R)) := Over.mk (U.ι ≫ toSpec W)
  have hG : IsIntegral (U : Scheme) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (U.ι ≫ toSpec W)
  have hN : IsLocallyNoetherian (U : Scheme) :=
    LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ toSpec W)
  have hG₁ : IsIntegral G.left := hG
  have hG₂ : IsIntegral (pullback (U.ι ≫ toSpec W) (U.ι ≫ toSpec W)) := inferInstance
  have hG₂' : IsIntegral (G ⊗ G).left := hG₂
  have hN₂ : IsLocallyNoetherian (G ⊗ G).left :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (U.ι ≫ toSpec W) (U.ι ≫ toSpec W))
  have hG₃ : IsIntegral ((G ⊗ G) ⊗ G).left := inferInstanceAs (IsIntegral
    (pullback (G ⊗ G).hom (U.ι ≫ toSpec W)))
  have hsep : IsSeparated G.hom := inferInstanceAs (IsSeparated (U.ι ≫ toSpec W))
  have H : ∀ (k : Type) [Field k] [Algebra R k], ∃ (M : Type) (_ : AddCommGroup M)
      (c : M ≃ (specOver R k ⟶ G)), toUnit _ ≫ e = c 0 ∧
        (∀ a b, lift (c a) (c b) ≫ m = c (a + b)) ∧ ∀ a, c a ≫ i = c (-a) := by
    intro k _ _
    obtain ⟨c, hc⟩ := exists_point_equiv_smoothLocus W U hU k
    refine ⟨_, inferInstance, c, ?_, ?_, ?_⟩
    · refine Over.OverMorphism.ext ((cancel_mono U.ι).mp ?_)
      rw [hc, ofProjectivePoint_zero, zeroOver_left]
      exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) he)
    · rintro @⟨⟨P⟩, hP⟩ @⟨⟨Q⟩, hQ⟩
      obtain ⟨h, e'⟩ := hm k (algebraMap R k) (c ⟨hP⟩) (c ⟨hQ⟩) P Q (.of_nonsingular hP)
        (.of_nonsingular hQ) (hc _) (hc _)
      refine Over.OverMorphism.ext ((cancel_mono U.ι).mp (e'.trans ?_))
      rw [hc]
      rfl
    · rintro @⟨⟨P⟩, hP⟩
      obtain ⟨h, e'⟩ := hi k (algebraMap R k) (c ⟨hP⟩) P (.of_nonsingular hP) (hc _)
      refine Over.OverMorphism.ext ((cancel_mono U.ι).mp (e'.trans ?_))
      rw [hc]
      rfl
  letI : GrpObj G := grpObjOfFieldPoints e m i H
  refine ⟨this, ⟨?_⟩, he, hm⟩
  refine over_hom_eq_iff_forall_field_algebra.mpr fun k _ _ x => ?_
  obtain ⟨M, _, c, h₀, h₁, h₂⟩ := H k
  obtain ⟨a, ha⟩ := c.surjective (x ≫ fst _ _)
  obtain ⟨b, hb⟩ := c.surjective (x ≫ snd _ _)
  obtain rfl : x = lift (c a) (c b) :=
    CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, ha]) (by rw [lift_snd, hb])
  change lift (c a) (c b) ≫ (β_ G G).hom ≫ m = lift (c a) (c b) ≫ m
  rw [lift_braiding_hom_assoc, h₁, h₁, add_comm]

end GlobalTheory
