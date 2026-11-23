import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIsGenTranslDiffComp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InKIffTrivialTwist
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeTranslationKernel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.KCriterion

theorem mono_of_unramified_of_geometric_points {X Y : Scheme.{0}} (f : X ⟶ Y) [FormallyUnramified f]
    [LocallyOfFiniteType f]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ X), y ≫ f = y' ≫ f → y = y') : Mono f := by
  have hs : Surjective (pullback.diagonal f) := ⟨fun z => by
    let κ : Type := (pullback f f).residueField z
    let y : Sp (AlgebraicClosure κ) ⟶ pullback f f :=
      spMap (algebraMap κ (AlgebraicClosure κ)) ≫ (pullback f f).fromSpecResidueField z
    have e := h _ (y ≫ pullback.fst f f) (y ≫ pullback.snd f f)
      ((Category.assoc _ _ _).trans ((congrArg _ pullback.condition).trans (Category.assoc _ _ _).symm))
    have e' : (y ≫ pullback.fst f f) ≫ pullback.diagonal f = y := by
      refine pullback.hom_ext ?_ ?_
      · simp
      · simp [e]
    exact ⟨(y ≫ pullback.fst f f) (IsLocalRing.closedPoint _),
      (congrArg (fun q => q (IsLocalRing.closedPoint _)) e').trans (Scheme.fromSpecResidueField_apply z _)⟩⟩
  have : IsIso (pullback.diagonal f) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hs⟩
  exact (pullback.isIso_diagonal_iff f).1 this

theorem triv_of_inK_local {S : Scheme.{0}} {A : Over S} [GrpObj A] {M : LB A.left} {K : Type} [CommRing K]
    [IsLocalRing K] {t : Sp K ⟶ S} {x : Over.mk t ⟶ A} (hx : InK A M x) : Triv (Out.translDiff A M x) := by
  obtain ⟨V, hp, c, hc⟩ := hx (IsLocalRing.closedPoint K)
  have hV : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hp
  have := exists_isGen_translDiff_comp A M x (𝟙 _) V (fun q => hV.ge trivial) c hc
  rwa [Category.id_comp] at this

theorem kTriv_of_points_of_tangents : Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsProjBy A.hom → ∀ M : LB A.left, M.IsLB → (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K], (∀ x : specO R K ⟶ A, Triv (Out.translDiff A M x) → x = 1) ∧ ∀ x : specO R (DualNumber K) ⟶ A, ptMap (TrivSqZeroExt.fstHom R K K) ≫ x = 1 → Triv (Out.translDiff A M x) → x = 1) → Out.KTriv A M := by
  intro hL R _ A _ _ hA hP M hM hK
  obtain ⟨hO, -, hT⟩ := TrivTwist.inK_iff_trivial_twist _ A M hM
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hL.globalFns R A hA hP M (pw M 0) hM hO
  have hrep : ∀ (T : Over (Sp R)) (x : T ⟶ A), InK A M x ↔ ∃ y : T ⟶ H, y ≫ j = x :=
    fun T x => (hT _ rfl T x).trans (hH T x)
  have := hA.proper
  have hft : LocallyOfFiniteType H.hom := by rw [← Over.w j]; infer_instance
  have hpt : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (y : Over.mk t ⟶ H), y ≫ j = 1 := by
    intro k _ _ t
    obtain ⟨φ, rfl⟩ := Spec.map_surjective t
    let _ : Algebra R k := φ.hom.toAlgebra
    exact fun y => (hK k).1 (y ≫ j) (triv_of_inK_local ((hrep _ _).2 ⟨y, rfl⟩))
  have htan : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R)
      (y : Over.mk (TangentCrit.dualBase k ≫ t) ⟶ H), y ≫ j = 1 := by
    intro k _ _ t
    obtain ⟨φ, rfl⟩ := Spec.map_surjective t
    let _ : Algebra R k := φ.hom.toAlgebra
    have e : TangentCrit.dualBase k ≫ Spec.map φ = spMap (algebraMap R (DualNumber k)) :=
      (Spec.map_comp _ _).symm
    rw [e]
    intro y
    refine (hK k).2 (y ≫ j) ?_ (triv_of_inK_local ((hrep _ _).2 ⟨y, rfl⟩))
    rw [← Category.assoc]
    exact hpt k _ _
  have hext : ∀ {T : Scheme.{0}} {t : T ⟶ Sp R}, (∀ y : Over.mk t ⟶ H, y ≫ j = 1) →
      ∀ w w' : T ⟶ H.left, w ≫ H.hom = t → w' ≫ H.hom = t → w = w' := fun h w w' e e' =>
    (cancel_mono j.left).1 (congrArg (fun q => q.left)
      ((h (Over.homMk w e)).trans (h (Over.homMk w' e')).symm))
  have hu : FormallyUnramified H.hom :=
    TangentCrit.formallyUnramified_of_tangent H.hom fun k _ _ w hw =>
      hext (htan k (TangentCrit.dualPt k ≫ w ≫ H.hom)) _ _ hw (by simp only [Category.assoc])
  have hm : Mono H.hom := mono_of_unramified_of_geometric_points H.hom fun k _ _ y y' e =>
    hext (hpt k (y' ≫ H.hom)) _ _ e rfl
  refine kTriv_iff_forall.2 fun T x hx => ?_
  obtain ⟨y, rfl⟩ := (hrep T x).1 hx
  obtain ⟨y', hy'⟩ := (hrep T 1).1 (inK_one hM T)
  have : y = y' := Over.OverMorphism.ext ((cancel_mono H.hom).1 ((Over.w y).trans (Over.w y').symm))
  rw [this, hy']

end GlobalTheory.KCriterion
