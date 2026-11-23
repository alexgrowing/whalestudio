import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeDescendsAlongEtaleIsogeny
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPwOfAffineLoci
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubeProjectiveAbelianSchemeAffineBaseStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibreStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRingStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsGenerateSquareBundleStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAffineOpenNonzeroLocusOfFibrewiseAmpleStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FibreAmple

theorem pw_pw_natCast {X : Scheme.{0}} (H : LB X) (a b : ℕ) :
    pw (pw H a) b = pw H ((a * b : ℕ) : ℤ) := by
  rw [Nat.cast_mul]
  exact congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X))
    (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem triv_theta_pull {S S' : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (g : S' ⟶ S)
    (H : LB A.left) (h : Triv (Theta ((Over.pullback g).obj A) (H.pull (pullback.fst A.hom g)))) :
    Triv ((Theta A H).pull (pullback.fst (G3 A).hom g)) := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨u, hu⟩ := GlobalTheory.CubeDescent.exists_gen_comp H (pullback.fst A.hom g) _ _ t ht
  let B := (Over.pullback g).obj A
  let T : Over S' := Over.mk (pullback.snd (G3 A).hom g)
  have hG := isGrpPullback_pullback A g
  let y : Fin 3 → (T ⟶ B) := fun i => Over.homMk
    (pullback.lift (pullback.fst (G3 A).hom g ≫ (x3 A i).left) (pullback.snd (G3 A).hom g)
      (by rw [Category.assoc, Over.w, pullback.condition])) (pullback.lift_snd _ _ _)
  let r : T ⟶ G3 B := lift (y 0) (lift (y 1) (y 2))
  have hr : ∀ i, r ≫ x3 B i = y i := fun i => by fin_cases i <;> simp [r, x3]
  let U : Over.mk (T.hom ≫ g) ⟶ G3 A := Over.homMk (pullback.fst (G3 A).hom g) pullback.condition
  have key : ∀ I : Finset (Fin 3), r.left ≫ (psum B (x3 B) I).left ≫ pullback.fst A.hom g =
      pullback.fst (G3 A).hom g ≫ (psum A (x3 A) I).left := fun I => by
    have e₁ : r ≫ psum B (x3 B) I = psum B y I :=
      (psum_hom (preHom r) (x3 B) I).trans (congrArg (fun z => psum B z I) (funext hr))
    have e₂ := psum_push hG y (x3 A) U (fun i => Over.OverMorphism.ext (pullback.lift_fst _ _ _)) I
    rw [← Category.assoc, ← Over.comp_left, e₁]
    exact e₂
  refine (CubeGen.triv_pull_iff H (thφ A (x3 A)) thε _).2 ?_
  have e : (fun k => pullback.fst (G3 A).hom g ≫ thφ A (x3 A) k) =
      fun k => r.left ≫ thφ B (x3 B) k ≫ pullback.fst A.hom g := funext fun k => (key k.down).symm
  unfold CubeGen.TrivAt
  rw [e]
  exact ⟨_, DVR.pullGen_isGen _ _ _ u hu r.left⟩

theorem exists_ne_zero {X : Scheme.{0}} [Nonempty X] {N : LB X} {I : Type} (s : I → LB.Sec N)
    (h : ⨆ i, Out.nonzeroLocus (s i) = ⊤) : ∃ (σ : LB.Sec N) (k : N.ι), σ.f k ≠ 0 := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hx : x ∈ ⨆ i, Out.nonzeroLocus (s i) := by rw [h]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  refine ⟨s i, k, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hk
  exact hk

theorem relAmple_of_fibres : Out.Laws → ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.RelAmple (Over.mk (pullback.snd A.hom (spMap (algebraMap O K)))) (M.pull (pullback.fst A.hom (spMap (algebraMap O K)))) → Out.RelAmple (Over.mk (pullback.snd A.hom (spMap (IsLocalRing.residue O)))) (M.pull (pullback.fst A.hom (spMap (IsLocalRing.residue O)))) → Out.RelAmple A M := by
  intro hL O K _ _ _ _ _ _ _ _ A _ hA M hM hK hk
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hB := CubeGen.isAb_baseChange hA (spMap (algebraMap O K))
  obtain ⟨d, hd, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K _ _ (LB.isLB_pull hM _)).1 hK
  have hH := isLB_pw hM d
  have hproj : IsProjBy ((Over.pullback (spMap (algebraMap O K))).obj A).hom :=
    ⟨_, isLB_pw (LB.isLB_pull hM _) _, n, s, hs⟩
  have cK := triv_theta_pull A _ (pw M d)
    (GlobalTheory.T.theorem_of_cube_projective_abelianScheme_affineBase hL K _ hB hproj _ (LB.isLB_pull hH (pullback.fst A.hom (spMap (algebraMap O K)))))
  have s₂ : Smooth (A ⊗ A).hom := by
    change Smooth (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have p₂ : IsProper (A ⊗ A).hom := by
    change IsProper (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have c₂ : GeometricallyConnected (A ⊗ A).hom := by
    change GeometricallyConnected (pullback.fst A.hom A.hom ≫ A.hom)
    exact GeometricallyConnected.comp _ _
  have s₃ : Smooth (G3 A).hom := by
    change Smooth (pullback.fst A.hom (A ⊗ A).hom ≫ A.hom); infer_instance
  have p₃ : IsProper (G3 A).hom := by
    change IsProper (pullback.fst A.hom (A ⊗ A).hom ≫ A.hom); infer_instance
  have c₃ : GeometricallyConnected (G3 A).hom := by
    change GeometricallyConnected (pullback.fst A.hom (A ⊗ A).hom ≫ A.hom)
    exact GeometricallyConnected.comp _ _
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have cube : Triv (Theta A (pw M d)) :=
    GlobalTheory.T.generator_extends_from_genericFibre_valuationRing O K _ _ (G3 A).hom _ _ (IsPullback.of_hasPullback _ _) s₃ inferInstance (gi _ _ _ s₃ c₃) _
      (LB.isLB_linComb hH _ _) cK
  have ne : Nonempty ((Over.pullback (spMap (algebraMap O K))).obj A).left :=
    ⟨(η[(Over.pullback (spMap (algebraMap O K))).obj A]).left (default : PrimeSpectrum K)⟩
  have hσ : ∃ (σ : LB.Sec ((pw M d).pull (pullback.fst A.hom (spMap (algebraMap O K))))) (k : _), σ.f k ≠ 0 := by
    have := @exists_ne_zero _ ne _ _ s hs.1
    rw [GlobalTheory.TrivLocus.pull_pw]
    exact this
  obtain ⟨σ, hσ⟩ := hσ
  obtain ⟨-, t, -, -, ht⟩ := GlobalTheory.T.exists_sec_nonzero_on_special_fibre_extending_smul O K _ _ A.hom _ _ (IsPullback.of_hasPullback _ _) hA.smooth
    inferInstance (gi _ _ _ hA.smooth hA.geomConnected) _ hH σ hσ
  have hu := GlobalTheory.T.exists_sections_generate_square_bundle O K A hA _ hH cube t ht
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, pw_pw_natCast] at hu
  obtain ⟨m, u, hu⟩ := hu
  have aff := GlobalTheory.T.isAffineOpen_nonzeroLocus_of_fibrewise_ample O _ A.hom M (d * 2) m u (by omega) hA.proper hM hu (fun q hq => by
    by_cases h0 : q = ⊥
    · exact ⟨K, inferInstance, algebraMap O K,
        h0 ▸ (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective O K), hK⟩
    · exact ⟨_, inferInstance, IsLocalRing.residue O,
        IsLocalRing.ker_residue.trans (IsLocalRing.eq_maximalIdeal (hq.isMaximal h0)).symm, hk⟩)
  obtain ⟨e, he, hv⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw_of_affine_loci O _ A.hom _ m u (isLB_pw hM _) hu aff
  rw [pw_pw_natCast] at hv
  exact (GlobalTheory.Unif.relAmple_iff_veryAmpleBy O A M hM).2 ⟨d * 2 * e, Nat.mul_pos (by omega) he, hv⟩

end GlobalTheory.FibreAmple
