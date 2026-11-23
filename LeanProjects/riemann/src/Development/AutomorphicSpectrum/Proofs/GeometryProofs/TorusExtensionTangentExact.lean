import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieExact

theorem ker_fst_isNilpotent {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra R (DualNumber A)] (π : DualNumber A →ₐ[R] A)
    (h : ∀ b, π b = TrivSqZeroExt.fst b) : IsNilpotent (RingHom.ker (π : DualNumber A →+* A)) := by
  refine ⟨2, ?_⟩
  rw [pow_two]
  refine le_bot_iff.mp (Ideal.mul_le.mpr fun a ha b hb => ?_)
  have ha' : TrivSqZeroExt.fst a = 0 := by rw [← h]; exact ha
  have hb' : TrivSqZeroExt.fst b = 0 := by rw [← h]; exact hb
  have : a * b = 0 := by
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, ha', hb']
  simp [this]

theorem exists_lift_dual {X S : Scheme.{0}} (f : X ⟶ S) [Smooth f] (A : Type) [Field A]
    (s : Spec (CommRingCat.of (DualNumber A)) ⟶ S) (x₀ : Spec (CommRingCat.of A) ⟶ X)
    (h : x₀ ≫ f = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ s) :
    ∃ x : Spec (CommRingCat.of (DualNumber A)) ⟶ X,
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ x = x₀ ∧ x ≫ f = s := by
  let π : CommRingCat.of (DualNumber A) ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom
  have hloc : IsLocalHom π.hom := ⟨fun b hb => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr hb⟩
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    GlobalTheory.exists_isAffineOpen_pair f (x₀ (IsLocalRing.closedPoint (CommRingCat.of A))) (O := ⊤) trivial
  refine GlobalTheory.exists_lift_of_smooth_of_isAffineOpen f hU hV hVU π s x₀ h
    (GlobalTheory.range_subset_opens_of_isLocalRing s ?_) (GlobalTheory.range_subset_opens_of_isLocalRing x₀ hxV) ?_
  · have e : f (x₀ (IsLocalRing.closedPoint (CommRingCat.of A))) =
        s (Spec.map π (IsLocalRing.closedPoint (CommRingCat.of A))) :=
      congr($h (IsLocalRing.closedPoint (CommRingCat.of A)))
    rw [← Spec_closedPoint (f := π), ← e]
    exact hVU hxV
  · intro R B _ _ _ _ _ _ π' hπ' φ
    have hsurj : Function.Surjective π' := fun a => ⟨TrivSqZeroExt.inl a, by rw [hπ']; rfl⟩
    have hnil := ker_fst_isNilpotent π' (fun b => by rw [hπ']; rfl)
    exact ⟨Algebra.FormallySmooth.liftOfSurjective φ π' hsurj hnil,
      Algebra.FormallySmooth.comp_liftOfSurjective φ π' hsurj hnil⟩

variable {S : Scheme.{0}}

theorem one_comp_hom {M N T : Over S} [GrpObj M] [GrpObj N] (f : M ⟶ N) [IsMonHom f] :
    (1 : T ⟶ M) ≫ f = 1 := by
  simp [Hom.one_def, IsMonHom.one_hom]

noncomputable def zeroSec {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) : Over.mk x ⟶ epsAt x :=
  Over.homMk (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom)) (by
    simp only [Over.mk_left, Over.mk_hom, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
      ext r; rfl
    rw [this]; simp)

theorem isTanAt_iff {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (G : Over S) [GrpObj G]
    (v : epsAt x ⟶ G) : IsTanAt G x v ↔ zeroSec x ≫ v = 1 :=
  ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg (fun t : Over.mk x ⟶ G => t.left) h⟩

end GlobalTheory.CompanionTheory.Ar.LieExact

open GlobalTheory.CompanionTheory.Ar.LieExact in

theorem GlobalTheory.CompanionTheory.Ar.LieExact.lie_exact_field : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] (τ : TorusExtension G), letI := τ.addCommGroup; letI := τ.grpB; ∀ (A : Type) [Field A] (c : K →+* A), (∀ v : epsAt (spMap c) ⟶ G, IsTanAt G _ v → (v ≫ τ.q = 1 ↔ ∃ w : epsAt (spMap c) ⟶ splitTorus (Sp K) τ.X, IsTanAt _ _ w ∧ w ≫ τ.i = v)) ∧ ∀ w : epsAt (spMap c) ⟶ τ.B, IsTanAt τ.B _ w → ∃ v : epsAt (spMap c) ⟶ G, IsTanAt G _ v ∧ v ≫ τ.q = w := by
  intro K _ G _ τ
  letI := τ.addCommGroup
  letI := τ.grpB
  intro A _ c
  have hq : IsMonHom τ.q := τ.q_hom
  have hi : IsMonHom τ.i := τ.i_hom
  refine ⟨fun v hv => ⟨fun h => ?_, ?_⟩, fun w hw => ?_⟩
  · have sq : v ≫ τ.q = toUnit _ ≫ η := h.trans Hom.one_def
    refine ⟨τ.isKernel.lift v (toUnit _) sq, ?_, τ.isKernel.lift_fst _ _ _⟩
    rw [isTanAt_iff]
    refine τ.isKernel.hom_ext ?_ (toUnit_unique _ _)
    rw [Category.assoc, τ.isKernel.lift_fst, one_comp_hom, (isTanAt_iff _ _ _).mp hv]
  · rintro ⟨w, -, rfl⟩
    rw [Category.assoc, τ.isKernel.w, ← Category.assoc, toUnit_unique (w ≫ toUnit _) (toUnit _),
      Hom.one_def]
  · obtain ⟨hs, -⟩ := GlobalTheory.torusExtension_smooth_geometricallyConnected G τ
    obtain ⟨x, hx1, hx2⟩ := exists_lift_dual τ.q.left A w.left
      (1 : Over.mk (spMap c) ⟶ G).left (by
        have h1 : ((1 : Over.mk (spMap c) ⟶ G) ≫ τ.q).left = (1 : Over.mk (spMap c) ⟶ τ.B).left := by
          rw [one_comp_hom]
        rw [Over.comp_left] at h1
        exact h1.trans hw.symm)
    refine ⟨Over.homMk x ?_, hx1, Over.OverMorphism.ext hx2⟩
    rw [← Over.w τ.q, ← Category.assoc, hx2, Over.w w]
