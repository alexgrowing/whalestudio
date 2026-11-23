import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem stalkMap_bijective_of_flat_preimmersion {X Y : Scheme.{0}} (f : X ⟶ Y) [IsPreimmersion f] [Flat f] (x : X) :
    Function.Bijective (f.stalkMap x).hom := by
  refine ⟨?_, f.stalkMap_surjective x⟩
  have h := Flat.stalkMap f x
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)

theorem spMap_flat_preimmersion {O F : Type} [CommRing O] [Field F] (β : O →+* F) (hi : Function.Injective β)
    (hq : ∀ x : F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) : IsPreimmersion (spMap β) ∧ Flat (spMap β) := by
  haveI : IsDomain O := hi.isDomain β
  letI : Algebra O F := β.toAlgebra
  have hal : ∀ a : O, algebraMap O F a = β a := fun _ => rfl
  have hfr : IsLocalization (nonZeroDivisors O) F :=
    { map_units := fun y => by
        refine IsUnit.mk0 _ ?_
        rw [hal]
        exact fun h => nonZeroDivisors.ne_zero y.2 (hi (h.trans (map_zero β).symm))
      surj := fun z => by
        obtain ⟨a, b, hb, e⟩ := hq z
        have hb0 : b ≠ 0 := fun h => hb (by rw [h, map_zero])
        exact ⟨(a, ⟨b, mem_nonZeroDivisors_of_ne_zero hb0⟩), e⟩
      exists_of_eq := fun {x y} e => ⟨1, by rw [hi e]⟩ }
  refine ⟨IsPreimmersion.of_isLocalization (nonZeroDivisors O) (S := F), ?_⟩
  have hfl : Module.Flat O F := IsLocalization.flat F (nonZeroDivisors O)
  exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 hfl)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem j_flat_preimmersion {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) (hi : Function.Injective β) (hq : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) :
    IsPreimmersion Y.j ∧ Flat Y.j := by
  obtain ⟨h1, h2⟩ := spMap_flat_preimmersion β hi hq
  have h3 : IsPreimmersion (pullback.fst Y.s (spMap β)) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip h1
  have h4 : Flat (pullback.fst Y.s (spMap β)) :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback _ _).flip h2
  have := Y.jQ_open
  exact ⟨inferInstanceAs (IsPreimmersion (Y.jQ ≫ pullback.fst _ _)), inferInstanceAs (Flat (Y.jQ ≫ pullback.fst _ _))⟩

theorem cptOver_isOpen_isDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → ∃ U' : (Xo.XF c).Opens, (U' : Set (Xo.XF c)) = U ∧ ∀ p : Xo.XF c, p ∈ U → IsDomain ((Xo.XF c).presheaf.stalk p) := by
  intro E _ _ _ H D l Xo c O _ β Y U Z ⟨hi, hN, hq⟩
  obtain ⟨h1, h2⟩ := j_flat_preimmersion Y hi hq
  have hP : IsProper Y.s := GlobalTheory.SchemeWords.isProper_of_isProjOver Y.proj
  have hLN : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have ho := isOpen_closure_genPt (Z.ξ₀ ≫ Y.j) Z.gen
  have hU : U = Y.j ⁻¹' closure {genPt (Z.ξ₀ ≫ Y.j)} := by
    ext u
    rw [Z.closure u, Set.mem_preimage, ← specializes_iff_mem_closure]
    exact (Y.j.isEmbedding.isInducing.specializes_iff).symm
  refine ⟨⟨U, hU ▸ ho.preimage Y.j.continuous⟩, rfl, fun p _ => ?_⟩
  haveI := (Y.normal (Y.j p)).1
  have hb := stalkMap_bijective_of_flat_preimmersion Y.j p
  exact ((RingEquiv.ofBijective _ hb).symm.injective.isDomain (RingEquiv.ofBijective _ hb).symm.toRingHom)

end GlobalTheory.CompanionTheory.Ar.Flat
