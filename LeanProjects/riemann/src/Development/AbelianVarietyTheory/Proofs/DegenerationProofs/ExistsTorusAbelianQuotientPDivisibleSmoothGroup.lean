import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfPowerSeriesArcsOverAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.InfiniteTorsionOrCocharacterOfArcAtInfinityStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusQuotientNoCocharacterStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QuasiFiniteAtGenericPointOfIsDominant

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.DivSemi

theorem smooth_proj {S : Scheme.{0}} {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {G B : Over S} [GrpObj G] [GrpObj B] {i : splitTorus S X ⟶ G} {q : G ⟶ B} (h : IsQuot i q) : Smooth q.left := by
  obtain ⟨hi, hq, hf, hs, ha, hk, -⟩ := h
  have := (H1.torus_dim S X).smooth
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ((H1.torsor_pullback i q hk).map (Over.forget _)).flip
    ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact q.left)⟩ ?_
  exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this

theorem dim_eq_add {S : Scheme.{0}} (y : S) {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {G B : Over S} [GrpObj G] [GrpObj B] {i : splitTorus S X ⟶ G} {q : G ⟶ B} (h : IsQuot i q) {g g' : ℕ}
    (dG : SmoothOfRelativeDimension g G.hom) (dB : SmoothOfRelativeDimension g' B.hom) :
    g = g' + Module.finrank ℤ X := by
  have := smooth_proj h
  obtain ⟨hi, hq, hf, hs, ha, hk, -⟩ := h
  obtain ⟨m, W, hW, d₁⟩ := H1.exists_dim q.left (eSec G y)
  have g₂ : m = Module.finrank ℤ X := H1.dim_base (hk.map (Over.forget _)) d₁ (H1.torus_dim S X) (eSec _ y)
    ((congrArg (fun k => k.left y ∈ W) (IsMonHom.one_hom i)).mpr hW)
  have d₂ : SmoothOfRelativeDimension (m + g') (W.ι ≫ G.hom) := by
    rw [← Over.w q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension (0 + g) (W.ι ≫ G.hom) := inferInstance
  have := H1.dim_unique _ d₂ d₃ ⟨_, hW⟩
  omega

theorem exists_lift_point {k : Type} [Field k] [IsAlgClosed k] {G B : Over (Sp k)} (q : G ⟶ B)
    [LocallyOfFiniteType q.left] [QuasiCompact q.left] [Surjective q.left] (y : 𝟙_ (Over (Sp k)) ⟶ B) :
    ∃ x : 𝟙_ (Over (Sp k)) ⟶ G, x ≫ q = y := by
  let x : Sp k ⟶ B.left := y.left
  have : CompactSpace ↥(pullback q.left x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd q.left x)
  obtain ⟨p, -⟩ := (pullback.snd q.left x).surjective (default : PrimeSpectrum k)
  obtain ⟨z, -, hz⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback q.left x)) ⟨p, trivial⟩
  have e : (pointOfClosedPoint (pullback.snd q.left x) z hz ≫ pullback.fst q.left x) ≫ q.left = x := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
  refine ⟨Over.homMk (pointOfClosedPoint (pullback.snd q.left x) z hz ≫ pullback.fst q.left x) ?_, ?_⟩
  · rw [← Over.w q, ← Category.assoc]
    exact (congrArg (· ≫ B.hom) e).trans (Over.w y)
  · exact Over.OverMorphism.ext e

theorem isMonHom_id_pow {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (n : ℕ) :
    IsMonHom ((𝟙 B) ^ n : B ⟶ B) := by
  induction n with
  | zero => rw [pow_zero, Hom.one_def]; infer_instance
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 B) ^ n) (𝟙 B) ≫ μ[B]))

theorem exists_torus_abelian_quotient :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (G : Over (Sp k)) [GrpObj G], SmConn G → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ^ p = y) → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (B : Over (Sp k)) (_ : GrpObj B) (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q ∧ IsAbelianScheme B ∧ ∀ g, SmoothOfRelativeDimension g G.hom → ∃ a, SmoothOfRelativeDimension a B.hom ∧ g = a + Module.finrank ℤ X := by
  intro k _ _ p _ _ G _ hG hp
  obtain ⟨X, _, _, _, B, _, i, q, hQ, hmax⟩ := GlobalTheory.T.exists_torusQuotient_no_cocharacter k G hG
  have hsm := smooth_proj hQ
  have hQ' := hQ
  obtain ⟨hi, hq, hf, hs, ha, hk, hB⟩ := hQ'
  have hB' := hB
  obtain ⟨hc, h₁, h₂, h₃, h₄⟩ := hB'
  have hgi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom h₁ h₄
  have hint : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have hfin : Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ p = 1} := by
    have e : ∀ x : (𝟙_ (Over (Sp k)) ⟶ B), x ≫ ((𝟙 B) ^ p : B ⟶ B) = x ^ p := fun x => by
      rw [MonObj.comp_pow, Category.comp_id]
    have := GlobalTheory.SS.finite_ker_of_surjective_points k B hB ((𝟙 B) ^ p) (isMonHom_id_pow B p) fun y => by
      obtain ⟨y', rfl⟩ := exists_lift_point q y
      obtain ⟨x, rfl⟩ := hp y'
      exact ⟨x ≫ q, by rw [e, MonObj.pow_comp]⟩
    simpa only [e] using this
  have hpr : IsProper B.hom := by
    refine GlobalTheory.T.isProper_of_powerSeries_arcs_over_algClosed k B h₂ inferInstance h₃ fun a ha => ?_
    by_contra hn
    rcases GlobalTheory.T.infinite_torsion_or_cocharacter_of_arc_at_infinity k p B hB a ha hn with h | ⟨f, hf, hf'⟩
    · exact not_finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ p = 1}
    · exact hf' (hmax f hf)
  refine ⟨X, _, ‹_›, ‹_›, B, _, i, q, hQ, ⟨hc, h₁, hpr, h₄⟩, fun g hg => ?_⟩
  obtain ⟨x⟩ : Nonempty B.left := inferInstance
  obtain ⟨a, ha⟩ := exists_dim_of_preconnected B.hom x
  exact ⟨a, ha, dim_eq_add (default : PrimeSpectrum k) hQ hg ha⟩

end GlobalTheory.SS.DivSemi
