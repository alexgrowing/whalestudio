import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.OntoSurj

theorem surjective_of_points {R K : Type} [CommRing R] [Field K] [IsAlgClosed K] (σ : R →+* K)
    (hσ : Function.Injective σ) {P A : Scheme.{0}} (a : A ⟶ Sp R) [LocallyOfFiniteType a]
    (ha : IsOpenMap a) (ψ : P ⟶ A) (hψ : IsClosed (Set.range ψ))
    (h : ∀ x : Sp K ⟶ A, x ≫ a = spMap σ → ∃ p : Sp K ⟶ P, x = p ≫ ψ) : Surjective ψ := by
  have hd : Dense (Set.range (spMap σ)) := by
    have : DenseRange (PrimeSpectrum.comap σ) := by
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
        (RingHom.injective_iff_ker_eq_bot σ).mp hσ]
      exact bot_le
    exact this
  have hJ : JacobsonSpace ↥(pullback a (spMap σ)) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd a (spMap σ))
  have hZ : IsClosed ((pullback.fst a (spMap σ)) ⁻¹' Set.range ψ) :=
    hψ.preimage (pullback.fst a (spMap σ)).continuous
  have hsub : closedPoints ↥(pullback a (spMap σ)) ⊆
      (pullback.fst a (spMap σ)) ⁻¹' Set.range ψ := by
    intro z hz
    replace hz : IsClosed {z} := hz
    obtain ⟨p, hp⟩ := h (pointOfClosedPoint (pullback.snd a (spMap σ)) z hz ≫ pullback.fst _ _)
      (by rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc])
    obtain ⟨w⟩ : Nonempty ↥(Sp K) := inferInstance
    refine ⟨p w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hp, Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
  have hall := closure_minimal hsub hZ
  rw [closure_closedPoints] at hall
  have hsub' : a ⁻¹' Set.range (spMap σ) ⊆ Set.range ψ := by
    rw [← Scheme.Pullback.range_fst]
    rintro _ ⟨z, rfl⟩
    exact hall (Set.mem_univ z)
  have hall' := closure_minimal hsub' hψ
  rw [(hd.preimage ha).closure_eq] at hall'
  exact ⟨fun y ↦ hall' (Set.mem_univ y)⟩

theorem surjective_of_onto_complex_points :
    ∀ (R : Type) [CommRing R] [IsDomain R] (σ : R →+* ℂ), Function.Injective σ → ∀ (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (Φ : B ⟶ A), IsAbelianScheme A → IsAbelianScheme B → (∀ y : Over.mk (spMap σ) ⟶ A, ∃ x : Over.mk (spMap σ) ⟶ B, y = x ≫ Φ) → Surjective Φ.left ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (y : Over.mk t ⟶ A), ∃ x : Over.mk t ⟶ B, y = x ≫ Φ := by
  intro R _ _ σ hσ A B _ _ Φ hA hB h
  have := hB.proper
  have := hA.proper
  have := hA.smooth
  have hpr : IsProper Φ.left := by
    have : IsProper (Φ.left ≫ A.hom) := by rwa [Over.w]
    exact IsProper.of_comp Φ.left A.hom
  have hs : Surjective Φ.left := by
    refine surjective_of_points σ hσ A.hom A.hom.isOpenMap Φ.left
      Φ.left.isClosedMap.isClosed_range fun y hy ↦ ?_
    obtain ⟨p, hp⟩ := h (Over.homMk y hy)
    exact ⟨p.left, congrArg (·.left) hp⟩
  refine ⟨hs, fun k _ _ t y ↦ ?_⟩
  obtain ⟨p, hp⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective Φ.left y.left
  refine ⟨Over.homMk p ?_, Over.OverMorphism.ext hp⟩
  rw [← Over.w Φ, ← Category.assoc, ← hp]
  exact Over.w y

end GlobalTheory.OntoSurj
