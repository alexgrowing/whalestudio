import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingElementOfLocalFieldPointValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueFieldPointPolarisedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalThetaConstantsLocalisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFlatCoverMSqTorsionSectionsStatement
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem thList_cover : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (c : Fin N → R₁), Module.Finite R R₁ ∧ Module.FaithfullyFlat R R₁ ∧ ∀ (K : Type) [Field K] (i : R →+* K) (i₁ : R₁ →+* K), i₁.comp (algebraMap R R₁) = i → ∃ pt : Fin N → (Over.mk (spMap i ≫ x) ⟶ G), ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt (fun a => i₁ (c a)) := by
  intro S G _ _ L ρ hL hρ g m N R _ _ x θ hm hu hN hP
  obtain ⟨R₁, _, _, q, hfin, hff, hq, hpts⟩ := GlobalTheory.T.exists_finite_flat_cover_m_sq_torsion_sections S G L g m N R x hm hu hN hP
  haveI : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R R₁
  have hcomp : ∀ {K : Type} [Field K] (i₁ : R₁ →+* K),
      spMap i₁ ≫ spMap (algebraMap R R₁) = spMap (i₁.comp (algebraMap R R₁)) := by
    intro K _ i₁; simp [spMap]
  let pt₀ : ∀ {K : Type} [Field K] (i₁ : R₁ →+* K) (a : Fin N), Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G :=
    fun i₁ a => Over.homMk (spMap i₁ ≫ (q a).left) (by
      have h := Over.w (q a)
      simp only [Over.mk_hom] at h ⊢
      rw [Category.assoc, h, ← Category.assoc, hcomp])
  have key : ∀ a : Fin N, ∃ c : R₁, ∀ (K : Type) [Field K] (i₁ : R₁ →+* K)
      (pt : Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G), pt.left = spMap i₁ ≫ (q a).left →
        ThG G L ρ m (SecAt.pull G L θ (i₁.comp (algebraMap R R₁))) pt (fn (i₁ c)) := by
    intro a
    refine GlobalTheory.T.exists_ring_element_of_local_field_point_values R₁ (fun K _ i₁ v => ∀ (pt : Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G),
        pt.left = spMap i₁ ≫ (q a).left →
        ThG G L ρ m (SecAt.pull G L θ (i₁.comp (algebraMap R R₁))) pt (fn v)) ?_ ?_
    · intro K _ i₁ u v hu' hv'
      exact GlobalTheory.T.thetaConstant_unique_field_point_polarisedFibre S G L ρ hL hρ g m R x K (i₁.comp (algebraMap R R₁)) hm hu hP _ (pt₀ i₁ a) u v
        (hu' _ rfl) (hv' _ rfl)
    · intro p hp
      obtain ⟨f, hf, c, hc⟩ := GlobalTheory.T.exists_local_thetaConstants_localisation S G L ρ hL hρ g m R x θ R₁ N q hm hu hP hq p hp
      exact ⟨f, hf, c a, fun K _ j pt hpt => hc K j a pt hpt⟩
  choose c hc using key
  refine ⟨R₁, inferInstance, inferInstance, c, hfin, hff, fun K _ i i₁ hi => ?_⟩
  subst hi
  obtain ⟨hinj, hcov⟩ := hpts K i₁ (pt₀ i₁) (fun a => rfl)
  exact ⟨pt₀ i₁, hinj, fun a => hc a K i₁ _ rfl, hcov⟩

end GlobalTheory.UMin
