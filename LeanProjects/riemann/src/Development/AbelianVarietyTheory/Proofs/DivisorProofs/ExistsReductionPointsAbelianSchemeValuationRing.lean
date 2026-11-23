import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperGroupSchemePointsValuationRingMulEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLiftUniqueValuationRingAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLocal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.ValReduction

theorem reduction_points : ∀ (U Ω k : Type) [CommRing U] [IsDomain U] [ValuationRing U] [Field Ω] [IsAlgClosed Ω] [Algebra U Ω] [IsFractionRing U Ω] [Field k] [IsAlgClosed k] (h : U →+* k) (S : Scheme.{0}) (G : Over S) [GrpObj G], IsAbelianScheme G → ∀ u : Sp U ⟶ S, ∃ r : (Over.mk (spMap (algebraMap U Ω) ≫ u) ⟶ G) →* (Over.mk (spMap h ≫ u) ⟶ G), (∀ (P : Over.mk u ⟶ G) y y₀, y.left = spMap (algebraMap U Ω) ≫ P.left → y₀.left = spMap h ≫ P.left → r y = y₀) ∧ (∀ (f : G ⟶ G) y, r (y ≫ f) = r y ≫ f) ∧ (∀ n : ℕ, IsUnit (n : U) → Set.BijOn r {y | y ^ n = 1} {y | y ^ n = 1}) ∧ ∀ (Lb : LB G.left), Lb.IsLB → ∀ n : ℕ, IsUnit (n : U) → ∀ y y' (c : Uˣ), y ^ n = 1 → y' ^ n = 1 → Out.WeilIs G Lb n y y' (unitOn (Units.map (algebraMap U Ω : U →* Ω) c)) → Out.WeilIs G Lb n (r y) (r y') (unitOn (Units.map (h : U →* k) c)) := by
  intro U Ω k _ _ _ _ _ _ _ _ _ h S G _ hA u
  obtain ⟨e, he⟩ := GlobalTheory.ValPts.points_generic_mulEquiv U Ω S G hA.proper u
  let Vk : Over.mk (spMap h ≫ u) ⟶ Over.mk u := Over.homMk (spMap h) rfl
  let φ : (Over.mk u ⟶ G) →* (Over.mk (spMap h ≫ u) ⟶ G) :=
    MonoidHom.mk' (Vk ≫ ·) fun x y => MonObj.comp_mul Vk x y
  have hφ : ∀ P, (φ P).left = spMap h ≫ P.left := fun P => rfl
  have hes : ∀ (P : Over.mk u ⟶ G) y, y.left = spMap (algebraMap U Ω) ≫ P.left → e.symm y = P := by
    intro P y hy
    rw [MulEquiv.symm_apply_eq]
    exact Over.OverMorphism.ext (hy.trans (he P).symm)
  have hey : ∀ y, y.left = spMap (algebraMap U Ω) ≫ (e.symm y).left := fun y => by
    rw [← he]; simp
  refine ⟨φ.comp e.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro P y y₀ hy hy₀
    apply Over.OverMorphism.ext
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hes P y hy, hφ, hy₀]
  · intro f y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have : e.symm (y ≫ f) = e.symm y ≫ f := hes _ _ (by
      rw [Over.comp_left, hey y, Category.assoc, Over.comp_left])
    rw [this]
    exact (Category.assoc Vk (e.symm y) f).symm
  · intro n hn
    refine ⟨fun y (hy : y ^ n = 1) => (show _ ^ n = 1 by rw [← map_pow, hy, map_one]), ?_, ?_⟩
    · intro y (hy : y ^ n = 1) y' (hy' : y' ^ n = 1) hyy
      have hP : (e.symm y) ^ n = 1 := by rw [← map_pow, hy, map_one]
      have hP' : (e.symm y') ^ n = 1 := by rw [← map_pow, hy', map_one]
      obtain ⟨Q, -, hQ⟩ := GlobalTheory.T.torsion_lift_unique_valuationRing_algClosed U Ω k h S G hA u n hn
        ((φ.comp e.symm.toMonoidHom) y) (by rw [← map_pow, hy, map_one])
      have h1 := hQ (e.symm y) ⟨hP, rfl⟩
      have h2 := hQ (e.symm y') ⟨hP', by rw [hyy]; rfl⟩
      exact e.symm.injective (h1.trans h2.symm)
    · intro y₀ (hy₀ : y₀ ^ n = 1)
      obtain ⟨P, ⟨hP, hPy⟩, -⟩ := GlobalTheory.T.torsion_lift_unique_valuationRing_algClosed U Ω k h S G hA u n hn y₀ hy₀
      refine ⟨e P, (show e P ^ n = 1 by rw [← map_pow, hP, map_one]), ?_⟩
      apply Over.OverMorphism.ext
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      rw [hφ, hPy]
  · intro Lb hLb n hn y y' c hy hy' H
    have hP : (e.symm y) ^ n = 1 := by rw [← map_pow, hy, map_one]
    have hP' : (e.symm y') ^ n = 1 := by rw [← map_pow, hy', map_one]
    exact GlobalTheory.WeilSpecialise.weilIs_specialise U Ω S G hA Lb hLb u n hn (e.symm y) (e.symm y') c hP hP' y y'
      (hey y) (hey y') H k h _ _ rfl rfl

end GlobalTheory.ValReduction
