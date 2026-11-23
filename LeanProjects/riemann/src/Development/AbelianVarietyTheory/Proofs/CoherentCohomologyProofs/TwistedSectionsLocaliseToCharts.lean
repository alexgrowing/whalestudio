import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.VeryAmpleCompactQuasiSeparatedAffineCharts
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemNonzeroLocusIffMemBasicOpenChart
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsNhdsPowMulTwCoordEqZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsTwExtendPowMul
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulOfTwCoord

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem eval₂Hom_xProd_pow {ι : Type} {R B : Type*} [CommRing R] [CommRing B] (c : R →+* B)
    (b : ι → B) (I : Finset ι) (k : ℕ) :
    MvPolynomial.eval₂Hom c b (xProd R I ^ k) = (∏ i ∈ I, b i) ^ k := by
  rw [map_pow, map_prod]
  simp only [MvPolynomial.eval₂Hom_X']

theorem twisted_sections_localise : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y), H.IsLB → M.IsLB → VeryAmpleBy f H s → ∀ (hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V) fun i t => SecOnR.mulSec f M t (s i) V) (I : Finset (Fin (m + 1))), (∀ (t : ℤ) (a : SecOnR f (tw M H t) ⊤), SecOnR.restrict f _ (le_top : (⨅ i ∈ I, nonzeroLocus (s i)) ≤ ⊤) a = 0 → ∃ k : ℕ, xProd R I ^ k • GrSum.of (hx ⊤) t a = 0) ∧ ∀ (t : ℤ) (y : SecOnR f (tw M H t) (⨅ i ∈ I, nonzeroLocus (s i))), ∃ (k : ℕ) (t' : ℤ) (a : SecOnR f (tw M H t') ⊤), GrSum.of (hx _) t' (SecOnR.restrict f _ le_top a) = xProd R I ^ k • GrSum.of (hx _) t y := by
  intro R _ Y f H m s M hH hM hv hx I
  obtain ⟨hc, hq, -⟩ := GlobalTheory.VeryAmpleCharts.compact_quasiSeparated_isAffineOpen R Y f H m s hH hv
  obtain ⟨σ, hσ, hV⟩ := GlobalTheory.exists_prod_sec_nonzeroLocus Y H _ s I hH
  refine ⟨fun t a ha => ?_, fun t y => ?_⟩
  · obtain ⟨k, hk⟩ := exists_pow_mul_twCoord_eq_zero Y H M _ σ _ t hH hM hV.symm hc
      ((SecOnR.of f _ ⊤).symm a) ha
    obtain ⟨y', e, hy'⟩ := exists_smul_of_twCoord R Y f H m s M hx ⊤ _ _ t _
      ((SecOnR.of f _ ⊤).symm a) (xProd_pow_mem R I k) rfl
    have h0 : y' = 0 := SecOn.tw_ext fun p l => by
      rw [hy', eval₂Hom_xProd_pow, map_pow]
      have := hk p l
      rw [hσ] at this
      exact this
    refine ⟨k, e.trans ?_⟩
    rw [h0, map_zero, map_zero]
  · obtain ⟨k, a, hk⟩ := exists_tw_extend_pow_mul Y H M _ σ _ t hH hM hV.symm hc hq
      ((SecOnR.of f _ _).symm y)
    obtain ⟨y', e, hy'⟩ := exists_smul_of_twCoord R Y f H m s M hx _ _ _ t _
      ((SecOnR.of f _ _).symm y) (xProd_pow_mem R I k) rfl
    have h0 : SecOn.restrict _ le_top a = y' := SecOn.tw_ext fun p l => by
      rw [hy', eval₂Hom_xProd_pow, map_pow, SecOn.twCoord_restrict]
      have := hk p l
      rw [hσ] at this
      exact this
    refine ⟨k, _, SecOnR.of f _ ⊤ a, Eq.trans ?_ e.symm⟩
    rw [← h0, SecOnR.restrict_of]

end GlobalTheory.AbLaw
