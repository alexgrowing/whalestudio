import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StrictModelTranslatesTwistCompatible
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.CommAlg.Hens

open Polynomial IsLocalRing

theorem exists_isRoot_of_monic {C : Type} [Field C] [IsAlgClosed C] {R : Type} [CommRing R]
    [IsDomain R] [ValuationRing R] [Algebra R C] [IsFractionRing R C]
    {f : R[X]} (hf : f.Monic) (hd : 0 < f.natDegree) : ∃ r : R, f.IsRoot r := by
  have hinj : Function.Injective (algebraMap R C) := IsFractionRing.injective R C
  have hdeg : (f.map (algebraMap R C)).degree ≠ 0 := by
    rw [hf.degree_map]
    exact (natDegree_pos_iff_degree_pos.mp hd).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (f.map (algebraMap R C)) hdeg
  have hxa : aeval x f = 0 := by
    rw [aeval_def, ← Polynomial.eval_map]
    exact hx
  have hint : IsIntegral R x := ⟨f, hf, by rw [← aeval_def]; exact hxa⟩
  obtain ⟨r, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨r, hinj ?_⟩
  have hr0 : algebraMap R C (f.eval r) = aeval (algebraMap R C r) f :=
    (aeval_algebraMap_apply_eq_algebraMap_eval r f).symm
  rw [hr0, hxa, map_zero]

theorem exists_root_near {C : Type} [Field C] [IsAlgClosed C] {R : Type} [CommRing R]
    [IsDomain R] [ValuationRing R] [Algebra R C] [IsFractionRing R C] (n : ℕ) :
    ∀ (f : R[X]), f.Monic → f.natDegree = n → ∀ a₀ : R, f.eval a₀ ∈ maximalIdeal R →
      ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ maximalIdeal R := by
  induction n with
  | zero =>
    intro f hf hn a₀ h
    have : f = 1 := hf.natDegree_eq_zero.mp hn
    subst this
    rw [eval_one] at h
    exact absurd h (Ideal.ne_top_iff_one _ |>.mp (maximalIdeal.isMaximal R).ne_top)
  | succ n ih =>
    intro f hf hn a₀ h
    obtain ⟨r, hr⟩ := exists_isRoot_of_monic (C := C) hf (by omega)
    have hfac : (X - Polynomial.C r) * (f /ₘ (X - Polynomial.C r)) = f :=
      mul_divByMonic_eq_iff_isRoot.mpr hr
    have hgm : (f /ₘ (X - Polynomial.C r)).Monic := (monic_X_sub_C r).of_mul_monic_left (hfac.symm ▸ hf)
    have hgd : (f /ₘ (X - Polynomial.C r)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C, hn]; rfl
    rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at h
    rcases (maximalIdeal.isMaximal R).isPrime.mem_or_mem h with h1 | h1
    · refine ⟨r, hr, ?_⟩
      have := (maximalIdeal R).neg_mem h1
      simpa using this
    · obtain ⟨a, ha, ham⟩ := ih _ hgm hgd a₀ h1
      refine ⟨a, ?_, ham⟩
      rw [IsRoot.def, ← hfac, eval_mul, ha.eq_zero, mul_zero]

theorem henselian_and_residueField_isAlgClosed : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra R C] [IsFractionRing R C],
    HenselianLocalRing R ∧ IsAlgClosed (IsLocalRing.ResidueField R) := by
  intro C _ _ R _ _ _ _ _
  refine ⟨⟨fun f hf a₀ h _ => exists_root_near (C := C) _ f hf rfl a₀ h⟩, ?_⟩
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hlift : p ∈ lifts (residue R) :=
    (lifts_iff_coeff_lifts p).mpr fun n => residue_surjective (p.coeff n)
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift hp
  have hpos : 0 < q.natDegree := by
    rw [hqd]; exact hirr.natDegree_pos
  obtain ⟨r, hr⟩ := exists_isRoot_of_monic (C := C) hqm hpos
  refine ⟨residue R r, ?_⟩
  rw [← hq, eval_map_apply, hr.eq_zero, map_zero]

end GlobalTheory.CompanionTheory.CommAlg.Hens
