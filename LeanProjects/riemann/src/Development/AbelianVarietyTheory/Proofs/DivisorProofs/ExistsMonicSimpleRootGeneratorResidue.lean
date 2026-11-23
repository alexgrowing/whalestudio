import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
open IsLocalRing GlobalTheory.Toroidal Polynomial

namespace GlobalTheory

theorem exists_monic_simple_root_generator_residue : ∀ (O R' Ω : Type) [CommRing O] [IsLocalRing O] [CommRing R']
    [IsLocalRing R'] [Field Ω] (φ' : O →+* R') (u' : R' →+* Ω), IsEtaleCompletion φ' →
    ((residue R').comp φ').FormallyUnramified → RingHom.ker u' = maximalIdeal R' →
    ∃ (G : Polynomial O) (β : Ω), G.Monic ∧ (G.map (u'.comp φ')).eval β = 0 ∧
      (G.map (u'.comp φ')).derivative.eval β ≠ 0 ∧
      ∀ r : R', ∃ q : Polynomial O, u' r = (q.map (u'.comp φ')).eval β := by
  intro O R' Ω _ _ _ _ _ φ u hφ hur hker
  obtain ⟨-, hmax, hfin⟩ := hφ
  haveI : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 : φ a ∈ maximalIdeal R' := hmax ▸ Ideal.mem_map_of_mem φ ((mem_maximalIdeal a).2 hna)
    exact (mem_maximalIdeal _).1 h1 ha
  have hcomp : (ResidueField.map φ).comp (residue O) = (residue R').comp φ :=
    ResidueField.map_comp_residue φ
  have hfin' : (ResidueField.map φ).Finite := by
    rw [← hcomp] at hfin
    exact RingHom.Finite.of_comp_finite hfin
  have hur' : (ResidueField.map φ).FormallyUnramified := by
    rw [← hcomp] at hur
    exact RingHom.FormallyUnramified.of_comp hur
  letI := (ResidueField.map φ).toAlgebra
  haveI : FiniteDimensional (ResidueField O) (ResidueField R') := hfin'
  haveI : Algebra.FormallyUnramified (ResidueField O) (ResidueField R') := hur'
  haveI : Algebra.IsSeparable (ResidueField O) (ResidueField R') :=
    Algebra.FormallyUnramified.isSeparable _ _
  let ι : ResidueField R' →+* Ω := Ideal.Quotient.lift (maximalIdeal R') u
    (fun a ha => by rwa [← RingHom.mem_ker, hker])
  have hι : ∀ r, ι (residue R' r) = u r := fun r => Ideal.Quotient.lift_mk _ _ _
  have hres : ∀ (P : O[X]) (x : ResidueField R'),
      (P.map (u.comp φ)).eval (ι x) = ι (aeval x (P.map (residue O))) := by
    intro P x
    rw [aeval_def, hom_eval₂, eval₂_map, eval_map]
    congr 1
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField O) (ResidueField R')
  have hint : IsIntegral (ResidueField O) α := Algebra.IsIntegral.isIntegral α
  have hpm : (minpoly (ResidueField O) α).Monic := minpoly.monic hint
  have hlift : minpoly (ResidueField O) α ∈ lifts (residue O) :=
    (lifts_iff_coeff_lifts _).2 fun n => residue_surjective _
  obtain ⟨G, hGmap, -, hGm⟩ := lifts_and_degree_eq_and_monic hlift hpm
  refine ⟨G, ι α, hGm, ?_, ?_, ?_⟩
  · rw [hres, hGmap, minpoly.aeval, map_zero]
  · rw [derivative_map, hres, ← derivative_map, hGmap]
    refine (map_ne_zero ι).2 ?_
    exact (Algebra.IsSeparable.isSeparable (ResidueField O) α).aeval_derivative_ne_zero (minpoly.aeval _ _)
  · intro r
    have hr : residue R' r ∈ Algebra.adjoin (ResidueField O) {α} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
        IntermediateField.mem_toSubalgebra, hα]
      exact IntermediateField.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hr
    obtain ⟨pb, hpb⟩ := hr
    obtain ⟨P, hP⟩ := map_surjective (residue O) residue_surjective pb
    refine ⟨P, ?_⟩
    rw [hres, hP, ← hι]
    exact congrArg ι hpb.symm

end GlobalTheory
