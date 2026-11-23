import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.StalkGenericPointSpecializesOfSpecializes
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringLiftOfSpecialFibre

open IsLocalRing

namespace GlobalTheory.ArcAvoid

theorem exists_ringEquiv_powerSeries_of_complete {k O : Type*} [Field k] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (ι : k →+* O)
    (hι : Function.Surjective ((residue O).comp ι)) :
    ∃ e : PowerSeries k ≃+* O, ∀ a, e (PowerSeries.C a) = ι a := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨ev, hev⟩ := exists_algHom_powerSeries_apply_X_of_isAdicComplete (maximalIdeal O)
    (π := π) (by rw [hπ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self π)
  let ψ : PowerSeries k →+* O := (ev : PowerSeries O →+* O).comp (PowerSeries.map ι)
  have hX : ψ PowerSeries.X = π := by simp [ψ, hev]
  have hC : ∀ a, ψ (PowerSeries.C a) = ι a := fun a => by
    simpa [ψ] using ev.commutes (ι a)
  have hmap : (Ideal.span {(PowerSeries.X : PowerSeries k)}).map ψ = maximalIdeal O := by
    rw [Ideal.map_span, Set.image_singleton, hX, hπ.maximalIdeal_eq]
  have hH : IsHausdorff ((Ideal.span {(PowerSeries.X : PowerSeries k)}).map ψ) O := by
    rw [hmap]; infer_instance
  have hs : Function.Surjective ψ := by
    refine surjective_of_mk_map_comp_surjective (I := Ideal.span {PowerSeries.X}) ψ ?_
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := hι (residue O y)
    refine ⟨PowerSeries.C a, ?_⟩
    rw [RingHom.comp_apply, hC, Ideal.Quotient.eq, hmap]
    exact Ideal.Quotient.eq.mp ha
  have hi : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra h0
    obtain ⟨n, u, rfl⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 (PowerSeries.X_irreducible (R := k))
    rw [map_mul, map_pow, (u.isUnit.map _).mul_right_eq_zero, hX] at ha
    exact hπ.ne_zero (eq_zero_of_pow_eq_zero ha)
  exact ⟨RingEquiv.ofBijective ψ ⟨hi, hs⟩, hC⟩

theorem exists_ringHom_powerSeries_of_dvr {k V : Type*} [Field k] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] (ι : k →+* V) (hι : Function.Surjective ((residue V).comp ι)) :
    ∃ φ : V →+* PowerSeries k, Function.Injective φ ∧ (∀ a, φ (ι a) = PowerSeries.C a) ∧
      ∀ v, v ∈ maximalIdeal V ↔ PowerSeries.constantCoeff (φ v) = 0 := by
  let O := AdicCompletion (maximalIdeal V) V
  obtain ⟨e, he⟩ := exists_ringEquiv_powerSeries_of_complete ((algebraMap V O).comp ι) (by
    intro y
    obtain ⟨z, rfl⟩ := (AdicCompletion.residueField_map_bijective V).2 y
    obtain ⟨a, rfl⟩ := hι z
    exact ⟨a, rfl⟩)
  refine ⟨(e.symm : O →+* PowerSeries k).comp (algebraMap V O),
    e.symm.injective.comp (algebraMap_adicCompletion_injective_of_dvr V), fun a => ?_, fun v => ?_⟩
  · exact e.symm_apply_eq.mpr (he a).symm
  · rw [mem_maximalIdeal, mem_nonunits_iff, ← isUnit_map_iff (algebraMap V O),
      ← isUnit_map_iff e.symm, PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]
    rfl

open Polynomial in

theorem surjective_residue_of_isAlgebraic {k V : Type*} [Field k] [IsAlgClosed k] [CommRing V]
    [IsDomain V] [IsLocalRing V] [Algebra k[X] V] [Algebra.IsAlgebraic k[X] V]
    [FaithfulSMul k[X] V] (hX : algebraMap k[X] V X ∈ maximalIdeal V) :
    Function.Surjective ((residue V).comp ((algebraMap k[X] V).comp C)) := by
  classical
  letI : Algebra k (ResidueField V) := ((residue V).comp ((algebraMap k[X] V).comp C)).toAlgebra
  have hc : (algebraMap k (ResidueField V)).comp (constantCoeff : k[X] →+* k) =
      (residue V).comp (algebraMap k[X] V) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [RingHom.algebraMap_toAlgebra]
    · simpa using ((residue_eq_zero_iff _).mpr hX).symm
  have : Algebra.IsAlgebraic k (ResidueField V) := ⟨fun y => by
    obtain ⟨x, rfl⟩ := residue_surjective y
    obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := k[X]) x
    have h1 := aeval_primPart_eq_zero hp0 hp
    refine ⟨p.primPart.map constantCoeff, fun h => ?_, ?_⟩
    · refine Polynomial.not_isUnit_X (R := k) (p.isPrimitive_primPart X ?_)
      rw [C_dvd_iff_dvd_coeff]
      intro i
      have := congrArg (fun q => q.coeff i) h
      simpa [X_dvd_iff] using this
    · rw [aeval_def, eval₂_map, hc, ← hom_eval₂, ← aeval_def, h1, map_zero]⟩
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := ResidueField V)).2

open Polynomial in

theorem exists_injective_of_height_le_one {k B : Type*} [Field k] [IsAlgClosed k] [CommRing B]
    [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] (m : Ideal B) [hm : m.IsMaximal]
    (h1 : m.height ≤ 1) :
    ∃ φ : B →ₐ[k] PowerSeries k, Function.Injective φ ∧
      ∀ b, b ∈ m ↔ PowerSeries.constantCoeff (φ b) = 0 := by
  rcases eq_or_ne m ⊥ with rfl | hne
  · letI : Field B := (Ring.isField_iff_maximal_bot.mpr hm).toField
    have : Module.Finite k B := finite_of_finite_type_of_isJacobsonRing k B
    let e : k ≃ₐ[k] B :=
      .ofBijective (Algebra.ofId k B) IsAlgClosed.algebraMap_bijective_of_isIntegral
    refine ⟨(Algebra.ofId k (PowerSeries k)).comp e.symm, RingHom.injective _, fun b => ?_⟩
    simp [Algebra.ofId_apply]
  obtain ⟨t, htm, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  letI : Algebra k[X] B := (aeval t : k[X] →ₐ[k] B).toRingHom.toAlgebra
  have hal : ∀ p : k[X], algebraMap k[X] B p = aeval t p := fun _ => rfl
  have : IsScalarTower k k[X] B := .of_algebraMap_eq fun a => by simp [hal]
  have : Algebra.FiniteType k[X] B := .of_restrictScalars_finiteType k k[X] B
  have hinj : Function.Injective (algebraMap k[X] B) := by
    refine transcendental_iff_injective.mp fun halg => hm.ne_top ?_
    exact m.eq_top_of_isUnit_mem htm (halg.isIntegral.isUnit ht0)
  obtain ⟨K', _, _, _, V, φ, hφ, hφi, hφm⟩ := exists_valuationSubring_of_height_le_one
    (O := k[X]) (K := FractionRing k[X]) hinj m h1 X X_ne_zero (by simpa [hal] using htm)
  letI : Algebra k[X] V := (φ.comp (algebraMap k[X] B)).toAlgebra
  letI : Algebra k[X] K' :=
    ((algebraMap (FractionRing k[X]) K').comp (algebraMap k[X] (FractionRing k[X]))).toAlgebra
  have : IsScalarTower k[X] (FractionRing k[X]) K' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k[X] V K' := .of_algebraMap_eq fun a => (hφ a).symm
  have : FaithfulSMul k[X] V := (faithfulSMul_iff_algebraMap_injective _ _).mpr (hφi.comp hinj)
  have halg : Algebra.IsAlgebraic k[X] K' :=
    (IsFractionRing.comap_isAlgebraic_iff (A := k[X]) (K := FractionRing k[X]) (C := K')).mpr
      inferInstance
  have : Algebra.IsAlgebraic k[X] V :=
    .of_injective (IsScalarTower.toAlgHom k[X] V K') Subtype.val_injective
  have hXV : algebraMap k[X] V X ∈ maximalIdeal V := by
    change algebraMap k[X] B X ∈ (maximalIdeal V).comap φ
    simpa [hal, hφm] using htm
  let W : Subalgebra k[X] K' :=
    { V.toSubring with algebraMap_mem' := fun r => (hφ r) ▸ (φ (algebraMap k[X] B r)).2 }
  have hVn : IsNoetherianRing V := (krullAkizuki (FractionRing k[X]) W).1
  have hnf : ¬ IsField V := by
    rw [isField_iff_maximalIdeal_eq]
    intro h
    rw [h] at hXV
    exact X_ne_zero ((FaithfulSMul.algebraMap_eq_zero_iff k[X] V).mp hXV)
  have hval : ValuationRing V := inferInstance
  have : IsDiscreteValuationRing V := ((IsDiscreteValuationRing.TFAE V hnf).out 1 0).mp hval
  obtain ⟨ψ, hψi, hψC, hψm⟩ :=
    exists_ringHom_powerSeries_of_dvr _ (surjective_residue_of_isAlgebraic hXV)
  refine ⟨{ ψ.comp φ with commutes' := fun a => ?_ }, hψi.comp hφi, fun b => ?_⟩
  · have := hψC a
    rw [IsScalarTower.algebraMap_apply k k[X] B]
    exact this
  · rw [← hφm]
    exact hψm (φ b)

theorem exists_algHom_powerSeries_ne_zero :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [IsDomain B] [Algebra k B]
      [Algebra.FiniteType k B] (m : Ideal B), m.IsMaximal → ∀ f : B, f ≠ 0 →
      ∃ φ : B →ₐ[k] PowerSeries k, φ f ≠ 0 ∧
        ∀ b, b ∈ m ↔ PowerSeries.constantCoeff (φ b) = 0 := by
  intro k _ _ B _ _ _ _ m hm f hf
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨q, hqf, hqm, hht⟩ := exists_mem_height_map_le_one m (PrimeSpectrum.basicOpen f).isOpen
    ⟨⊥, hf, bot_le⟩
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have hcomap : (m.map (Ideal.Quotient.mk q.asIdeal)).comap (Ideal.Quotient.mk q.asIdeal) = m := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hqm
  have : (m.map (Ideal.Quotient.mk q.asIdeal)).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hm).resolve_left fun e => by
      rw [e, Ideal.comap_top] at hcomap
      exact hm.ne_top hcomap.symm
  obtain ⟨φ, hφi, hφm⟩ := exists_injective_of_height_le_one (k := k) _ hht
  refine ⟨φ.comp (Ideal.Quotient.mkₐ k q.asIdeal), fun h => hqf ?_, fun b => ?_⟩
  · exact Ideal.Quotient.eq_zero_iff_mem.mp (hφi (h.trans (map_zero φ).symm))
  · conv_lhs => rw [← hcomap]
    exact hφm _

end GlobalTheory.ArcAvoid
