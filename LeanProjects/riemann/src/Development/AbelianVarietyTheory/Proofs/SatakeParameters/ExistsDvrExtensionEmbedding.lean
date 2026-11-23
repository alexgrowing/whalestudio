import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

namespace GlobalTheory

theorem exists_finite_ext_numberField_sqrt (Qq E K : Type) [Field Qq] [Field E] [Field K]
    [NumberField K] (i : E →+* Qq) (e : E →+* K) (a : Qq) :
    ∃ (Kf : IntermediateField Qq (AlgebraicClosure Qq)) (s : Kf) (eK : K →+* Kf),
      FiniteDimensional Qq Kf ∧ s ^ 2 = algebraMap Qq Kf a ∧
        ∀ x : E, eK (e x) = algebraMap Qq Kf (i x) := by
  classical
  let Ω := AlgebraicClosure Qq
  letI : Algebra E K := e.toAlgebra
  letI : Algebra E Ω := ((algebraMap Qq Ω).comp i).toAlgebra
  haveI : CharZero E := RingHom.charZero e
  haveI : Module.Finite E K := Module.Finite.of_restrictScalars_finite ℚ E K
  let f : K →ₐ[E] Ω := IsAlgClosed.lift
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap Qq Ω a) (n := 2) two_pos
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := E) (M := K)
  let S : Set Ω := insert s (f '' (T : Set K))
  haveI : Finite S := ((T.finite_toSet.image f).insert s).to_subtype
  let Kf : IntermediateField Qq Ω := IntermediateField.adjoin Qq S
  have hfin : FiniteDimensional Qq Kf :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hmem : ∀ x : K, f x ∈ Kf := by
    intro x
    have hx : x ∈ Submodule.span E (T : Set K) := hT ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      exact IntermediateField.subset_adjoin Qq S (Set.mem_insert_of_mem _ ⟨y, hy, rfl⟩)
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      rw [map_smul, Algebra.smul_def]
      exact mul_mem (Kf.algebraMap_mem (i c)) hy
  refine ⟨Kf, ⟨s, IntermediateField.subset_adjoin Qq S (Set.mem_insert _ _)⟩,
    (f : K →+* Ω).codRestrict Kf hmem, hfin, Subtype.ext hs, fun x => Subtype.ext ?_⟩
  exact f.commutes x

theorem exists_complete_dvr_ext_numberField_sqrt : ∀ (W Qq E K : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [Field E] [Field K] [NumberField K] (i : E →+* Qq) (e : E →+* K) (a : W), ∃ (O Kf : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Field Kf) (_ : Algebra O Kf) (ι : Qq →+* Kf) (j : W →+* O) (w : O) (eK : K →+* Kf), IsFractionRing O Kf ∧ (∀ x : W, ι (algebraMap W Qq x) = algebraMap O Kf (j x)) ∧ j.Finite ∧ IsAdicComplete (IsLocalRing.maximalIdeal O) O ∧ w ^ 2 = j a ∧ ∀ x : E, eK (e x) = ι (i x) := by
  intro W Qq E K _ _ _ _ _ _ _ _ _ _ i e a
  obtain ⟨Kf, s, eK, hfin, hs, he⟩ :=
    exists_finite_ext_numberField_sqrt Qq E K i e (algebraMap W Qq a)
  letI : Algebra W Kf := ((algebraMap Qq Kf).comp (algebraMap W Qq)).toAlgebra
  haveI : IsScalarTower W Qq Kf := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI h1 := FormalIsogeny.finite_integralClosure W Qq Kf
  haveI h2 := FormalIsogeny.isDiscreteValuationRing_integralClosure W Qq Kf
  have h3 := FormalIsogeny.isAdicComplete_maximalIdeal_of_finite W (integralClosure W Kf)
  have h4 := integralClosure.isFractionRing_of_finite_extension (A := W) Qq Kf
  have hs' : s ^ 2 = algebraMap W Kf a := hs
  have hint : IsIntegral W s :=
    IsIntegral.of_pow two_pos (hs' ▸ isIntegral_algebraMap)
  exact ⟨integralClosure W Kf, Kf, inferInstance, inferInstance, h2, inferInstance, inferInstance,
    algebraMap Qq Kf, algebraMap W _, ⟨s, hint⟩, eK, h4, fun _ => rfl,
    RingHom.finite_algebraMap.2 h1, h3, Subtype.ext hs', he⟩

end GlobalTheory
