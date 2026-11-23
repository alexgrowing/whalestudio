import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.Proof.CoefField

theorem exists_coefField {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (ι : FractionRing O →+* Qbar l)
    (hι : ∀ z : ℤ_[l], ι (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    ∃ K : IntermediateField ℚ_[l] (Qbar l), (∀ z, z ∈ K ↔ ∃ x, ι x = z) ∧ FiniteDimensional ℚ_[l] K ∧
      ∀ x : FractionRing O, ‖ι x‖ ≤ 1 ↔ x ∈ (algebraMap O (FractionRing O)).range := by
  classical
  let φ : O →+* Qbar l := ι.comp (algebraMap O (FractionRing O))
  have hφ : ∀ z : ℤ_[l], φ (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) := hι
  have hQ : ∀ q : ℚ_[l], algebraMap ℚ_[l] (Qbar l) q ∈ ι.fieldRange := by
    intro q
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[l]) q
    rw [map_div₀]
    refine div_mem ?_ ?_
    · exact ⟨_, hι a⟩
    · exact ⟨_, hι b⟩
  let K : IntermediateField ℚ_[l] (Qbar l) := ι.fieldRange.toIntermediateField hQ
  have hK : ∀ z, z ∈ K ↔ ∃ x, ι x = z := fun z => Iff.rfl
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[l] O).FG)
  let S : Set (Qbar l) := φ '' (s : Set O)
  have hint : ∀ x ∈ S, IsIntegral ℚ_[l] x := by
    rintro _ ⟨y, -, rfl⟩
    obtain ⟨p, hp, hy⟩ : IsIntegral ℤ_[l] y := Algebra.IsIntegral.isIntegral y
    refine ⟨p.map (algebraMap ℤ_[l] ℚ_[l]), hp.map _, ?_⟩
    have := congrArg φ hy
    rw [map_zero, Polynomial.hom_eval₂] at this
    have e : (algebraMap ℚ_[l] (Qbar l)).comp (algebraMap ℤ_[l] ℚ_[l]) = φ.comp (algebraMap ℤ_[l] O) :=
      RingHom.ext fun z => (hφ z).symm
    rw [Polynomial.eval₂_map, e]
    exact this
  haveI : Finite S := (s.finite_toSet.image φ).to_subtype
  have hfd : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] S) :=
    IntermediateField.finiteDimensional_adjoin hint
  have hle : K ≤ IntermediateField.adjoin ℚ_[l] S := by
    have hO : ∀ y : O, φ y ∈ IntermediateField.adjoin ℚ_[l] S := by
      intro y
      have hy : y ∈ Submodule.span ℤ_[l] (s : Set O) := hs ▸ Submodule.mem_top
      induction hy using Submodule.span_induction with
      | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx =>
        rw [Algebra.smul_def, map_mul, hφ]
        exact mul_mem (IntermediateField.algebraMap_mem _ _) hx
    rintro _ ⟨x, rfl⟩
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    rw [map_div₀]
    exact div_mem (hO a) (hO b)
  refine ⟨K, hK, ?_, fun x => (GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.mem_range_iff ι hι x).symm⟩
  have hge : IntermediateField.adjoin ℚ_[l] S ≤ K := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨_, rfl⟩
  have heq : K = IntermediateField.adjoin ℚ_[l] S := le_antisymm hle hge
  rw [heq]
  exact hfd

theorem coefField_range : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc), ∃ K : IntermediateField ℚ_[N.l i] (Qbar (N.l i)), (∀ z, z ∈ K ↔ ∃ x, A.iotaQ i x = z) ∧ FiniteDimensional ℚ_[N.l i] K ∧ ∀ x : FractionRing (N.O i), ‖A.iotaQ i x‖ ≤ 1 ↔ x ∈ (algebraMap (N.O i) (FractionRing (N.O i))).range := by
  intro R H what₂ N A i
  exact exists_coefField (A.iotaQ i) (A.iotaQ_alg i)

end GlobalTheory.Proof.CoefField

end
