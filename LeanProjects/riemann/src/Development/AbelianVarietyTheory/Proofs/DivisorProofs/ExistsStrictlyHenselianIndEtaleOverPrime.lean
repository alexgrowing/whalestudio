import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIndEtaleOfEtaleAtPrime

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.StrictHensPrime

theorem exists_sh_indEt (A : Type) [CommRing A] (p : Ideal A) [p.IsPrime] :
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra A O) (_ : IsLocalRing O), SH O ∧ IndEt A O ∧
      (IsLocalRing.maximalIdeal O).comap (algebraMap A O) = p := by
  classical
  obtain ⟨S, _, _, hH, hloc, hsep, -, -, -, ι, _, _, _, Si, hmono, hcov, hSi⟩ :=
    GlobalTheory.exists_strictHenselisation (Localization.AtPrime p)
      (SeparableClosure (IsLocalRing.ResidueField (Localization.AtPrime p)))
  let _ : Algebra A S := ((algebraMap (Localization.AtPrime p) S).comp
    (algebraMap A (Localization.AtPrime p))).toAlgebra
  have _ : IsScalarTower A (Localization.AtPrime p) S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hI : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Localization.AtPrime p) S) := by
    refine GlobalTheory.StrictHensUnion.indEtale_of_directed_union _ S ι Si hmono hcov fun i => ?_
    obtain ⟨B, _, _, _, q, _, ⟨e⟩⟩ := hSi i
    exact GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e
      (GlobalTheory.StrictHensUnion.indEtale_localization_of_etale _ B q.primeCompl)
  refine ⟨S, inferInstance, inferInstance, inferInstance, ⟨hH, hsep⟩, ?_, ?_⟩
  · exact IndEtaleAtPrime.indEt_of_indEt_atPrime A S p hI
  · rw [IsScalarTower.algebraMap_eq A (Localization.AtPrime p) S, ← Ideal.comap_comap,
      IsLocalRing.maximalIdeal_comap]
    exact Localization.AtPrime.under_maximalIdeal

end GlobalTheory.StrictHensPrime

end

example : ∀ (A : Type) [CommRing A] (p : Ideal A) [p.IsPrime], ∃ (O : Type) (_ : CommRing O) (_ : Algebra A O) (_ : IsLocalRing O), SH O ∧ IndEt A O ∧ (IsLocalRing.maximalIdeal O).comap (algebraMap A O) = p :=
  GlobalTheory.StrictHensPrime.exists_sh_indEt
