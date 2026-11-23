import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneTmulOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfForallFinsetSubsetFlatStatement

open IsLocalRing

namespace GlobalTheory

open StrictHensOfHens

theorem exists_strictHenselisation_of_henselian : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (Ω : Type) [Field Ω] [Algebra (ResidueField R) Ω] [IsSepClosure (ResidueField R) Ω], ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (_ : HenselianLocalRing S) (_ : IsLocalHom (algebraMap R S)), IsSepClosed (ResidueField S) ∧ Module.Flat R S ∧ (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧ Nonempty (ResidueField S ≃ₐ[ResidueField R] Ω) ∧ (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  intro R _ _ Ω _ _ _
  have hflat : Module.Flat R (SH R Ω) := by
    refine GlobalTheory.T.flat_of_forall_finset_subset_flat_submodule R (SH R Ω) fun s => ?_
    obtain ⟨E, hE⟩ := exists_ofA_finset s
    let e := AlgEquiv.ofInjective (ofA R Ω E) (ofA_injective E)
    haveI : Module.Flat R (Lift R Ω E) := Algebra.Smooth.flat _ _
    refine ⟨Subalgebra.toSubmodule (ofA R Ω E).range, fun x hx => ?_,
      Module.Flat.of_linearEquiv e.symm.toLinearEquiv⟩
    obtain ⟨a, rfl⟩ := hE x hx
    exact ⟨a, rfl⟩
  refine ⟨SH R Ω, inferInstance, inferInstance, inferInstance, inferInstance,
    isSepClosed_residueField, hflat, map_maximalIdeal, ⟨resAlgEquiv⟩, Idx R Ω, inferInstance,
    inferInstance, inferInstance, fun E => (ofA R Ω E).range, ?_, ?_, fun E => ?_⟩
  · intro E F h x hx
    obtain ⟨a, rfl⟩ := hx
    exact ⟨trans R Ω E F h a, ofA_trans h a⟩
  · intro s
    obtain ⟨E, a, rfl⟩ := exists_ofA s
    exact ⟨E, a, rfl⟩
  · refine ⟨Lift R Ω E, inferInstance, inferInstance, inferInstance, maximalIdeal _, inferInstance, ⟨?_⟩⟩
    have hu : (maximalIdeal (Lift R Ω E)).primeCompl ≤ IsUnit.submonoid (Lift R Ω E) :=
      fun x hx => by simpa [IsUnit.mem_submonoid_iff, mem_maximalIdeal, mem_nonunits_iff] using hx
    exact ((IsLocalization.atUnits (Lift R Ω E) (maximalIdeal (Lift R Ω E)).primeCompl
      (S := Localization.AtPrime (maximalIdeal (Lift R Ω E))) hu).restrictScalars R).symm.trans
      (AlgEquiv.ofInjective (ofA R Ω E) (ofA_injective E))

end GlobalTheory
