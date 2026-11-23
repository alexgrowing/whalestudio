import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion

open IsLocalRing

namespace GlobalTheory.RegularCompletionPackage

theorem exists_regular_completion :
    ∀ (R₁ Ω : Type) [CommRing R₁] [IsRegularLocalRing R₁] [Field Ω] (u : R₁ →+* Ω),
      RingHom.ker u = maximalIdeal R₁ →
      ∃ (C : Type) (_ : CommRing C) (_ : IsRegularLocalRing C) (c : R₁ →+* C) (uC : C →+* Ω),
        c.Flat ∧ (maximalIdeal R₁).map c = maximalIdeal C ∧ IsAdicComplete (maximalIdeal C) C ∧
        RingHom.ker uC = maximalIdeal C ∧ uC.comp c = u := by
  intro R₁ Ω _ _ _ u hu
  set C := AdicCompletion (maximalIdeal R₁) R₁
  haveI : IsRegularLocalRing C := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion R₁
  have hbij := AdicCompletion.residueField_map_bijective_of_fg (R := R₁)
    (maximalIdeal R₁).fg_of_isNoetherianRing
  let e : ResidueField R₁ ≃+* ResidueField C :=
    RingEquiv.ofBijective (ResidueField.map (algebraMap R₁ C)) hbij
  let ub : ResidueField R₁ →+* Ω := Ideal.Quotient.lift (maximalIdeal R₁) u
    (fun a ha => by rw [← RingHom.mem_ker, hu]; exact ha)
  let uC : C →+* Ω := (ub.comp e.symm.toRingHom).comp (residue C)
  have hcomp : uC.comp (algebraMap R₁ C) = u := by
    ext r
    simp only [uC, RingHom.comp_apply]
    have : residue C (algebraMap R₁ C r) = e (residue R₁ r) := by
      simp [e, ResidueField.map_residue]
    rw [this]
    simp [ub]
    rfl
  refine ⟨C, inferInstance, inferInstance, algebraMap R₁ C, uC,
    RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _),
    (AdicCompletion.maximalIdeal_eq_map).symm, inferInstance, ?_, hcomp⟩
  ext x
  rw [RingHom.mem_ker]
  simp only [uC, RingHom.comp_apply]
  constructor
  · intro h
    have h1 : e.symm (residue C x) = 0 := (injective_iff_map_eq_zero ub).1 ub.injective _ h
    have h2 : residue C x = 0 := by simpa using h1
    simpa [residue_eq_zero_iff] using h2
  · intro h
    rw [(residue_eq_zero_iff x).2 h]
    simp

end GlobalTheory.RegularCompletionPackage
