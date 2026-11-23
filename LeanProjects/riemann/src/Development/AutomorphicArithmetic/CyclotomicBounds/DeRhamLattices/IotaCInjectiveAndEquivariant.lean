import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistedCharacterCocycleOfTorsionLocalCocyc

open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.UseLoc.Cases

private theorem UpperTheory.KN.integral_tensor_pure {O LL : Type} [CommRing O] [Field LL] [Algebra O LL]
    (X : Type) [AddCommGroup X] [Module O X] (u : ↥(intO (O := O) LL) ⊗[O] X) :
    ∃ x : X, u = (oneO (O := O) (LL := LL)) ⊗ₜ x := by
  induction u using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul t x =>
    obtain ⟨tv, ht⟩ := t
    have ht' : tv ∈ (Algebra.linearMap O LL).range := ht
    obtain ⟨r, rfl⟩ := LinearMap.mem_range.mp ht'
    refine ⟨r • x, ?_⟩
    rw [← TensorProduct.smul_tmul]
    congr 1
    ext
    simp [oneO, Algebra.smul_def]
  | add u v hu hv =>
    obtain ⟨x, rfl⟩ := hu
    obtain ⟨y, rfl⟩ := hv
    exact ⟨x + y, by rw [TensorProduct.tmul_add]⟩

private theorem UpperTheory.KN.evaluation_of_integral_inclusion {O LL : Type} [CommRing O] [Field LL] [Algebra O LL]
    (lam : O) (a : ℕ) (x : ↥(Xq LL lam a)) :
    evOneQ LL (iotaC LL lam a ((oneO (O := O) (LL := LL)) ⊗ₜ x)) = x.1 := by
  obtain ⟨q, hq⟩ := x
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp only [iotaC, LinearMap.comp_apply, LinearMap.lTensor_tmul, Submodule.subtype_apply]
  rw [iotaG_tmul, evOneQ_mk]
  simp [oneO, constOne]

private theorem UpperTheory.KN.evaluation_at_one_injective {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] :
    Function.Injective (evOneQ (O := O) LL) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro q hq
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [LinearMap.mem_ker, evOneQ_mk, Submodule.Quotient.mk_eq_zero] at hq
  have hq' : v 0 ∈ (Algebra.linearMap O LL).range := hq
  obtain ⟨r, hr⟩ := LinearMap.mem_range.mp hq'
  rw [Submodule.Quotient.mk_eq_zero]
  show v ∈ ((Algebra.linearMap O LL).compLeft (Fin 1)).range
  refine LinearMap.mem_range.mpr ⟨fun _ => r, ?_⟩
  funext i
  fin_cases i
  simpa using hr

theorem _root_.UpperTheory.KN.iotaC_injective_and_equivariant :
    ∀ {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G]
      [TopologicalSpace G] (N : G →* Matrix (Fin 1) (Fin 1) O) (χ ψ : G →* Oˣ) (lam : O) (a : ℕ),
      (∀ g, (((χ g)⁻¹ * ψ g : Oˣ) : O) = N g 0 0) →
      Function.Injective (iotaC LL lam a) ∧ ∀ (g : G) (u : ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a)),
        iotaC LL lam a (tableLineDegreeTwo.actTw (latOne hinj ψ) ↥(Xq LL lam a) χ g u) = actD (stdLatG hinj N) g (iotaC LL lam a u) := by
  intro O LL _ _ _ hinj G _ _ N χ ψ lam a hN
  refine ⟨?_, ?_⟩
  · intro u v huv
    obtain ⟨x, rfl⟩ := UpperTheory.KN.integral_tensor_pure (O := O) (LL := LL) _ u
    obtain ⟨y, rfl⟩ := UpperTheory.KN.integral_tensor_pure (O := O) (LL := LL) _ v
    have h := congrArg (evOneQ LL) huv
    rw [UpperTheory.KN.evaluation_of_integral_inclusion, UpperTheory.KN.evaluation_of_integral_inclusion] at h
    rw [Subtype.ext h]
  · intro g u
    obtain ⟨x, rfl⟩ := UpperTheory.KN.integral_tensor_pure (O := O) (LL := LL) _ u
    apply UpperTheory.KN.evaluation_at_one_injective (O := O) (LL := LL)
    erw [actTw_oneO hinj]
    rw [evOneQ_actD]
    erw [UpperTheory.KN.evaluation_of_integral_inclusion, UpperTheory.KN.evaluation_of_integral_inclusion]
    rw [Submodule.coe_smul, hN g]
