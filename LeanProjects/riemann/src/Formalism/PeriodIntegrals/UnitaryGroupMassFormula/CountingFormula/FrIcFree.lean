import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGFR

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S
open ValuativeRel

theorem fr_ic_free {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (hc : CharZero F) (hE : ∀ x : E, x ≠ 0 → IsUnit x) :
    Module.Free 𝒪[F] (integralClosure 𝒪[F] E) ∧ Module.Finite 𝒪[F] (integralClosure 𝒪[F] E) ∧
      Module.finrank 𝒪[F] (integralClosure 𝒪[F] E) = 2 := by
  haveI := hl
  haveI := hc
  have hnt : Nontrivial E := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have := L.rank
    rw [Module.finrank_zero_of_subsingleton] at this
    omega
  letI : Field E := (show IsField E from
    ⟨exists_pair_ne E, mul_comm, fun {x} hx => (hE x hx).exists_right_inv⟩).toField
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ L.rank
  haveI : Module.IsTorsionFree 𝒪[F] E := FaithfulSMul.to_isTorsionFree _ E
  refine ⟨IsIntegralClosure.module_free 𝒪[F] F E (integralClosure 𝒪[F] E),
    IsIntegralClosure.finite 𝒪[F] F E (integralClosure 𝒪[F] E), ?_⟩
  rw [IsIntegralClosure.rank 𝒪[F] F E (integralClosure 𝒪[F] E), L.rank]

theorem fr_card {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hl : IsNonarchimedeanLocalField F)
    (hc : CharZero F) (hE : ∀ x : E, x ≠ 0 → IsUnit x) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) :
    Nat.card (L.O ⧸ Ideal.span {piO L ϖ}) = Nat.card 𝓀[F] ^ 2 := by
  classical
  haveI := hl
  obtain ⟨hfree, hfin, hrank⟩ := fr_ic_free L hl hc hE
  set A := integralClosure 𝒪[F] E with hA

  have hOA : L.O = A.toSubring := by
    ext x
    rw [L.O_def]
    rfl
  let e : L.O ≃+* A.toSubring := RingEquiv.subringCongr hOA

  let b : Module.Basis (Fin 2) 𝒪[F] A := (Module.finBasisOfFinrankEq 𝒪[F] A hrank)

  let πA : A := algebraMap 𝒪[F] A ϖ
  have hmemI : ∀ x : A, x ∈ (Ideal.span {πA} : Ideal A) ↔ ∃ y : A, x = ϖ • y := by
    intro x
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [Algebra.smul_def, mul_comm]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [Algebra.smul_def, mul_comm]⟩
  let I' : Submodule 𝒪[F] A := (Ideal.span {πA} : Ideal A).restrictScalars 𝒪[F]
  let P : Submodule 𝒪[F] (Fin 2 → 𝒪[F]) := Submodule.pi Set.univ fun _ => Ideal.span {ϖ}
  have hmap : I'.map (b.equivFun : A →ₗ[𝒪[F]] (Fin 2 → 𝒪[F])) = P := by
    ext v
    simp only [Submodule.mem_map, Submodule.restrictScalars_mem, P, Submodule.mem_pi, Set.mem_univ,
      true_implies, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨x, hx, rfl⟩ i
      obtain ⟨y, rfl⟩ := (hmemI x).mp hx
      exact ⟨b.equivFun y i, by rw [LinearEquiv.coe_coe, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]⟩
    · intro h
      choose w hw using h
      refine ⟨ϖ • b.equivFun.symm w, (hmemI _).mpr ⟨_, rfl⟩, ?_⟩
      funext i
      rw [LinearEquiv.coe_coe, map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul, ← hw i,
        mul_comm]
  have hmax : IsLocalRing.maximalIdeal 𝒪[F] = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  calc Nat.card (L.O ⧸ Ideal.span {piO L ϖ})
      = Nat.card (A.toSubring ⧸ Ideal.span {e (piO L ϖ)}) := by
        apply Nat.card_congr
        refine (Ideal.quotientEquiv _ _ e ?_).toEquiv
        rw [Ideal.map_span, Set.image_singleton]
        rfl
    _ = Nat.card (A ⧸ (Ideal.span {πA} : Ideal A)) := by
        rfl
    _ = Nat.card (A ⧸ I') := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv 𝒪[F] _).toEquiv.symm
    _ = Nat.card ((Fin 2 → 𝒪[F]) ⧸ P) := by
        apply Nat.card_congr
        rw [← hmap]
        exact (Submodule.Quotient.equiv I' _ b.equivFun rfl).toEquiv
    _ = Nat.card (Fin 2 → 𝒪[F] ⧸ Ideal.span {ϖ}) := Nat.card_congr (Submodule.quotientPi _).toEquiv
    _ = Nat.card (𝒪[F] ⧸ Ideal.span {ϖ}) ^ 2 := by
        rw [Nat.card_fun, Nat.card_fin]
    _ = Nat.card 𝓀[F] ^ 2 := by
        congr 1
        apply Nat.card_congr
        exact (Ideal.quotEquivOfEq hmax).toEquiv.symm

end PI.UnitaryGroupMassFormula.CntFormula
