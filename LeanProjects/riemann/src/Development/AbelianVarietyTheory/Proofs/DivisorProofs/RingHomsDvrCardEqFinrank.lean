import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomEqCanonical
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem card_ringHom_to_integers_eq_finrank : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ]
    [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ],
    Finite (Λ →+* O) ∧ Nat.card (Λ →+* O) = Module.finrank ℤ_[p] Λ := by
  intro p _ C _ _ _ v O _ _ _ _ hv Λ _ _ _ _ _ _
  letI : Algebra ℤ_[p] O := (padicToO p O).toAlgebra
  letI : Algebra ℤ_[p] C := ((algebraMap O C).comp (algebraMap ℤ_[p] O)).toAlgebra
  haveI : IsScalarTower ℤ_[p] O C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hZC : Function.Injective (algebraMap ℤ_[p] C) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
    have hu : algebraMap ℤ_[p] C (PadicInt.unitCoeff h0 : ℤ_[p]) ≠ 0 :=
      ((PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[p] C)).ne_zero
    have hp : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    exact (mul_ne_zero hu (pow_ne_zero _ hp)) hx
  haveI : FaithfulSMul ℤ_[p] C := (faithfulSMul_iff_algebraMap_injective _ _).mpr hZC
  have hZE : Function.Injective (algebraMap ℤ_[p] (FractionRing Λ)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[p] Λ (FractionRing Λ)]
    exact (IsFractionRing.injective Λ (FractionRing Λ)).comp (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)
  haveI : FaithfulSMul ℤ_[p] (FractionRing Λ) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hZE
  letI : Algebra (FractionRing ℤ_[p]) (FractionRing Λ) := FractionRing.liftAlgebra ℤ_[p] (FractionRing Λ)
  haveI : IsScalarTower ℤ_[p] (FractionRing ℤ_[p]) (FractionRing Λ) :=
    FractionRing.isScalarTower_liftAlgebra ℤ_[p] (FractionRing Λ)
  letI : Algebra (FractionRing ℤ_[p]) C := FractionRing.liftAlgebra ℤ_[p] C
  haveI : IsScalarTower ℤ_[p] (FractionRing ℤ_[p]) C := FractionRing.isScalarTower_liftAlgebra ℤ_[p] C
  have hrank : Module.finrank (FractionRing ℤ_[p]) (FractionRing Λ) = Module.finrank ℤ_[p] Λ :=
    IsFractionRing.finrank_eq ℤ_[p] (FractionRing ℤ_[p]) Λ (FractionRing Λ)
  haveI : Module.IsTorsionFree ℤ_[p] Λ :=
    NoZeroSMulDivisors.iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective ℤ_[p] Λ)
  have hpos : 0 < Module.finrank ℤ_[p] Λ := Module.finrank_pos
  haveI : FiniteDimensional (FractionRing ℤ_[p]) (FractionRing Λ) :=
    Module.finite_of_finrank_pos (hrank ▸ hpos)
  haveI : Algebra.IsSeparable (FractionRing ℤ_[p]) (FractionRing Λ) := inferInstance
  have hcard := AlgHom.card (FractionRing ℤ_[p]) (FractionRing Λ) C

  haveI : Algebra.IsIntegral ℤ_[p] Λ := Algebra.IsIntegral.of_finite ℤ_[p] Λ
  let Φ : (Λ →+* O) → (Λ →+* C) := fun σ => (algebraMap O C).comp σ
  have hΦ : Function.Injective Φ := fun σ τ h =>
    RingHom.ext fun x => hv.hom_inj (RingHom.congr_fun h x)
  let Ψ : (FractionRing Λ →ₐ[FractionRing ℤ_[p]] C) → (Λ →+* C) :=
    fun φ => (φ : FractionRing Λ →+* C).comp (algebraMap Λ (FractionRing Λ))
  have hΨ : Function.Injective Ψ := fun φ ψ h =>
    AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (nonZeroDivisors Λ) h)
  have hrange : Set.range Φ = Set.range Ψ := by
    ext τ
    constructor
    · rintro ⟨σ, rfl⟩
      have hcomm : ∀ c : ℤ_[p], Φ σ (algebraMap ℤ_[p] Λ c) = algebraMap ℤ_[p] C c := by
        intro c
        have hu := GlobalTheory.padicToO_unique p O (σ.comp (algebraMap ℤ_[p] Λ))
        have := RingHom.congr_fun hu c
        simp only [RingHom.comp_apply] at this
        change algebraMap O C (σ (algebraMap ℤ_[p] Λ c)) = algebraMap O C (padicToO p O c)
        rw [this]
      let τa : Λ →ₐ[ℤ_[p]] C := { Φ σ with commutes' := hcomm }
      have hinj : Function.Injective τa := by
        rw [injective_iff_map_eq_zero]
        have hk : RingHom.ker (τa : Λ →+* C) = ⊥ := by
          apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[p])
          rw [eq_bot_iff]
          intro c hc
          rw [Ideal.mem_comap, RingHom.mem_ker] at hc
          have : algebraMap ℤ_[p] C c = 0 := by rw [← hc]; exact (τa.commutes c).symm
          rw [Ideal.mem_bot]
          exact hZC (by rw [this, map_zero])
        intro x hx
        have : x ∈ RingHom.ker (τa : Λ →+* C) := hx
        rwa [hk, Ideal.mem_bot] at this
      let φ0 : FractionRing Λ →ₐ[ℤ_[p]] C := IsFractionRing.liftAlgHom (K := FractionRing Λ) hinj
      refine ⟨φ0.extendScalarsOfIsLocalization (FractionRing ℤ_[p]) (nonZeroDivisors ℤ_[p]), ?_⟩
      ext x
      change φ0 (algebraMap Λ (FractionRing Λ) x) = τa x
      rw [IsFractionRing.liftAlgHom_apply]
      exact IsFractionRing.lift_algebraMap hinj x
    · rintro ⟨φ, rfl⟩
      let τa : Λ →ₐ[ℤ_[p]] C :=
        (φ.restrictScalars ℤ_[p]).comp (IsScalarTower.toAlgHom ℤ_[p] Λ (FractionRing Λ))
      have hmem : ∀ x : Λ, ∃ y : O, algebraMap O C y = τa x := by
        intro x
        have h1 : IsIntegral ℤ_[p] (τa x) := (Algebra.IsIntegral.isIntegral x).map τa
        have h2 : IsIntegral O (τa x) := h1.tower_top
        exact hv.exists_of_le_one (hv.mem_of_integral h2)
      let e : O ≃+* (algebraMap O C).range :=
        RingEquiv.ofBijective (algebraMap O C).rangeRestrict
          ⟨fun a b h => hv.hom_inj (congrArg Subtype.val h), (algebraMap O C).rangeRestrict_surjective⟩
      let σ : Λ →+* O := e.symm.toRingHom.comp ((τa : Λ →+* C).codRestrict (algebraMap O C).range
        (fun x => by obtain ⟨y, hy⟩ := hmem x; exact ⟨y, hy⟩))
      refine ⟨σ, ?_⟩
      ext x
      have := congrArg Subtype.val (e.apply_symm_apply
        ((τa : Λ →+* C).codRestrict (algebraMap O C).range
          (fun x => by obtain ⟨y, hy⟩ := hmem x; exact ⟨y, hy⟩) x))
      exact this
  let eqv : (Λ →+* O) ≃ (FractionRing Λ →ₐ[FractionRing ℤ_[p]] C) :=
    (Equiv.ofInjective Φ hΦ).trans ((Equiv.setCongr hrange).trans (Equiv.ofInjective Ψ hΨ).symm)
  refine ⟨Finite.of_equiv _ eqv.symm, ?_⟩
  rw [Nat.card_congr eqv, Nat.card_eq_fintype_card, hcard, hrank]

end GlobalTheory
