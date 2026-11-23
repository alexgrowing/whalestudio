import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyDvdPowOfAevalEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralPi

noncomputable section

open Polynomial

namespace GlobalTheory.UnitLemma.PrincipalLat

theorem isIntegral_pi' {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i) (hx : ∀ i, IsIntegral O (x i)) :
    IsIntegral O x := by
  first
  | exact @_root_.GlobalTheory.IntegralPi.main
  | exact _root_.GlobalTheory.IntegralPi.main
  | (apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPi.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPi.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPi.main ..)

section General

variable {O E A : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
  [CommRing A] [Algebra E A] [Algebra O A] [IsScalarTower O E A] [Module.Finite E A]

variable (E) in
include E in

theorem exists_mul_isIntegral (y : A) : ∃ c : O, c ≠ 0 ∧ IsIntegral O (algebraMap O A c * y) := by
  have : Algebra.IsAlgebraic O A :=
    (IsFractionRing.comap_isAlgebraic_iff (A := O) (K := E) (C := A)).mpr inferInstance
  obtain ⟨c, hc, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := O) y).exists_integral_multiple
  exact ⟨c, hc, by rwa [Algebra.smul_def] at h⟩

end General

section General2

variable {O E A : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
  [CommRing A] [Algebra E A] [Algebra O A] [IsScalarTower O E A] [Module.Finite E A]

variable (E) in
include E in

theorem exists_mul_le_integral (J : Submodule O A) (hJ : J.FG) :
    ∃ c : O, c ≠ 0 ∧ ∀ z ∈ J, IsIntegral O (algebraMap O A c * z) := by
  classical
  obtain ⟨s, rfl⟩ := hJ
  choose f hf0 hf using fun y : A => exists_mul_isIntegral (O := O) E y
  refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.2 fun y _ => hf0 y, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.mul_prod_erase s f hy, map_mul, mul_comm (algebraMap O A (f y)), mul_assoc]
    exact isIntegral_algebraMap.mul (hf y)
  | zero => rw [mul_zero]; exact isIntegral_zero
  | add x y _ _ hx hy => rw [mul_add]; exact hx.add hy
  | smul o x _ hx => rw [mul_smul_comm]; exact hx.smul o

theorem eq_mulLat_of_isPrincipalIdealRing [IsPrincipalIdealRing (integralClosure O A)]
    (J : Submodule O A) (hJ : IsLat O E J) (hst : ∀ a ∈ integralClosure O A, ∀ y ∈ J, a * y ∈ J) :
    ∃ a : Aˣ, J = mulLat O (a : A) (Subalgebra.toSubmodule (integralClosure O A)) := by
  classical
  obtain ⟨c, hc0, hc⟩ := exists_mul_le_integral E J hJ.1
  set Λ := integralClosure O A

  have hcu : IsUnit (algebraMap O A c) := by
    rw [IsScalarTower.algebraMap_apply O E A]
    refine (IsUnit.mk0 _ ?_).map _
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc0))
  set C := algebraMap O A c
  let I : Ideal Λ :=
    { carrier := {l | ∃ z ∈ J, (l : A) = C * z}
      add_mem' := by
        rintro a b ⟨x, hx, hax⟩ ⟨y, hy, hby⟩
        exact ⟨x + y, J.add_mem hx hy, by rw [Subalgebra.coe_add, hax, hby, mul_add]⟩
      zero_mem' := ⟨0, J.zero_mem, by simp⟩
      smul_mem' := by
        rintro a b ⟨x, hx, hbx⟩
        refine ⟨(a : A) * x, hst _ a.2 _ hx, ?_⟩
        rw [smul_eq_mul, Subalgebra.coe_mul, hbx]; ring }
  obtain ⟨b, hb⟩ := (IsPrincipalIdealRing.principal I).principal
  have hmemI : ∀ l : Λ, l ∈ I ↔ ∃ m : Λ, m * b = l := by
    intro l; rw [hb]; exact Ideal.mem_span_singleton'
  have key : ∀ z, z ∈ J ↔ ∃ l ∈ Λ, C * z = b * l := by
    intro z; constructor
    · intro hz
      obtain ⟨m, hm⟩ := (hmemI ⟨C * z, hc z hz⟩).1 ⟨z, hz, rfl⟩
      have h2 := congrArg Subtype.val hm
      simp only [Subalgebra.coe_mul] at h2
      exact ⟨m, m.2, by rw [← h2, mul_comm]⟩
    · rintro ⟨l, hl, hzl⟩
      obtain ⟨z0, hz0, hbz0⟩ : b ∈ I := by rw [hb]; exact Ideal.mem_span_singleton_self b
      have : C * z = C * (l * z0) := by rw [hzl, hbz0]; ring
      rw [hcu.mul_left_cancel this]
      exact hst l hl z0 hz0

  have hbu : IsUnit (b : A) := by
    have hle : (J : Set A) ⊆ LinearMap.range (LinearMap.mulLeft E (b : A)) := by
      intro z hz
      obtain ⟨l, _, hzl⟩ := (key z).1 hz
      refine ⟨hcu.unit⁻¹ * l, ?_⟩
      simp only [LinearMap.mulLeft_apply]
      calc (b : A) * (↑hcu.unit⁻¹ * l) = ↑hcu.unit⁻¹ * (b * l) := by ring
        _ = z := by rw [← hzl, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
    have h1 : (1 : A) ∈ LinearMap.range (LinearMap.mulLeft E (b : A)) := by
      have := Submodule.span_le.2 hle
      rw [hJ.2] at this
      exact this Submodule.mem_top
    obtain ⟨w, hw⟩ := h1
    exact isUnit_iff_exists_inv.2 ⟨w, by simpa using hw⟩
  refine ⟨hcu.unit⁻¹ * hbu.unit, ?_⟩
  ext z
  rw [key z]
  simp only [mulLat, Submodule.mem_map, LinearMap.mulLeft_apply, Subalgebra.mem_toSubmodule,
    Units.val_mul, IsUnit.unit_spec]
  constructor
  · rintro ⟨l, hl, hzl⟩
    refine ⟨l, hl, ?_⟩
    rw [mul_assoc, ← hzl, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · rintro ⟨l, hl, hzl⟩
    refine ⟨l, hl, ?_⟩
    rw [← hzl, ← mul_assoc, ← mul_assoc, IsUnit.mul_val_inv, one_mul]

end General2

theorem isPrincipalIdealRing_integralClosure {O E A : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field E]
    [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra E A] [Algebra O A]
    [IsScalarTower O E A] [Module.Finite E A] [IsReduced A] :
    IsPrincipalIdealRing (integralClosure O A) := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite E A
  let ψ : A ≃ₐ[O] (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    (IsArtinianRing.equivPi A).restrictScalars O
  haveI hpir : ∀ I : MaximalSpectrum A, IsPrincipalIdealRing (integralClosure O (A ⧸ I.asIdeal)) := by
    intro I
    haveI := I.isMaximal
    letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional E (A ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ E I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    haveI := GlobalTheory.FormalIsogeny.isDiscreteValuationRing_integralClosure O E (A ⧸ I.asIdeal)
    infer_instance
  haveI : Finite (MaximalSpectrum A) := inferInstance
  let G : (∀ I : MaximalSpectrum A, integralClosure O (A ⧸ I.asIdeal)) →ₐ[O]
      (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) :=
    Pi.algHom O _ fun I => (integralClosure O (A ⧸ I.asIdeal)).val.comp (Pi.evalAlgHom O _ I)
  let F := (ψ.symm.toAlgHom.comp G).codRestrict (integralClosure O A) fun l =>
    (isIntegral_pi' (G l) fun I => (l I).2).map ψ.symm
  refine IsPrincipalIdealRing.of_surjective F ?_
  intro x
  refine ⟨fun I => ⟨ψ x I, x.2.map ((Pi.evalAlgHom O _ I).comp ψ.toAlgHom)⟩, ?_⟩
  apply Subtype.ext
  change ψ.symm (G _) = (x : A)
  have : G (fun I => ⟨ψ x I, x.2.map ((Pi.evalAlgHom O _ I).comp ψ.toAlgHom)⟩) = ψ x := rfl
  rw [this, AlgEquiv.symm_apply_apply]

theorem eq_mulLat_integralClosure : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) →
    ∃ a : B.Aˣ, J = mulLat K.O (a : B.A) (Subalgebra.toSubmodule (integralClosure K.O B.A)) := by
  intro K B hsep J hJ hst
  haveI : IsReduced B.A := ⟨fun a ha => Centraliser.eq_zero_of_isNilpotent B hsep a ha⟩
  haveI := isPrincipalIdealRing_integralClosure (O := K.O) (E := K.E) (A := B.A)
  exact eq_mulLat_of_isPrincipalIdealRing J hJ hst

end GlobalTheory.UnitLemma.PrincipalLat
