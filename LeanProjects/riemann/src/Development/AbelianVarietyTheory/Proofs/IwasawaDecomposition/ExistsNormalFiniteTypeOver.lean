import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory

theorem isFractionRing_of_forall_eq_div {B : Type} [CommRing B] [IsDomain B]
    (K : Type) [Field K] [Algebra B K] [IsFractionRing B K]
    (R : Type) [CommRing R] [Algebra R B] [Algebra R K]
    [IsScalarTower R B K] (hinj : Function.Injective (algebraMap R B))
    (h : ∀ b : B, ∃ a s : R, s ≠ 0 ∧ algebraMap R B s * b = algebraMap R B a) :
    IsFractionRing R K := by
  have hcomp : algebraMap R K = (algebraMap B K).comp (algebraMap R B) :=
    IsScalarTower.algebraMap_eq R B K
  have hinjK : Function.Injective (algebraMap R K) := by
    rw [hcomp]; exact (IsFractionRing.injective B K).comp hinj
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).mpr hinjK
  refine IsFractionRing.of_field R K (fun z => ?_)
  obtain ⟨b₁, b₂, -, rfl⟩ := IsFractionRing.div_surjective (A := B) z
  obtain ⟨a₁, s₁, hs₁, e₁⟩ := h b₁
  obtain ⟨a₂, s₂, hs₂, e₂⟩ := h b₂
  refine ⟨a₁ * s₂, s₁ * a₂, ?_⟩
  have n₁ : algebraMap B K (algebraMap R B s₁) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective B K), map_ne_zero_iff _ hinj]; exact hs₁
  have n₂ : algebraMap B K (algebraMap R B s₂) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective B K), map_ne_zero_iff _ hinj]; exact hs₂
  simp only [hcomp, RingHom.comp_apply, map_mul, ← e₁, ← e₂]
  set u := algebraMap B K (algebraMap R B s₁)
  set v := algebraMap B K (algebraMap R B s₂)
  rw [show u * algebraMap B K b₁ * v = (u * v) * algebraMap B K b₁ by ring,
    show u * (v * algebraMap B K b₂) = (u * v) * algebraMap B K b₂ by ring,
    mul_div_mul_left _ _ (mul_ne_zero n₁ n₂)]

theorem exists_finiteType_isIntegrallyClosed_integral_over :
    ∀ (A B : Type) [CommRing A] [Algebra.EssFiniteType ℤ A] [CommRing B] [IsDomain B]
      [IsIntegrallyClosed B] [Algebra A B] (C : Subalgebra A B), Algebra.FiniteType A C →
      (∀ b : B, ∃ a ∈ C, ∃ s ∈ C, s ≠ 0 ∧ s * b = a) →
      ∃ C' : Subalgebra A B, C ≤ C' ∧ Algebra.FiniteType A C' ∧ IsIntegrallyClosed C' ∧
        ∀ x ∈ C', IsIntegral C x := by
  intro A B _ _ _ _ _ _ C hC hfrac
  haveI : Algebra.FiniteType A C := hC
  haveI : Algebra.EssFiniteType ℤ C := Algebra.EssFiniteType.comp ℤ A C
  haveI : IsNoetherianRing C := Algebra.EssFiniteType.isNoetherianRing ℤ C
  set K := FractionRing B
  set D : Subalgebra C B := integralClosure C B with hD
  haveI hCK : IsFractionRing C K := by
    refine isFractionRing_of_forall_eq_div (B := B) K C Subtype.val_injective
      (fun b => ?_)
    obtain ⟨a, ha, s, hs, hne, e⟩ := hfrac b
    refine ⟨⟨a, ha⟩, ⟨s, hs⟩, ?_, e⟩
    intro h0; apply hne; simpa using congrArg Subtype.val h0
  haveI hDK : IsFractionRing D K := by
    refine isFractionRing_of_forall_eq_div (B := B) K D Subtype.val_injective
      (fun b => ?_)
    obtain ⟨a, ha, s, hs, hne, e⟩ := hfrac b
    refine ⟨⟨a, D.algebraMap_mem ⟨a, ha⟩⟩, ⟨s, D.algebraMap_mem ⟨s, hs⟩⟩, ?_, e⟩
    intro h0; apply hne; simpa using congrArg Subtype.val h0
  have hinjBK : Function.Injective (IsScalarTower.toAlgHom C B K) :=
    IsFractionRing.injective B K

  have hfinK : Module.Finite C (integralClosure C K) := by
    haveI := finite_integralClosure_of_essFiniteType_int C
    let e : FractionRing C ≃ₐ[C] K := IsLocalization.algEquiv (nonZeroDivisors C) _ _
    exact Module.Finite.equiv e.mapIntegralClosure.toLinearEquiv
  have hfinD : Module.Finite C D := by
    let f : D →ₗ[C] integralClosure C K :=
      { toFun := fun x => ⟨algebraMap B K x, x.2.map (IsScalarTower.toAlgHom C B K)⟩
        map_add' := fun x y => by ext; simp
        map_smul' := fun c x => by
          ext; simp [Algebra.smul_def]; left; exact (IsScalarTower.algebraMap_apply C B K c).symm }
    refine Module.Finite.of_injective f (fun x y hxy => ?_)
    apply Subtype.ext; apply IsFractionRing.injective B K
    exact congrArg Subtype.val hxy
  have hftD : Algebra.FiniteType A D := Algebra.FiniteType.trans hC inferInstance
  have hicD : IsIntegrallyClosed D := by
    refine (isIntegrallyClosed_iff K).mpr (fun {x} hx => ?_)
    have hxB : IsIntegral B x := hx.tower_top
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxB
    have hxC : IsIntegral C (algebraMap B K y) := isIntegral_trans _ hx
    have hyC : IsIntegral C y := (isIntegral_algHom_iff _ hinjBK).mp hxC
    exact ⟨⟨y, hyC⟩, rfl⟩
  refine ⟨D.restrictScalars A, fun x hx => ?_, hftD, hicD, fun x hx => hx⟩
  exact isIntegral_algebraMap (R := C) (A := B) (x := ⟨x, hx⟩)

end GlobalTheory
