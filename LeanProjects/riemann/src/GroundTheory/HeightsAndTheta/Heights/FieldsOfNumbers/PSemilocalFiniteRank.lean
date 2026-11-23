import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFibreFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocFrac
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Rank

variable {F L₀ L : Type*} [Field F] [Field L₀] [Field L] [Algebra F L₀] [Algebra F L]

theorem isFractionRing_of_div {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    (inj : Function.Injective (algebraMap A K))
    (surj : ∀ z : K, ∃ x y : A, z = algebraMap A K x / algebraMap A K y) : IsFractionRing A K :=
  haveI := (faithfulSMul_iff_algebraMap_injective A K).mpr inj
  IsFractionRing.of_field A K surj

theorem finrank_eq_relfinrank_of_div (φ : L₀ →ₐ[F] L) {K₀ : IntermediateField F L₀}
    {E : IntermediateField F L} (hKE : K₀.map φ ≤ E) {A : Subalgebra F L₀} {B : Subalgebra F L}
    [Algebra A B] (hφ : ∀ a : A, ((algebraMap A B a : B) : L) = φ a) (hA : ∀ a ∈ A, a ∈ K₀)
    (hB : ∀ b ∈ B, b ∈ E) (fracA : ∀ x ∈ K₀, ∃ y ∈ A, ∃ z ∈ A, z ≠ 0 ∧ x = y / z)
    (fracB : ∀ x ∈ E, ∃ y ∈ B, ∃ z ∈ B, z ≠ 0 ∧ x = y / z) :
    Module.finrank A B = IntermediateField.relfinrank (K₀.map φ) E := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le hKE]
  set K := K₀.map φ
  set Lf := IntermediateField.extendScalars hKE
  let _ : Algebra A K := (((φ.comp A.val).toRingHom).codRestrict K
    (fun a => show φ a ∈ K from ⟨a, hA a a.2, rfl⟩)).toAlgebra
  let _ : Algebra B Lf := ((B.val.toRingHom).codRestrict Lf (fun b => hB b b.2)).toAlgebra
  let _ : Algebra A Lf := ((algebraMap B Lf).comp (algebraMap A B)).toAlgebra
  have _ : IsScalarTower A B Lf := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have _ : IsScalarTower A K Lf := IsScalarTower.of_algebraMap_eq (fun a => Subtype.ext (hφ a))
  have _ : IsFractionRing A K := by
    refine isFractionRing_of_div (fun a b h => Subtype.ext (φ.injective ?_)) ?_
    · exact congrArg Subtype.val h
    · rintro ⟨_, x, hx, rfl⟩
      obtain ⟨y, hy, z, hz, -, rfl⟩ := fracA x hx
      exact ⟨⟨y, hy⟩, ⟨z, hz⟩, Subtype.ext (map_div₀ φ y z)⟩
  have _ : IsFractionRing B Lf := by
    refine isFractionRing_of_div (fun a b h => Subtype.ext (congrArg Subtype.val h :)) ?_
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, z, hz, -, rfl⟩ := fracB x hx
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩, Subtype.ext rfl⟩
  exact (IsFractionRing.finrank_eq A K B Lf).symm

end Rank

theorem mem_homFracDegZero_of_mem_degZeroLoc {K : Type*} [DecidableEq K] {ι : K → Type*}
    {F : Type*} [Field F] (P : Ideal (MRing ι F)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι F))) :
    ∀ x ∈ degZeroLoc P 𝒲, x ∈ homFracDegZero P := by
  intro x hx
  refine (Algebra.adjoin_le (S := (homFracDegZero P).toSubalgebra) ?_) hx
  rintro _ ⟨b, f, g, hf, hg, hgP, -, rfl⟩
  exact IntermediateField.subset_adjoin _ _ ⟨b, f, g, hf, hg, hgP, rfl⟩

theorem SemilocalFiniteRank.proof (h1 : FibreFinite.Statement.{u})
    (h2 : SemilocalFinite.Statement.{u}) (h3 : DegZeroLocFrac.Statement.{u}) :
    SemilocalFiniteRank.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hd' hd W hW hdW hle
  have := hP'.isPrime
  have hfin := h1 F K K' j ι' P' hP' n hd' hd W hW hdW hle
  have inj : Function.Injective (algebraMap (degZeroLoc (contractPrime j P') {W})
      (degZeroLoc P' (fibrePrimes j P' W))) := by
    intro a b hab
    apply Subtype.ext
    apply (contractFracMap j P').toRingHom.injective
    have := congrArg Subtype.val hab
    rwa [degZeroLoc.algebraMap_contract_coe, degZeroLoc.algebraMap_contract_coe] at this
  refine ⟨h2 F K K' j ι' P' hP' n hd' hd W hW hdW hle, ⟨fun r hr x y hxy => ?_⟩, ?_⟩
  · have hr0 : algebraMap (degZeroLoc (contractPrime j P') {W})
        (degZeroLoc P' (fibrePrimes j P' W)) r ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap (degZeroLoc (contractPrime j P') {W})
        (degZeroLoc P' (fibrePrimes j P' W))), inj.eq_iff]
      exact hr.ne_zero
    simp only [Algebra.smul_def] at hxy
    exact mul_left_cancel₀ hr0 hxy
  · refine finrank_eq_relfinrank_of_div (contractFracMap j P') (map_homFracDegZero_le j ι' P')
      (degZeroLoc.algebraMap_contract_coe j P' W)
      (mem_homFracDegZero_of_mem_degZeroLoc _ _) (mem_homFracDegZero_of_mem_degZeroLoc _ _) ?_ ?_
    · intro x hx
      refine h3 F K (fun k => ι' (j k)) (contractPrime j P')
        (isMultiProjPrime_contractPrime _ _ hP') {W} (Set.finite_singleton W) ?_ x hx
      intro W₁ hW₁
      rw [Set.mem_singleton_iff.mp hW₁]
      exact hW
    · exact h3 F K' ι' P' hP' (fibrePrimes j P' W) hfin (fun W' hW' => hW'.1)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
