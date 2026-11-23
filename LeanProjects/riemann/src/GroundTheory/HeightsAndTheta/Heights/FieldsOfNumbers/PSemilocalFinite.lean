import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalIntegral
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsLocalIntegralClosureFinite
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocNoetherian
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalFiniteRank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem module_finite_of_forall_mem_span {A A' B L : Type*} [CommRing A] [IsNoetherianRing A]
    [CommRing A'] [CommRing B] [Algebra A B] [CommRing L] [Algebra A' L] (φ : A →+* A')
    (hφ : Function.Surjective φ) (ψ : B →+* L) (hψ : Function.Injective ψ)
    (hcomm : ∀ a b, ψ (algebraMap A B a * b) = algebraMap A' L (φ a) * ψ b) (s : Finset L)
    (h : ∀ b, ψ b ∈ Submodule.span A' (s : Set L)) : Module.Finite A B := by
  let _ : Algebra A L := ((algebraMap A' L).comp φ).toAlgebra
  have hspan : ∀ x ∈ Submodule.span A' (s : Set L), x ∈ Submodule.span A (s : Set L) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact zero_mem _
    | add _ _ _ _ hy hz => exact add_mem hy hz
    | smul a' y _ hy =>
      obtain ⟨a, rfl⟩ := hφ a'
      have e : φ a • y = a • y := by rw [Algebra.smul_def, Algebra.smul_def]; rfl
      rw [e]
      exact Submodule.smul_mem _ a hy
  let f : B →ₗ[A] L :=
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := fun a b => by rw [Algebra.smul_def, hcomm]; rfl }
  have : IsNoetherian A (Submodule.span A (s : Set L)) :=
    isNoetherian_span_of_finite A s.finite_toSet
  exact Module.Finite.of_injective (f.codRestrict _ fun b => hspan _ (h b))
    fun b c hbc => hψ (congrArg Subtype.val hbc)

theorem SemilocalFinite.proof (h1 : SemilocalIntegral.Statement.{u})
    (h2 : LocalIntegralClosureFinite.Statement.{u}) (h3 : DegZeroLocNoetherian.Statement.{u}) :
    SemilocalFinite.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hd' hd W hW hdW hle
  have := hP'.isPrime
  set A := degZeroLoc (contractPrime j P') {W}
  set B := degZeroLoc P' (fibrePrimes j P' W)
  set A' := A.map (contractFracMap j P')
  have : IsNoetherianRing A :=
    h3 F K (fun k => ι' (j k)) _ (isMultiProjPrime_contractPrime _ _ hP') W hW hle
  have hint : Algebra.IsIntegral A B := h1 F K K' j ι' P' hP' n hd' hd W hW hdW hle
  obtain ⟨s, -, hs⟩ := h2 F K K' j ι' P' hP' (hd.trans hd'.symm) W hW hle
  let φA : A →+* A' := (((contractFracMap j P').comp A.val).codRestrict A'
    (fun a => Subalgebra.mem_map.mpr ⟨a, a.2, rfl⟩)).toRingHom
  have hφA : Function.Surjective φA := fun a' => by
    obtain ⟨a, ha, hae⟩ := Subalgebra.mem_map.mp a'.2
    exact ⟨⟨a, ha⟩, Subtype.ext hae⟩
  refine module_finite_of_forall_mem_span φA hφA B.val.toRingHom Subtype.val_injective
    (fun _ _ => rfl) s fun b => ?_
  exact hs _ (mem_homFracDegZero_of_mem_degZeroLoc P' _ _ b.2)
    (IsIntegral.map_of_comp_eq φA B.val.toRingHom (RingHom.ext fun _ => rfl) (hint.isIntegral b))

end

end GroundTheory.Heights₂.Heights.FieldNumbers
