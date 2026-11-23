import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInducedClassFunction
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfRepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldRestrictClassFunctionOne
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

open Polynomial in
theorem _root_.GlobalTheory.BI.isChar_mem_virt_complex {G : Type} [Group G] {χ : G → ℂ}
    (h : _root_.GlobalTheory.BI.IsChar ℂ ℂ χ) : χ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G :=
  AddSubgroup.subset_closure h

open Polynomial in
theorem _root_.GlobalTheory.BI.isChar_mul_complex {G : Type} [Group G] {a b : G → ℂ}
    (ha : _root_.GlobalTheory.BI.IsChar ℂ ℂ a) (hb : _root_.GlobalTheory.BI.IsChar ℂ ℂ b) :
    _root_.GlobalTheory.BI.IsChar ℂ ℂ (a * b) := by
  obtain ⟨n, ρ, hρ⟩ := ha
  obtain ⟨m, σ, hσ⟩ := hb
  have key := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G _ (Representation.tprod ρ σ)).1
  convert key using 1
  funext g
  simp [Representation.char_tensor, hρ, hσ]

open Polynomial in
private lemma trace_mulLeft_complex_lemma (z : ℂ) :
    LinearMap.trace ℂ ℂ (Algebra.lmul ℂ ℂ z) = z := by
  have hz : (Algebra.lmul ℂ ℂ z : ℂ →ₗ[ℂ] ℂ) = z • LinearMap.id := by
    ext x
    simp
  rw [hz, map_smul, LinearMap.trace_id]
  simp

open Polynomial in
theorem _root_.GlobalTheory.BI.isChar_monoidHom_complex {G : Type} [Group G] (lam : G →* ℂˣ) :
    _root_.GlobalTheory.BI.IsChar ℂ ℂ (fun g => (lam g : ℂ)) := by
  let ρ : Representation ℂ G ℂ :=
    (Algebra.lmul ℂ ℂ).toMonoidHom.comp ((Units.coeHom ℂ).comp lam)
  have key := (_root_.GlobalTheory.BI.isChar_and_isIrrChar_of_rep ℂ ℂ G ℂ ρ).1
  convert key using 1
  funext g
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Representation.character]
  exact (trace_mulLeft_complex_lemma _).symm

open Polynomial in
theorem _root_.GlobalTheory.BI.subgroupFunctionExtendByZero_add {G : Type} [Group G] (H : Subgroup G) (a b : H → ℂ)
    (g : G) :
    _root_.GlobalTheory.BI.ext0 H (a + b) g =
      _root_.GlobalTheory.BI.ext0 H a g + _root_.GlobalTheory.BI.ext0 H b g := by
  unfold _root_.GlobalTheory.BI.ext0
  split_ifs <;> simp

noncomputable def indAddHomComplex {G : Type} [Group G] [Finite G] (H : Subgroup G) : (H → ℂ) →+ (G → ℂ) :=
  AddMonoidHom.mk' (ind H) (fun a b => by
    funext g
    haveI := Fintype.ofFinite G
    simp only [ind, Pi.add_apply, subgroupFunctionExtendByZero_add, finsum_eq_sum_of_fintype, Finset.sum_add_distrib, mul_add])

open Polynomial in

theorem _root_.GlobalTheory.BI.virt_mul_comap_conj_ind_linear : ∀ (G : Type) [Group G] [Finite G],
    (∀ a ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G, ∀ b ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G,
      a * b ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G) ∧
    (∀ a ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G, ∀ (H : Type) [Group H] (f : H →* G),
      (fun h => a (f h)) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ H) ∧
    (∀ a ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G, ∀ g x : G, a (x⁻¹ * g * x) = a g) ∧
    (∀ (H : Subgroup G) (ψ : H → ℂ), ψ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ H →
      _root_.GlobalTheory.BI.ind H ψ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G) ∧
    ∀ lam : G →* ℂˣ, (fun g => (lam g : ℂ)) ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G := by
  intro G _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    induction ha using AddSubgroup.closure_induction with
    | mem a ha' =>
      induction hb using AddSubgroup.closure_induction with
      | mem b hb' => exact AddSubgroup.subset_closure (_root_.GlobalTheory.BI.isChar_mul_complex ha' hb')
      | zero => simpa using zero_mem _
      | add b c _ _ hb hc => simpa [mul_add] using add_mem hb hc
      | neg b _ hb => simpa [mul_neg] using neg_mem hb
    | zero => simpa using zero_mem _
    | add a c _ _ ha hc => simpa [add_mul] using add_mem ha hc
    | neg a _ ha => simpa [neg_mul] using neg_mem ha
  · intro a ha H _ f
    induction ha using AddSubgroup.closure_induction with
    | mem a ha' =>
      exact AddSubgroup.subset_closure
        ((_root_.GlobalTheory.isChar_restrict_conj_one ℂ ℂ G a ha').1 H f)
    | zero => exact zero_mem _
    | add a c _ _ ha hc => exact add_mem ha hc
    | neg a _ ha => exact neg_mem ha
  · intro a ha g x
    induction ha using AddSubgroup.closure_induction with
    | mem a ha' => exact (_root_.GlobalTheory.isChar_restrict_conj_one ℂ ℂ G a ha').2.1 g x
    | zero => rfl
    | add a c _ _ ha hc => simp [ha, hc]
    | neg a _ ha => simp [ha]
  · intro H ψ hψ
    change _root_.GlobalTheory.BI.indAddHomComplex H ψ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G
    induction hψ using AddSubgroup.closure_induction with
    | mem ψ hψ' =>
      exact AddSubgroup.subset_closure
        (_root_.GlobalTheory.BI.isChar_ind ℂ ℂ G H ψ hψ')
    | zero => simpa using zero_mem _
    | add ψ φ _ _ hψ hφ => simpa [map_add] using add_mem hψ hφ
    | neg ψ _ hψ => simpa [map_neg] using neg_mem hψ
  · intro lam
    exact _root_.GlobalTheory.BI.isChar_mem_virt_complex (_root_.GlobalTheory.BI.isChar_monoidHom_complex lam)

end GlobalTheory.BI
