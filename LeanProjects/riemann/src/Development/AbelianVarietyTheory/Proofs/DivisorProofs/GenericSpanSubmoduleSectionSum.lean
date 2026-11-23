import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameCokernelP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagOfTriangularFrames

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.VB GlobalTheory.LieFilt GlobalTheory.GrFilt
open GlobalTheory.Twist (resM germ_resM)
open scoped Classical

namespace GlobalTheory.GrFilt

theorem stalkBasis_repr_germ_of_fintype {X : Scheme.{0}} {F : X.Modules} {κ : Type} [Fintype κ] {U V : X.Opens}
    {e : κ → Γ(F, U)} (he : IsFrame e) (h : V ≤ U) (x : X) (hx : x ∈ V) (t : Γ(F, V)) (i : κ) :
    (he.stalkBasis x (h hx)).repr (F.presheaf.germ V x hx t) i =
      X.presheaf.germ V x hx ((he.basis h).repr t i) := by
  conv_lhs => rw [← (he.basis h).sum_repr t]
  simp only [map_sum, QCoh.germ_smul, IsFrame.basis_apply, germ_resM]
  simp only [← he.stalkBasis_apply x (h hx)]
  rw [← map_sum, Module.Basis.repr_sum_self]

theorem mem_ofGeneric_iff_of_span :
    ∀ {X : Scheme.{0}} [IsIntegral X] {F : X.Modules} {κ : Type} [Fintype κ] {V : X.Opens} (c : κ → Γ(F, V)), IsFrame c →
    ∀ (Q : κ → Prop) (N : Submodule X.functionField (genStalk F)),
    (∀ hV : genericPoint X ∈ V, N = Submodule.span X.functionField ((fun z => F.presheaf.germ V _ hV (c z)) '' {z | Q z})) →
    ∀ (V' : X.Opens) (h : V' ≤ V) (a : κ → Γ(X, V')),
      (∑ z, a z • resM F h (c z)) ∈ (Sub.ofGeneric N).sec V' ↔ ∀ z, ¬ Q z → a z = 0 := by
  intro X _ F κ _ U e he Q N hN V h a
  rw [Sub.mem_ofGeneric]
  by_cases hV : genericPoint X ∈ V
  swap
  · refine ⟨fun _ j _ => ?_, fun _ h => (hV h).elim⟩
    obtain rfl : V = ⊥ := by
      by_contra hne
      obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
      exact hV (genericPoint_mem hx)
    exact Subsingleton.elim _ _
  have hsp : N = Submodule.span X.functionField
      ((show Module.Basis κ X.functionField (genStalk F) from he.stalkBasis _ (h hV)) '' {j | Q j}) := by
    refine (hN (h hV)).trans ?_
    congr 2
    funext z
    exact (he.stalkBasis_apply _ (h hV) z).symm
  have hco (j : κ) : (he.stalkBasis _ (h hV)).repr
      (F.presheaf.germ V _ hV (∑ j, a j • resM F h (e j))) j = X.presheaf.germ V _ hV (a j) := by
    rw [stalkBasis_repr_germ_of_fintype he h]
    simp only [← he.basis_apply h]
    rw [Module.Basis.repr_sum_self]
  have key : F.presheaf.germ V _ hV (∑ j, a j • resM F h (e j)) ∈ Submodule.span X.functionField
      ((show Module.Basis κ X.functionField (genStalk F) from he.stalkBasis _ (h hV)) ''
        {j | Q j}) ↔ ∀ j : κ, ¬ Q j → a j = 0 := by
    rw [Module.Basis.mem_span_image]
    constructor
    · intro H j hj
      by_contra hne
      have h0 : X.presheaf.germ V _ hV (a j) ≠ 0 := fun h0 =>
        hne (germ_injective_of_isIntegral X _ hV (h0.trans (map_zero _).symm))
      exact hj (H (Finsupp.mem_support_iff.2 (fun h1 => h0 ((hco j).symm.trans h1))))
    · intro H j hj
      by_contra hn
      refine Finsupp.mem_support_iff.1 hj ((hco j).trans ?_)
      rw [H j hn, map_zero]
  rw [← key]
  exact ⟨fun H => hsp.le (H hV), fun H _ => hsp.ge H⟩

end GlobalTheory.GrFilt

end
