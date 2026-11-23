import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

namespace GlobalTheory.EtC.GmStep.FinSH

open IsLocalRing

theorem sh_of_finite_local (A T : Type) [CommRing A] [CommRing T] [Algebra A T] (hA : SH A)
    [Module.Finite A T] [IsLocalRing T] : SH T := by
  obtain ⟨hH, hk⟩ := hA
  refine ⟨GlobalTheory.henselianLocalRing_of_finite A T, ?_⟩
  have hc : (maximalIdeal T).comap (algebraMap A T) = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal T))
  haveI : IsLocalHom (algebraMap A T) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have : a ∈ (maximalIdeal T).comap (algebraMap A T) := by rw [hc]; exact hna
    exact (maximalIdeal T).ne_top_iff_one.1 (maximalIdeal.isMaximal T).ne_top
      (by simpa using Ideal.mul_mem_left _ (↑ha.unit⁻¹ : T) (show algebraMap A T a ∈ maximalIdeal T from this))
  haveI : Algebra.IsIntegral (ResidueField A) (ResidueField T) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨t', rfl⟩ := residue_surjective x
    have h1 : IsIntegral A (residue T t') :=
      (Algebra.IsIntegral.isIntegral (R := A) t').map (IsScalarTower.toAlgHom A T (ResidueField T))
    exact h1.tower_top
  exact Algebra.IsAlgebraic.isSepClosed (F := ResidueField A)

def optionProdEquiv (A : Type) [CommRing A] {α : Type} (T : Option α → Type) [∀ i, CommRing (T i)]
    [∀ i, Algebra A (T i)] : (∀ o, T o) ≃ₐ[A] T none × ∀ a, T (some a) :=
  { Equiv.piOptionEquivProd with
    map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl, commutes' := fun _ => rfl }

theorem induction_principle : ∀ (A : Type) [CommRing A], SH A → ∀ (P : ∀ (T : Type) [CommRing T] [Algebra A T], Prop),
  (∀ (T T' : Type) [CommRing T] [CommRing T'] [Algebra A T] [Algebra A T'], (T ≃ₐ[A] T') → P T → P T') →
  (∀ (T : Type) [CommRing T] [Algebra A T], Subsingleton T → P T) →
  (∀ (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] [Algebra A T₁] [Algebra A T₂], Module.Finite A T₁ → Module.Finite A T₂ →
    P T₁ → P T₂ → P (T₁ × T₂)) →
  (∀ (T : Type) [CommRing T] [Algebra A T], Module.Finite A T → SH T → P T) →
  ∀ (T : Type) [CommRing T] [Algebra A T], Module.Finite A T → P T := by
  intro A _ hA P hiso hsub hprod hsh T _ _ hT
  obtain ⟨hH, hk⟩ := hA
  obtain ⟨ι, hι, S, _, _, e, hS⟩ := GlobalTheory.exists_algEquiv_pi_henselianLocalRing A T
  have key : ∀ (α : Type) [Finite α] (S : α → Type) [∀ i, CommRing (S i)] [∀ i, Algebra A (S i)],
      (∀ i, Module.Finite A (S i) ∧ SH (S i)) → P (∀ i, S i) := by
    intro α _
    induction α using Finite.induction_empty_option with
    | of_equiv e' ih =>
      intro S _ _ hS'
      exact hiso _ _ (AlgEquiv.piCongrLeft A S e') (ih (fun a => S (e' a)) (fun a => hS' (e' a)))
    | h_empty =>
      intro S _ _ _
      exact hsub _ inferInstance
    | h_option ih =>
      intro S _ _ hS'
      refine hiso _ _ (optionProdEquiv A S).symm ?_
      haveI : ∀ a, Module.Finite A (S (some a)) := fun a => (hS' (some a)).1
      exact hprod _ _ (hS' none).1 inferInstance (hsh _ (hS' none).1 (hS' none).2)
        (ih (fun a => S (some a)) (fun a => hS' (some a)))
  refine hiso _ _ e.symm (key ι S fun i => ⟨(hS i).2, ?_⟩)
  haveI := (hS i).1
  haveI := (hS i).2
  exact sh_of_finite_local A (S i) ⟨hH, hk⟩

end GlobalTheory.EtC.GmStep.FinSH
