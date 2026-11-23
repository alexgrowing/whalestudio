import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivOfCharacterEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FreeOfCharacter

noncomputable def freeRep (P : Type) [Group P] (N : ℕ) :
    Representation ℂ P (Fin N → MonoidAlgebra ℂ P) where
  toFun g :=
    { toFun := fun x => (MonoidAlgebra.single g (1 : ℂ) : MonoidAlgebra ℂ P) • x
      map_add' := fun x y => smul_add _ x y
      map_smul' := fun c x => smul_comm _ c x }
  map_one' := by
    refine LinearMap.ext fun x => ?_
    simp [← MonoidAlgebra.one_def]
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    simp [smul_smul, MonoidAlgebra.single_mul_single]

theorem freeRep_apply {P : Type} [Group P] {N : ℕ} (g : P) (x : Fin N → MonoidAlgebra ℂ P) :
    freeRep P N g x = (MonoidAlgebra.single g (1 : ℂ) : MonoidAlgebra ℂ P) • x := rfl

theorem trace_freeRep {P : Type} [Group P] [Finite P] (N : ℕ) {g : P} (hg : g ≠ 1) :
    LinearMap.trace ℂ _ (freeRep P N g) = 0 := by
  classical
  haveI := Fintype.ofFinite P
  let b := Pi.basis fun _ : Fin N => MonoidAlgebra.basis P ℂ
  have hb : ∀ (j : Fin N) (q : P), b ⟨j, q⟩ = Pi.single j (MonoidAlgebra.single q 1) := by
    intro j q
    simp [b, Pi.basis_apply]
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
  refine Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨j, p⟩ := i
  have hmove : freeRep P N g (b ⟨j, p⟩) = b ⟨j, g * p⟩ := by
    rw [hb, hb, freeRep_apply]
    funext k
    by_cases hk : k = j
    · subst hk
      simp [MonoidAlgebra.single_mul_single]
    · simp [hk]
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hmove, b.repr_self, Finsupp.single_apply, if_neg]
  intro h
  rw [Sigma.mk.inj_iff, heq_iff_eq] at h
  exact hg (mul_right_cancel (h.2.trans (one_mul p).symm))

theorem finrank_free (P : Type) [Group P] [Finite P] (N : ℕ) :
    Module.finrank ℂ (Fin N → MonoidAlgebra ℂ P) = Nat.card P * N := by
  haveI := Fintype.ofFinite P
  rw [Module.finrank_eq_card_basis (Pi.basis fun _ : Fin N => MonoidAlgebra.basis P ℂ),
    Fintype.card_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Nat.card_eq_fintype_card, mul_comm]

theorem free_of_trace_eq_zero : ∀ (P M : Type) [Group P] [Finite P] [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ P M), (∀ g : P, g ≠ 1 → LinearMap.trace ℂ M (ρ g) = 0) → ∃ N : ℕ, Nat.card P * N = Module.finrank ℂ M ∧ Nonempty (ρ.asModule ≃ₗ[MonoidAlgebra ℂ P] (Fin N → MonoidAlgebra ℂ P)) := by
  intro P M _ _ _ _ _ ρ hρ
  classical
  haveI := Fintype.ofFinite P
  have hcard : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  haveI : Invertible (Nat.card P : ℂ) := invertibleOfNonzero hcard

  have hz : ∀ g : P, g ≠ 1 → ρ.character g = 0 := hρ
  have havg := Representation.card_inv_mul_sum_char_eq_finrank ρ
  rw [Finset.sum_eq_single (1 : P) (fun g _ hg => hz g hg) (by simp),
    Representation.char_one] at havg
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Nat.card P * N = Module.finrank ℂ M := by
    refine ⟨Module.finrank ℂ (Representation.invariants ρ), ?_⟩
    have hc : ((Nat.card P * Module.finrank ℂ (Representation.invariants ρ) : ℕ) : ℂ) =
        (Module.finrank ℂ M : ℂ) := by
      push_cast
      rw [← havg, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
    exact_mod_cast hc
  refine ⟨N, hN, ?_⟩
  haveI : FiniteDimensional ℂ (MonoidAlgebra ℂ P) :=
    Module.Finite.of_basis (MonoidAlgebra.basis P ℂ)

  have hχ : ρ.character = (freeRep P N).character := by
    funext g
    by_cases hg : g = 1
    · subst hg
      rw [Representation.char_one, Representation.char_one, finrank_free, hN]
    · exact (hz g hg).trans (trace_freeRep N hg).symm
  obtain ⟨e⟩ := GlobalTheory.CharacterDetermines.nonempty_equiv_of_character_eq P M
    (Fin N → MonoidAlgebra ℂ P) ρ (freeRep P N) hχ

  have hlin : ∀ (r : MonoidAlgebra ℂ P) (x : M),
      e.toLinearEquiv (ρ.asAlgebraHom r x) = (freeRep P N).asAlgebraHom r (e.toLinearEquiv x) := by
    intro r x
    induction r using MonoidAlgebra.induction_on with
    | of g =>
      simp only [Representation.asAlgebraHom_of]
      exact e.toIntertwiningMap.isIntertwining _ _ g x
    | add f f' hf hf' => simp only [map_add, LinearMap.add_apply, hf, hf']
    | smul c f hf => simp only [map_smul, LinearMap.smul_apply, hf]

  have hact : ∀ (r : MonoidAlgebra ℂ P) (y : Fin N → MonoidAlgebra ℂ P),
      (freeRep P N).asAlgebraHom r y = r • y := by
    intro r y
    induction r using MonoidAlgebra.induction_on with
    | of g => rw [Representation.asAlgebraHom_of, freeRep_apply, MonoidAlgebra.of_apply]
    | add f f' hf hf' => rw [map_add, LinearMap.add_apply, hf, hf', add_smul]
    | smul c f hf => rw [map_smul, LinearMap.smul_apply, hf, smul_assoc]
  exact ⟨{ (ρ.asModuleEquiv.trans e.toLinearEquiv).toAddEquiv with
    map_smul' := fun r x => by
      change e.toLinearEquiv (ρ.asModuleEquiv (r • x)) = r • e.toLinearEquiv (ρ.asModuleEquiv x)
      rw [Representation.asModuleEquiv_map_smul, hlin, hact] }⟩

end GlobalTheory.FreeOfCharacter
