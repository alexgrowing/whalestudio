import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import GroundTheory.AutomorphicForms.HarishChandraCentre

namespace UpperTheory.V.Af.CuspFin

def MultiRel {ι A : Type} [Ring A] {n : ℕ} (E : ι → Fin n → Fin n → A) : Prop :=
  (∀ v, Formalism.REAL.GlRel (E v)) ∧ ∀ v v', v ≠ v' → ∀ i j k l, Commute (E v i j) (E v' k l)

def capAlg {ι A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : ι → Fin n → Fin n → A) : Subalgebra ℂ A :=
  Algebra.adjoin ℂ {z | ∃ v u, z = Formalism.REAL.qdet (E v) u}

structure IsUniv {ι T : Type} [Ring T] [Algebra ℂ T] {n : ℕ} (E : ι → Fin n → Fin n → T) : Prop where
  rel : MultiRel E
  gen : Algebra.adjoin ℂ {z | ∃ v i j, z = E v i j} = ⊤
  univ : ∀ (A : Type) [Ring A] [Algebra ℂ A] (E' : ι → Fin n → Fin n → A), MultiRel E' →
    ∃ f : T →ₐ[ℂ] A, ∀ v i j, f (E v i j) = E' v i j
  centre : Subalgebra.center ℂ T ≤ capAlg E

def HasUniv (ι : Type) (n : ℕ) : Prop :=
  ∃ (T : Type) (_ : Ring T) (_ : Algebra ℂ T) (E : ι → Fin n → Fin n → T), IsUniv E

theorem hasUniv_empty (n : ℕ) : HasUniv PEmpty n := by
  refine ⟨ℂ, inferInstance, inferInstance, fun v => v.elim, ⟨fun v => v.elim, fun v => v.elim⟩, ?_,
    fun A _ _ _ _ => ⟨Algebra.ofId ℂ A, fun v => v.elim⟩, fun z _ => Subalgebra.algebraMap_mem _ z⟩
  exact eq_top_iff.2 fun z _ => Subalgebra.algebraMap_mem _ z

theorem HasUniv.of_equiv {ι κ : Type} {n : ℕ} (e : ι ≃ κ) (h : HasUniv ι n) : HasUniv κ n := by
  obtain ⟨T, _, _, E, h⟩ := h
  refine ⟨T, inferInstance, inferInstance, fun v => E (e.symm v),
    ⟨fun v => h.rel.1 _, fun v v' hv => h.rel.2 _ _ fun h => hv (e.symm.injective h)⟩, ?_, fun A _ _ E' hE => ?_, ?_⟩
  · refine eq_top_iff.2 (h.gen.ge.trans (Algebra.adjoin_mono ?_))
    rintro _ ⟨v, i, j, rfl⟩
    exact ⟨e v, i, j, by simp⟩
  · obtain ⟨f, hf⟩ := h.univ A (fun v => E' (e v)) ⟨fun v => hE.1 _, fun v v' hv => hE.2 _ _ fun h => hv (e.injective h)⟩
    exact ⟨f, fun v i j => by simp [hf]⟩
  · refine h.centre.trans (Algebra.adjoin_mono ?_)
    rintro _ ⟨v, u, rfl⟩
    exact ⟨e v, u, by simp⟩

theorem hasUniv_of_step {n : ℕ} (step : ∀ ι : Type, HasUniv ι n → HasUniv (Option ι) n) (ι : Type) [Finite ι] :
    HasUniv ι n :=
  Finite.induction_empty_option (P := fun ι => HasUniv ι n) (fun e h => h.of_equiv e) (hasUniv_empty n)
    (fun {ι} _ h => step ι h) ι

theorem hasUniv_of_sum {n : ℕ} (one : HasUniv Unit n)
    (sum : ∀ ι κ : Type, HasUniv ι n → HasUniv κ n → HasUniv (ι ⊕ κ) n) (ι : Type) [Finite ι] : HasUniv ι n :=
  hasUniv_of_step (fun ι h => (sum ι Unit h one).of_equiv (Equiv.optionEquivSumPUnit ι).symm) ι

theorem map_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun a b => f (X a b)) u := by
  have h : ∀ v a b, f (Formalism.REAL.Tm X v a b) = Formalism.REAL.Tm (fun a b => f (X a b)) v a b := fun v a b => by
    unfold Formalism.REAL.Tm
    split_ifs <;> simp
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, h]

end UpperTheory.V.Af.CuspFin
