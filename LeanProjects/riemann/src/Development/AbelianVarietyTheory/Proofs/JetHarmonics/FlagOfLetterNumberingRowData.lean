import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces

set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

theorem card_sigma_fibre {A B : Type} [Fintype A] (m : A → ℕ) (ty : A ≃ B) (s : A) :
    (Finset.univ.filter fun c : (Σ s : A, Fin (m s)) => ty c.1 = ty s).card = m s := by
  have h : (Finset.univ.filter fun c : (Σ s : A, Fin (m s)) => ty c.1 = ty s)
      = (Finset.univ : Finset (Fin (m s))).map (Function.Embedding.sigmaMk (β := fun s => Fin (m s)) s) := by
    ext ⟨a, c⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, EmbeddingLike.apply_eq_iff_eq, Finset.mem_map,
      Function.Embedding.sigmaMk_apply]
    constructor
    · rintro rfl
      exact ⟨c, rfl⟩
    · rintro ⟨c', h⟩
      exact (congrArg Sigma.fst h).symm
  rw [h, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem flag_of_numbering : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (A : Fin 2 → Type) [∀ g, Fintype (A g)] (m : ∀ g, A g → ℕ) (ty : ∀ g, A g ≃ ZMod d) (J : Fin 2 → Type) [∀ g, Fintype (J g)] (X : RowData C V d (fun g => Σ s : A g, Fin (m g s)) J), (∀ g x, (X.G g).ty (Sum.inl x) = ty g x.1) → (∀ g s, X.rkF g (ty g s) = m g s) ∧ ∃ F : RF.Flag X, ∀ g a c, (F.en g a c).1 = (ty g).symm a ∧ ((F.en g a c).2 : ℕ) = c := by
  intro C _ V d _ A _ m ty J _ X h
  have h1 : ∀ g s, X.rkF g (ty g s) = m g s := by
    intro g s
    unfold RowData.rkF
    simp only [h]
    convert card_sigma_fibre (m g) (ty g) s
  have h2 : ∀ g a, X.rkF g a = m g ((ty g).symm a) := by
    intro g a
    rw [← h1, Equiv.apply_symm_apply]
  refine ⟨h1, ⟨⟨fun g a c => ⟨(ty g).symm a, Fin.cast (h2 g a) c⟩, ?_, ?_⟩, fun g a c => ⟨rfl, rfl⟩⟩⟩
  · intro g a c c' hc
    exact Fin.cast_injective _ (eq_of_heq (Sigma.mk.inj hc).2)
  · intro g a c
    rw [h]
    exact Equiv.apply_symm_apply _ _

end GlobalTheory
