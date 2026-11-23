import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore

namespace GlobalTheory.Cut

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

theorem cutVal_exists_single {O X : Type} [CommRing O] [IsDomain O] [Fintype X]
    (T : Subalgebra O (X → O)) (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) (x : X) :
    ∃ g ∈ T, g x ≠ 0 ∧ ∀ y, y ≠ x → g y = 0 := by
  classical
  have key : ∀ y : X, ∃ f ∈ T, f x ≠ 0 ∧ (y ≠ x → f y = 0) := by
    intro y
    by_cases hy : y = x
    · exact ⟨1, one_mem _, one_ne_zero, fun h => absurd hy h⟩
    · obtain ⟨f, hf, hne⟩ := hsep y x hy
      refine ⟨f - algebraMap _ _ (f y), sub_mem hf (Subalgebra.algebraMap_mem _ _), ?_, fun _ => ?_⟩
      · simpa [sub_eq_zero] using hne.symm
      · simp
  choose f hf h1 h2 using key
  refine ⟨∏ y, f y, prod_mem fun y _ => hf y, ?_, fun y hy => ?_⟩
  · rw [Finset.prod_apply]
    exact Finset.prod_ne_zero_iff.2 fun y _ => h1 y
  · rw [Finset.prod_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ y) (h2 y hy)

theorem cutVal_coord_eq_zero {O X X' ι : Type} [CommRing O] [IsDomain O] [Fintype X] [Fintype ι]
    (T : Subalgebra O (X → O)) (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y)
    (p : X' → X) (b : ι → X' → O)
    (huniq : ∀ cf : ι → T, (0 : X' → O) = ∑ k, ((fun x' => (cf k : X → O) (p x')) : X' → O) * b k →
      cf = 0)
    (cf : ι → T) (x : X)
    (h0 : ∀ x', p x' = x → (∑ k, ((fun x' => (cf k : X → O) (p x')) : X' → O) * b k) x' = 0)
    (k : ι) : (cf k : X → O) x = 0 := by
  obtain ⟨g, hg, hx, hy⟩ := cutVal_exists_single T hsep x
  have h := huniq (fun k => ⟨g, hg⟩ * cf k) (by
    funext x'
    have : (∑ k, ((fun x' => (((⟨g, hg⟩ : T) * cf k : T) : X → O) (p x')) : X' → O) * b k) x' =
        g (p x') * (∑ k, ((fun x' => (cf k : X → O) (p x')) : X' → O) * b k) x' := by
      simp [Finset.sum_apply, Finset.mul_sum, mul_assoc]
    rw [this]
    by_cases hp : p x' = x
    · rw [h0 x' hp]; simp
    · rw [hy _ hp]; simp)
  have h2 : g x * (cf k : X → O) x = 0 := by
    have := congrArg (fun c : ι → T => (c k : X → O) x) h
    simpa using this
  exact (mul_eq_zero.1 h2).resolve_left hx

theorem value_mem_ccOff :
    ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → ∀ f ∈ S.T', (∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → f x' = 0) → f S.π' ∈ ccOff i Xs π := by
  intro D i r ρ π Xs S _ hS _ f hf h0
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, -, ⟨b, -, hb⟩, -⟩, -, ⟨hπ, -⟩, -⟩ := hS
  obtain ⟨cf, hcf, -⟩ := hb f hf
  have huniq : ∀ c : Fin D.R.t.factorial → D.nd.T i,
      (0 : S.X' → D.nd.O i) = ∑ k, ((fun x' => (c k : D.nd.X i → D.nd.O i) (S.p x')) :
        S.X' → D.nd.O i) * b k → c = 0 := by
    intro c hc
    obtain ⟨c0, -, hc0⟩ := hb 0 (zero_mem _)
    rw [hc0 c hc, hc0 0 (by funext x'; simp)]
  have hz : ∀ k, ∀ x ∈ Xs, x ∉ D.nd.Z i → (cf k : D.nd.X i → D.nd.O i) x = 0 := by
    intro k x hx hZ
    refine cutVal_coord_eq_zero (D.nd.T i) (D.nd.T_sep i) S.p b huniq cf x (fun x' hp => ?_) k
    rw [← hcf]
    exact h0 x' (hp ▸ hx) (hp ▸ hZ)
  rw [hcf, Finset.sum_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [Pi.mul_apply]
  refine Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨cf k, (cf k).2, hz k, ?_⟩)
  rw [hπ]

end GlobalTheory.Cut
