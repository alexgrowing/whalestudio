import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeaklyRegularRelationsEqKoszulRelationsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Koszul

noncomputable def pairEquiv (g : ℕ) : {z : Sym2 (Fin g) // ¬ z.IsDiag} ≃ Fin (g.choose 2) :=
  Fintype.equivFinOfCardEq (by rw [Sym2.card_subtype_not_diag, Fintype.card_fin])

variable {O : Type} [CommRing O] {g : ℕ}

noncomputable def upper (x : Fin (g.choose 2) → O) : Matrix (Fin g) (Fin g) O :=
  fun i j => if h : i < j then
    x (pairEquiv g ⟨s(i, j), by rw [Sym2.mk_isDiag_iff]; exact h.ne⟩) else 0

noncomputable def skew (x : Fin (g.choose 2) → O) : Matrix (Fin g) (Fin g) O :=
  fun i j => upper x i j - upper x j i

lemma upper_add (x x' : Fin (g.choose 2) → O) : upper (x + x') = upper x + upper x' := by
  ext i j; simp only [upper, Matrix.add_apply]; split_ifs <;> simp

lemma upper_smul (a : O) (x : Fin (g.choose 2) → O) : upper (a • x) = a • upper x := by
  ext i j; simp only [upper, Matrix.smul_apply]; split_ifs <;> simp

lemma skew_add (x x' : Fin (g.choose 2) → O) : skew (x + x') = skew x + skew x' := by
  ext i j; simp only [skew, upper_add, Matrix.add_apply]; ring

lemma skew_smul (a : O) (x : Fin (g.choose 2) → O) : skew (a • x) = a • skew x := by
  ext i j; simp only [skew, upper_smul, Matrix.smul_apply, smul_eq_mul]; ring

noncomputable def d₂ (f : Fin g → O) : (Fin (g.choose 2) → O) →ₗ[O] (Fin g → O) where
  toFun x := (skew x).mulVec f
  map_add' x x' := by rw [skew_add, Matrix.add_mulVec]
  map_smul' a x := by
    rw [skew_smul]; ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

lemma d₂_apply (f : Fin g → O) (x : Fin (g.choose 2) → O) : d₂ f x = (skew x).mulVec f := rfl

lemma sum_skew_mulVec (f : Fin g → O) (x : Fin (g.choose 2) → O) :
    ∑ i, (skew x).mulVec f i * f i = 0 := by
  simp only [Matrix.mulVec, dotProduct, skew, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [sub_eq_zero, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma exists_skew_eq (c : Matrix (Fin g) (Fin g) O) (hd : ∀ i, c i i = 0)
    (hs : ∀ i j, c i j = - c j i) : ∃ x : Fin (g.choose 2) → O, skew x = c := by
  let F : Sym2 (Fin g) → O :=
    Sym2.lift ⟨fun i j => c (min i j) (max i j), fun i j => show c (min i j) (max i j) = c (min j i) (max j i) by rw [min_comm, max_comm]⟩
  refine ⟨fun k => F ((pairEquiv g).symm k).1, ?_⟩
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [skew, upper, h, lt_asymm h, F, min_eq_left h.le, max_eq_right h.le]
  · simp [skew, upper, hd]
  · simp [skew, upper, h, lt_asymm h, F, min_eq_left h.le, max_eq_right h.le, ← hs i j]

end GlobalTheory.Koszul

open GlobalTheory.Koszul in

theorem GlobalTheory.koszul_resolution_three_terms : ∀ (O : Type) [CommRing O] (g : ℕ) (f : Fin g → O), RingTheory.Sequence.IsWeaklyRegular O (List.ofFn f) → ∃ (e₁ : (Fin g → O) →ₗ[O] O) (e₂ : (Fin (g.choose 2) → O) →ₗ[O] (Fin g → O)), Function.Exact e₁ (Ideal.span (Set.range f)).mkQ ∧ Function.Exact e₂ e₁ ∧ (∀ x, e₁ x ∈ Ideal.span (Set.range f)) ∧ ∀ x i, e₂ x i ∈ Ideal.span (Set.range f) := by
  intro O _ g f hreg
  refine ⟨Fintype.linearCombination O f, d₂ f, ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.exact_iff, Submodule.ker_mkQ, Fintype.range_linearCombination]
  · intro y
    constructor
    · intro hy
      rw [Fintype.linearCombination_apply] at hy
      obtain ⟨c, hd, hs, rfl⟩ := GlobalTheory.T.weaklyRegular_relations_eq_koszulRelations O g f hreg y (by simpa [smul_eq_mul] using hy)
      obtain ⟨x, hx⟩ := exists_skew_eq c hd hs
      exact ⟨x, by rw [d₂_apply, hx]⟩
    · rintro ⟨x, rfl⟩
      rw [Fintype.linearCombination_apply, d₂_apply]
      simpa [smul_eq_mul] using sum_skew_mulVec f x
  · intro x
    show _ ∈ Submodule.span O (Set.range f)
    rw [← Fintype.range_linearCombination]
    exact LinearMap.mem_range_self _ x
  · intro x i
    rw [d₂_apply]
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self j))
