import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMat
open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Ar.Lines.Coords

variable {R : Type*} [CommRing R] [IsDomain R] {M : Type*} [AddCommGroup M] [Module R M]

theorem exists_relation [Module.Finite R M] {i : ℕ} {f : Fin i → M}
    (hf : LinearIndependent R f) (hi : i = Module.finrank R M) (x : M) :
    ∃ (D : R) (a : Fin i → R), D ≠ 0 ∧ D • x = ∑ j, a j • f j := by
  classical
  have hnot : ¬ LinearIndependent R (Fin.cons x f : Fin (i + 1) → M) := fun hli => by
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_fin] at this
    omega
  obtain ⟨g, hg, k, hk⟩ := Fintype.not_linearIndependent_iff.mp hnot
  rw [Fin.sum_univ_succ] at hg
  simp only [Fin.cons_zero, Fin.cons_succ] at hg
  have h0 : g 0 ≠ 0 := by
    intro h0
    rw [h0, zero_smul, zero_add] at hg
    have hz := Fintype.linearIndependent_iff.mp hf _ hg
    apply hk
    induction k using Fin.cases with
    | zero => exact h0
    | succ j => exact hz j
  refine ⟨g 0, fun j => -g j.succ, h0, ?_⟩
  simp only [neg_smul, Finset.sum_neg_distrib]
  exact eq_neg_of_add_eq_zero_left hg

theorem relation_cross {i : ℕ} {f : Fin i → M} (hf : LinearIndependent R f) {x : M}
    {D D' : R} {a a' : Fin i → R} (h : D • x = ∑ j, a j • f j)
    (h' : D' • x = ∑ j, a' j • f j) (j : Fin i) : D' * a j = D * a' j := by
  have key : ∑ j, (D' * a j - D * a' j) • f j = 0 := by
    simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, ← h, ← h']
    rw [smul_comm D' D x, sub_self]
  exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hf _ key j)

private theorem coord_lemma (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] {i : ℕ}
    {f : Fin i → M} (hf : LinearIndependent R f) {x : M} {D D' : R} {a a' : Fin i → R}
    (hD : D ≠ 0) (hD' : D' ≠ 0) (h : D • x = ∑ j, a j • f j) (h' : D' • x = ∑ j, a' j • f j)
    (j : Fin i) :
    algebraMap R K (a j) / algebraMap R K D = algebraMap R K (a' j) / algebraMap R K D' := by
  have hne : ∀ {E : R}, E ≠ 0 → algebraMap R K E ≠ 0 := fun hE h0 =>
    hE (IsFractionRing.injective R K (by rw [h0, map_zero]))
  rw [div_eq_div_iff (hne hD) (hne hD'), ← map_mul, ← map_mul, mul_comm (a j),
    relation_cross hf h h' j, mul_comm]

theorem exists_coordinates (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    [Module.Finite R M] [Module.IsTorsionFree R M] {i : ℕ} {f : Fin i → M}
    (hf : LinearIndependent R f) (hi : i = Module.finrank R M) :
    ∃ c : M →ₗ[R] (Fin i → K), Function.Injective c ∧ (∀ j, c (f j) = Pi.single j 1) ∧
      ∀ x, ∃ (D : R) (a : Fin i → R), D ≠ 0 ∧ D • x = ∑ j, a j • f j ∧
        ∀ j, algebraMap R K D * c x j = algebraMap R K (a j) := by
  classical
  choose Dx ax hDx hax using fun x => exists_relation hf hi x
  have hne : ∀ {D : R}, D ≠ 0 → algebraMap R K D ≠ 0 := fun hD h0 =>
    hD (IsFractionRing.injective R K (by rw [h0, map_zero]))
  have key : ∀ x (D : R) (a : Fin i → R), D ≠ 0 → D • x = ∑ j, a j • f j → ∀ j,
      algebraMap R K (ax x j) / algebraMap R K (Dx x) =
        algebraMap R K (a j) / algebraMap R K D :=
    fun x D a hD h j => coord_lemma K hf (hDx x) hD (hax x) h j
  let c : M →ₗ[R] (Fin i → K) :=
    { toFun := fun x j => algebraMap R K (ax x j) / algebraMap R K (Dx x)
      map_add' := fun x y => by
        funext j
        have hrel : (Dx x * Dx y) • (x + y) = ∑ j, (Dx y * ax x j + Dx x * ax y j) • f j := by
          rw [smul_add, mul_smul, mul_smul, smul_comm (Dx x) (Dx y) x, hax x, hax y,
            Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
          simp only [add_smul, mul_smul]
        dsimp only [Pi.add_apply]
        rw [key (x + y) _ _ (mul_ne_zero (hDx x) (hDx y)) hrel j,
          div_add_div _ _ (hne (hDx x)) (hne (hDx y))]
        simp only [map_add, map_mul]
        ring
      map_smul' := fun r x => by
        funext j
        have hrel : Dx x • (r • x) = ∑ j, (r * ax x j) • f j := by
          rw [smul_comm, hax x, Finset.smul_sum]
          simp only [mul_smul]
        dsimp only [Pi.smul_apply, RingHom.id_apply]
        rw [key (r • x) _ _ (hDx x) hrel j, Algebra.smul_def, map_mul]
        ring }
  have hc : ∀ x j, c x j = algebraMap R K (ax x j) / algebraMap R K (Dx x) := fun _ _ => rfl
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have ha : ∀ j, ax x j = 0 := fun j => by
      have := congrFun hx j
      rw [hc, Pi.zero_apply, div_eq_zero_iff] at this
      rcases this with h | h
      · exact IsFractionRing.injective R K (by rw [h, map_zero])
      · exact absurd h (hne (hDx x))
    have h0 : Dx x • x = 0 := by
      rw [hax x]
      simp [ha]
    exact (smul_eq_zero_iff_right (hDx x)).mp h0
  · intro j
    funext k
    have hrel : (1 : R) • f j = ∑ l, (Pi.single j (1 : R) : Fin i → R) l • f l := by
      rw [one_smul]
      simp [Pi.single_apply]
    rw [hc, key (f j) 1 _ one_ne_zero hrel k]
    by_cases hk : k = j
    · subst hk
      simp
    · simp [hk]
  · intro x
    exact ⟨Dx x, ax x, hDx x, hax x, fun j => by
      rw [hc]
      exact mul_div_cancel₀ _ (hne (hDx x))⟩

theorem coordinates_of_maximal_independent (L : Type) [Field L] [NumberField L] (M : Type)
    [AddCommGroup M] [Module (𝓞 L) M] [Module.Finite (𝓞 L) M] [Module.IsTorsionFree (𝓞 L) M]
    (i : ℕ) (f : Fin i → M) (hf : LinearIndependent (𝓞 L) f)
    (hi : i = Module.finrank (𝓞 L) M) :
    ∃ c : M →ₗ[𝓞 L] (Fin i → L), Function.Injective c ∧ (∀ j, c (f j) = Pi.single j 1) ∧
      ∀ x, ∃ (D : 𝓞 L) (a : Fin i → 𝓞 L), D ≠ 0 ∧ D • x = ∑ j, a j • f j ∧
        ∀ j, (D : L) * c x j = a j := by
  obtain ⟨c, h1, h2, h3⟩ := exists_coordinates L hf hi
  exact ⟨c, h1, h2, h3⟩

end GlobalTheory.CompanionTheory.Ar.Lines.Coords
