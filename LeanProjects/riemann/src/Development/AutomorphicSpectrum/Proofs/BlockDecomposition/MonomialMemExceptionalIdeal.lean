import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4
open CrystallineSemistableComparison.Onto

theorem sub_oneE_mem_cone {n d : ℕ} {S : Finset (Fin d)} {g : Gam n d}
    (hg : g ∈ (cone S : AddSubmonoid (Gam n d))) (ht : 1 ≤ tdeg g) (k : Fin d)
    (hk : k ∈ S ∨ 1 ≤ g (Sum.inr k)) :
    g - oneE (Sum.inr k) ∈ (cone S : AddSubmonoid (Gam n d)) := by
  have hg' : (∀ l, 0 ≤ g (Sum.inl l)) ∧ (∀ j, j ∉ S → 0 ≤ g (Sum.inr j)) ∧ 0 ≤ tdeg g := hg
  obtain ⟨h1, h2, _⟩ := hg'
  show (∀ l, 0 ≤ (g - oneE (Sum.inr k) : Gam n d) (Sum.inl l)) ∧
    (∀ j, j ∉ S → 0 ≤ (g - oneE (Sum.inr k) : Gam n d) (Sum.inr j)) ∧ 0 ≤ tdeg (g - oneE (Sum.inr k))
  refine ⟨fun l => ?_, fun j hj => ?_, ?_⟩
  · simp only [oneE, Pi.sub_apply]
    rw [Pi.single_eq_of_ne Sum.inl_ne_inr, sub_zero]
    exact h1 l
  · by_cases hjk : j = k
    · subst hjk
      have h1' : 1 ≤ g (Sum.inr j) := hk.resolve_left hj
      simp only [oneE, Pi.sub_apply, Pi.single_eq_same]
      omega
    · simp only [oneE, Pi.sub_apply]
      rw [Pi.single_eq_of_ne (fun h => hjk (Sum.inr_injective h)), sub_zero]
      exact h2 j hj
  · have hs : ∑ j, (oneE (Sum.inr k) : Gam n d) (Sum.inr j) = 1 := by
      rw [Finset.sum_eq_single k]
      · simp [oneE]
      · intro b _ hb
        simp only [oneE]
        exact Pi.single_eq_of_ne (fun h => hb (Sum.inr_injective h)) _
      · intro h
        exact absurd (Finset.mem_univ k) h
    show 0 ≤ ∑ j, (g - oneE (Sum.inr k) : Gam n d) (Sum.inr j)
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    rw [hs]
    have ht' : 1 ≤ ∑ j, g (Sum.inr j) := ht
    omega

theorem monomial_mem_exceptional_ideal {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (g : Gam n d)
    (hg : g ∈ (cone S : AddSubmonoid (Gam n d))) (ht : 1 ≤ tdeg g) : mon K g hg ∈ I0 n K S := by
  have hex : ∃ k, (S = ∅ ∨ k ∈ S) ∧ (k ∈ S ∨ 1 ≤ g (Sum.inr k)) := by
    by_cases hS : S = ∅
    · by_contra hno
      push_neg at hno
      have hsum : ∑ j, g (Sum.inr j) ≤ 0 := Finset.sum_nonpos fun j _ => by
        have := (hno j (Or.inl hS)).2
        omega
      have ht' : 1 ≤ ∑ j, g (Sum.inr j) := ht
      omega
    · obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.2 hS
      exact ⟨k, Or.inr hk, Or.inl hk⟩
  obtain ⟨k, hkS, hk⟩ := hex
  have h' := sub_oneE_mem_cone hg ht k hk
  have hmul : mon K g hg =
      mon K (oneE (Sum.inr k)) (oneE_mem S _) * mon K (g - oneE (Sum.inr k)) h' := by
    simp only [mon, AddMonoidAlgebra.single_mul_single, mul_one]
    congr 1
    ext1
    simp
  rw [hmul]
  unfold I0
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨k, hkS, rfl⟩)

end GlobalTheory.CompanionTheory.SurjectionOntoH4
