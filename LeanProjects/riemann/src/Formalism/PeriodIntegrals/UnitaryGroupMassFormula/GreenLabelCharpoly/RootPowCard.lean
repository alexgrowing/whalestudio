import Mathlib

open Polynomial IntermediateField

noncomputable section

namespace PI.GreenLabelMapW

variable {K : Type} [Field K] [Fintype K]

theorem root_ne_zero {P : K[X]} (hm : P.Monic) (hi : Irreducible P) (hX : P ≠ X)
    {w : AlgebraicClosure K} (hw : aeval w P = 0) : w ≠ 0 := by
  rintro rfl
  apply hX
  have h0 : P.coeff 0 = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_at_zero] at hw
    exact (algebraMap K (AlgebraicClosure K)).injective (by rw [hw, map_zero])
  have hXP : X ∣ P := Polynomial.X_dvd_iff.2 h0
  have hPX : P ∣ X := Polynomial.irreducible_X.dvd_symm hi hXP
  exact Polynomial.eq_of_monic_of_associated hm Polynomial.monic_X (associated_of_dvd_dvd hPX hXP)

theorem root_pow_card {P : K[X]} (hm : P.Monic) (hi : Irreducible P) (hX : P ≠ X)
    {w : AlgebraicClosure K} (hw : aeval w P = 0) :
    w ^ (Fintype.card K ^ P.natDegree - 1) = 1 := by
  have hint : IsIntegral K w := ⟨P, hm, hw⟩
  have hmin : P = minpoly K w := minpoly.eq_of_irreducible_of_monic hi hw hm
  have hw0 := root_ne_zero hm hi hX hw
  haveI : FiniteDimensional K K⟮w⟯ := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K⟮w⟯ := Module.finite_of_finite K
  letI : Fintype K⟮w⟯ := Fintype.ofFinite _
  have hcard : Fintype.card K⟮w⟯ = Fintype.card K ^ P.natDegree := by
    rw [Module.card_eq_pow_finrank (K := K), IntermediateField.adjoin.finrank hint, ← hmin]
  have h1 := FiniteField.pow_card_sub_one_eq_one (⟨w, IntermediateField.mem_adjoin_simple_self K w⟩ : K⟮w⟯)
    (fun h => hw0 (by simpa using congrArg Subtype.val h))
  rw [hcard] at h1
  simpa using congrArg Subtype.val h1

theorem conj_roots {P : K[X]} (hm : P.Monic) (hi : Irreducible P) {w : AlgebraicClosure K}
    (hw : aeval w P = 0) (f : AlgebraicClosure K → AlgebraicClosure K)
    (hf : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure K),
      f (σ x) = σ (f x)) (y : AlgebraicClosure K) :
    aeval y (minpoly K (f w)) = 0 ↔ ∃ r, aeval r P = 0 ∧ f r = y := by
  have halg : ∀ z : AlgebraicClosure K, IsAlgebraic K z := fun z => Algebra.IsAlgebraic.isAlgebraic z
  have hmin : P = minpoly K w := minpoly.eq_of_irreducible_of_monic hi hw hm
  constructor
  · intro hy
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root (halg (f w)) hy
    refine ⟨σ.symm w, ?_, ?_⟩
    · simpa [hw] using Polynomial.aeval_algHom_apply (σ.symm : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) w P
    · rw [hf, ← hσ, AlgEquiv.symm_apply_apply]
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root (halg w) (by rw [← hmin]; exact hr)
    rw [← hσ, hf, show minpoly K (σ (f r)) = minpoly K (f r) from
      minpoly.algHom_eq (σ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) σ.injective (f r)]
    exact minpoly.aeval K (f r)

theorem aroots_eq_map {P : K[X]} (hm : P.Monic) (hi : Irreducible P) {w : AlgebraicClosure K}
    (hw : aeval w P = 0) (f : AlgebraicClosure K → AlgebraicClosure K)
    (hf : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure K),
      f (σ x) = σ (f x))
    (hinj : ∀ r₁ r₂ : AlgebraicClosure K, aeval r₁ P = 0 → aeval r₂ P = 0 → f r₁ = f r₂ → r₁ = r₂) :
    (minpoly K (f w)).aroots (AlgebraicClosure K) = (P.aroots (AlgebraicClosure K)).map f := by
  have hsep : P.Separable := PerfectField.separable_of_irreducible hi
  have hint : IsIntegral K (f w) := Algebra.IsIntegral.isIntegral _
  have hsep2 : (minpoly K (f w)).Separable := PerfectField.separable_of_irreducible (minpoly.irreducible hint)
  have hP0 : P ≠ 0 := hm.ne_zero
  have hnd1 : ((minpoly K (f w)).aroots (AlgebraicClosure K)).Nodup :=
    (Polynomial.nodup_aroots_iff_of_splits (minpoly.ne_zero hint) (IsAlgClosed.splits _)).2 hsep2
  have hnd2 : (P.aroots (AlgebraicClosure K)).Nodup :=
    (Polynomial.nodup_aroots_iff_of_splits hP0 (IsAlgClosed.splits _)).2 hsep
  have hnd3 : ((P.aroots (AlgebraicClosure K)).map f).Nodup :=
    Multiset.Nodup.map_on (fun r₁ h₁ r₂ h₂ h =>
      hinj r₁ r₂ (Polynomial.mem_aroots.1 h₁).2 (Polynomial.mem_aroots.1 h₂).2 h) hnd2
  refine (Multiset.Nodup.ext hnd1 hnd3).2 fun y => ?_
  rw [Polynomial.mem_aroots, Multiset.mem_map]
  constructor
  · rintro ⟨-, hy⟩
    obtain ⟨r, hr, hry⟩ := (conj_roots hm hi hw f hf y).1 hy
    exact ⟨r, Polynomial.mem_aroots.2 ⟨hP0, hr⟩, hry⟩
  · rintro ⟨r, hr, hry⟩
    exact ⟨minpoly.ne_zero hint, (conj_roots hm hi hw f hf y).2 ⟨r, (Polynomial.mem_aroots.1 hr).2, hry⟩⟩

theorem natDegree_minpoly_eq {P : K[X]} (hm : P.Monic) (hi : Irreducible P)
    {w : AlgebraicClosure K} (hw : aeval w P = 0) (f : AlgebraicClosure K → AlgebraicClosure K)
    (hf : ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure K),
      f (σ x) = σ (f x))
    (hinj : ∀ r₁ r₂ : AlgebraicClosure K, aeval r₁ P = 0 → aeval r₂ P = 0 → f r₁ = f r₂ → r₁ = r₂) :
    (minpoly K (f w)).natDegree = P.natDegree := by
  have e1 : ∀ Q : K[X], (Q.aroots (AlgebraicClosure K)).card = Q.natDegree := fun Q => by
    unfold Polynomial.aroots
    rw [IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map]
  rw [← e1, ← e1, aroots_eq_map hm hi hw f hf hinj, Multiset.card_map]

end PI.GreenLabelMapW
