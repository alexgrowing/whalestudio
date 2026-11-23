import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff

namespace GlobalTheory.Proof.ScalarPart

theorem sum_le_prod_of_two_le {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 2 ≤ x i) : ∑ i ∈ s, x i ≤ ∏ i ∈ s, x i := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a t ha ht ih =>
    rw [Finset.sum_cons, Finset.prod_cons]
    have hxa : 2 ≤ x a := hx a (Finset.mem_cons_self a t)
    have ht' : ∀ i ∈ t, 2 ≤ x i := fun i hi => hx i (Finset.mem_cons_of_mem hi)
    have h1 := ih ht'
    obtain ⟨j, hj⟩ := ht
    have h2 : x j ≤ ∑ i ∈ t, x i :=
      Finset.single_le_sum (fun i hi => by linarith [ht' i hi]) hj
    have h3 : 2 ≤ ∏ i ∈ t, x i := by linarith [ht' j hj]
    nlinarith

end GlobalTheory.Proof.ScalarPart

open GlobalTheory.Proof.ScalarPart in

theorem GlobalTheory.Proof.scalarBounds_of_norm_le_one :
    ∀ {X : Type} [TopologicalSpace X] {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ)
      (D : Fin m → Set X), (∀ i y, normSec (L i) (s i) y ≤ 1) →
      (∀ y, y ∉ ⋃ i, D i → ∀ i, normSec (L i) (s i) y ≠ 0) → ScalarBounds L s D := by
  intro X _ m L s D hle hne y hy
  set n : Fin m → ℝ := fun i => normSec (L i) (s i) y with hn
  have n0 : ∀ i, 0 ≤ n i := fun i => by
    simp only [hn, normSec]; positivity
  have n1 : ∀ i, n i ≤ 1 := fun i => hle i y
  have nne : ∀ i, n i ≠ 0 := hne y hy
  set a : Fin m → ℝ := fun i => Real.log (n i ^ 2) with ha
  have a0 : ∀ i, a i ≤ 0 := fun i =>
    Real.log_nonpos (sq_nonneg _) (pow_le_one₀ (n0 i) (n1 i))
  have hrc : ∀ i, rComp L s i y = Real.exp 1 - a i := fun i => rfl
  have hrt : rTot L s y = Real.exp 1 - ∑ i, a i := by
    simp only [rTot, ha]
    rw [← Finset.prod_pow, Real.log_prod]
    intro i _; exact pow_ne_zero _ (nne i)
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hge : ∀ i, Real.exp 1 ≤ rComp L s i y := fun i => by rw [hrc]; linarith [a0 i]
  have hle' : ∀ i, rComp L s i y ≤ rTot L s y := fun i => by
    rw [hrc, hrt]
    have : ∑ l, a l ≤ a i := by
      have h := Finset.single_le_sum (f := fun l => -a l) (fun l _ => by linarith [a0 l])
        (Finset.mem_univ i)
      simp only [Finset.sum_neg_distrib] at h
      linarith
    linarith
  refine ⟨hge, ?_, hle', ?_⟩
  · rw [hrt]; simp only [hrc, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  · intro hm
    have hpos : ∀ i, 0 < rComp L s i y := fun i => by linarith [hge i]
    have hrpos : 0 < rTot L s y := by
      have i0 : Fin m := ⟨0, hm⟩
      linarith [hle' i0, hpos i0]
    constructor
    · rw [← Real.log_prod (fun i _ => (hpos i).ne')]
      apply Real.log_le_log hrpos
      have hsum : rTot L s y ≤ ∑ i, rComp L s i y := by
        rw [hrt]; simp only [hrc, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        have : (1 : ℝ) ≤ m := by exact_mod_cast hm
        nlinarith [Real.exp_pos 1]
      have hne' : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
      exact hsum.trans (sum_le_prod_of_two_le _ hne' _ (fun i _ => he.trans (hge i)))
    · have : ∀ i ∈ (Finset.univ : Finset (Fin m)),
          Real.log (rComp L s i y) ≤ Real.log (rTot L s y) :=
        fun i _ => Real.log_le_log (hpos i) (hle' i)
      have h := Finset.sum_le_sum this
      simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
