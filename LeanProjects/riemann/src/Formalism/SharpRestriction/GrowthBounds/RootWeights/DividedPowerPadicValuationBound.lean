import Formalism.SharpRestriction.GrowthBounds.RootWeights.IntegralPolyLinearMapClosed

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem choose_factorial_identity (α β f : ℕ) (h : f ≤ β) :
    β.choose f * ((β - f).factorial * (α + f).factorial) = (α + f).choose f * (β.factorial * α.factorial) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial h
  have h2 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left f α)
  rw [Nat.add_sub_cancel] at h2
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos f)
  calc f.factorial * (β.choose f * ((β - f).factorial * (α + f).factorial))
      = (β.choose f * f.factorial * (β - f).factorial) * (α + f).factorial := by ring
    _ = β.factorial * (α + f).factorial := by rw [h1]
    _ = β.factorial * ((α + f).choose f * f.factorial * α.factorial) := by rw [h2]
    _ = f.factorial * ((α + f).choose f * (β.factorial * α.factorial)) := by ring

theorem product_two_coordinates_swap {n : ℕ} (g g' : Fin n → ℕ) (a b : Fin n) (hab : a ≠ b)
    (h : ∀ c, c ≠ a → c ≠ b → g' c = g c) :
    (∏ c, g' c) * (g a * g b) = (∏ c, g c) * (g' a * g' b) := by
  classical
  have hs : ∀ f : Fin n → ℕ, ∏ c, f c = f a * f b * ∏ c ∈ (univ.erase a).erase b, f c := by
    intro f
    rw [← Finset.mul_prod_erase univ f (mem_univ a),
      ← Finset.mul_prod_erase (univ.erase a) f (mem_erase.2 ⟨hab.symm, mem_univ b⟩)]
    ring
  have hrest : ∏ c ∈ (univ.erase a).erase b, g' c = ∏ c ∈ (univ.erase a).erase b, g c :=
    prod_congr rfl fun c hc => h c (ne_of_mem_erase (mem_of_mem_erase hc)) (ne_of_mem_erase hc)
  rw [hs g', hs g, hrest]
  ring

theorem sum_single_apply_section {ι : Type} {n : ℕ} (g : ι → ι × Fin n) (hg : ∀ l, (g l).1 = l) (f : ι →₀ ℕ)
    (v : ι × Fin n) [Decidable (v = g v.1)] :
    (∑ l ∈ f.support, Finsupp.single (g l) (f l)) v = if v = g v.1 then f v.1 else 0 := by
  classical
  rw [Finsupp.finset_sum_apply]
  have key : ∀ l, g l = v → l = v.1 ∧ v = g v.1 := by
    rintro l rfl
    exact ⟨(hg l).symm, by rw [hg l]⟩
  split_ifs with hv
  · rw [Finset.sum_eq_single v.1]
    · rw [← hv, Finsupp.single_eq_same]
    · intro l _ hl
      rw [Finsupp.single_apply, if_neg]
      exact fun h => hl (key l h).1
    · intro hnot
      simp only [Finsupp.mem_support_iff, not_not] at hnot
      simp [hnot]
  · refine Finset.sum_eq_zero fun l _ => ?_
    rw [Finsupp.single_apply, if_neg]
    exact fun h => hv (key l h).2

theorem exponent_factorial_eq_prod {ι : Type} [Fintype ι] {n : ℕ} (m : ι × Fin n →₀ ℕ) :
    expFact m = ∏ l : ι, ∏ c : Fin n, (m (l, c)).factorial := by
  classical
  unfold expFact
  rw [Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero), Fintype.prod_prod_type]

theorem exponent_factorial_ne_zero {σ : Type} (m : σ →₀ ℕ) : expFact m ≠ 0 := by
  unfold expFact Finsupp.prod
  exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _

theorem divided_power_padic_valuation_bound {ι : Type} [Fintype ι] {n : ℕ} (p : ℕ) [Fact p.Prime] (src dst : ι → ι × Fin n)
    (hs : ∀ l, (src l).1 = l) (hd : ∀ l, (dst l).1 = l) (hne : ∀ l, src l ≠ dst l)
    (m : ι × Fin n →₀ ℕ) (f : ι →₀ ℕ) (zf : ι → ℤ) (hz : ∀ l, (zf l).natAbs = (m (src l)).choose (f l)) :
    (∏ l ∈ f.support, zf l) = 0 ∨ padicValNat p (expFact m) ≤ 2 * padicValInt p (∏ l ∈ f.support, zf l) +
      padicValNat p (expFact ((m - ∑ l ∈ f.support, Finsupp.single (src l) (f l)) +
        ∑ l ∈ f.support, Finsupp.single (dst l) (f l))) := by
  classical
  by_cases hall : ∀ l ∈ f.support, f l ≤ m (src l)
  swap
  ·
    left
    push_neg at hall
    obtain ⟨l, hl, hlt⟩ := hall
    apply Finset.prod_eq_zero hl
    have := hz l
    rw [Nat.choose_eq_zero_of_lt hlt] at this
    exact Int.natAbs_eq_zero.1 this
  have hall' : ∀ l, f l ≤ m (src l) := fun l => by
    by_cases hl : l ∈ f.support
    · exact hall l hl
    · simp only [Finsupp.mem_support_iff, not_not] at hl
      rw [hl]
      exact Nat.zero_le _
  right
  have hm' : ∀ x : ι × Fin n, ((m - ∑ l ∈ f.support, Finsupp.single (src l) (f l)) +
      ∑ l ∈ f.support, Finsupp.single (dst l) (f l)) x =
      (m x - (if x = src x.1 then f x.1 else 0)) + (if x = dst x.1 then f x.1 else 0) := by
    intro x
    rw [Finsupp.add_apply, Finsupp.tsub_apply, sum_single_apply_section src hs f x, sum_single_apply_section dst hd f x]
  set m' : ι × Fin n →₀ ℕ := (m - ∑ l ∈ f.support, Finsupp.single (src l) (f l)) +
      ∑ l ∈ f.support, Finsupp.single (dst l) (f l) with hm'def

  have hrow : ∀ l, (∏ c, (m (l, c)).factorial) * (m (dst l) + f l).choose (f l) =
      (∏ c, (m' (l, c)).factorial) * (m (src l)).choose (f l) := by
    intro l
    obtain ⟨a, ha⟩ : ∃ a, src l = (l, a) := ⟨(src l).2, Prod.ext (hs l) rfl⟩
    obtain ⟨b, hb⟩ : ∃ b, dst l = (l, b) := ⟨(dst l).2, Prod.ext (hd l) rfl⟩
    have hab : a ≠ b := fun h => hne l (by rw [ha, hb, h])
    have hma : m' (l, a) = m (l, a) - f l := by
      rw [hm']; simp [ha, hb, hab]
    have hmb : m' (l, b) = m (l, b) + f l := by
      rw [hm']; simp [ha, hb, hab, Ne.symm hab]
    have hmc : ∀ c, c ≠ a → c ≠ b → m' (l, c) = m (l, c) := by
      intro c hca hcb
      rw [hm']; simp [ha, hb, hca, hcb]
    have hF : f l ≤ m (l, a) := ha ▸ hall' l
    have h2 := product_two_coordinates_swap (fun c => (m (l, c)).factorial) (fun c => (m' (l, c)).factorial) a b hab
      (fun c hca hcb => by simp only [hmc c hca hcb])
    beta_reduce at h2
    rw [hma, hmb] at h2
    have h3 := choose_factorial_identity (m (l, b)) (m (l, a)) (f l) hF
    rw [ha, hb]
    apply Nat.eq_of_mul_eq_mul_right
      (Nat.mul_pos (Nat.factorial_pos (m (l, a))) (Nat.factorial_pos (m (l, b))))
    calc (∏ c, (m (l, c)).factorial) * (m (l, b) + f l).choose (f l) *
          ((m (l, a)).factorial * (m (l, b)).factorial)
        = (∏ c, (m (l, c)).factorial) * ((m (l, b) + f l).choose (f l) *
          ((m (l, a)).factorial * (m (l, b)).factorial)) := by ring
      _ = (∏ c, (m (l, c)).factorial) * ((m (l, a)).choose (f l) *
          ((m (l, a) - f l).factorial * (m (l, b) + f l).factorial)) := by rw [h3]
      _ = (m (l, a)).choose (f l) * ((∏ c, (m (l, c)).factorial) *
          ((m (l, a) - f l).factorial * (m (l, b) + f l).factorial)) := by ring
      _ = (m (l, a)).choose (f l) * ((∏ c, (m' (l, c)).factorial) *
          ((m (l, a)).factorial * (m (l, b)).factorial)) := by rw [h2]
      _ = (∏ c, (m' (l, c)).factorial) * (m (l, a)).choose (f l) *
          ((m (l, a)).factorial * (m (l, b)).factorial) := by ring
  have htot : expFact m * ∏ l, (m (dst l) + f l).choose (f l) =
      expFact m' * ∏ l, (m (src l)).choose (f l) := by
    rw [exponent_factorial_eq_prod m, exponent_factorial_eq_prod m', ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun l _ => hrow l
  have hY : (∏ l ∈ f.support, zf l).natAbs = ∏ l, (m (src l)).choose (f l) := by
    have hnat : (∏ l ∈ f.support, zf l).natAbs = ∏ l ∈ f.support, (zf l).natAbs := by
      first
        | exact map_prod Int.natAbsHom zf f.support
        | simpa using map_prod Int.natAbsHom zf f.support
    rw [hnat, Finset.prod_congr rfl (fun l _ => hz l)]
    refine Finset.prod_subset (Finset.subset_univ _) fun l _ hl => ?_
    simp only [Finsupp.mem_support_iff, not_not] at hl
    rw [hl, Nat.choose_zero_right]
  have hX0 : ∏ l, (m (dst l) + f l).choose (f l) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun l _ => (Nat.choose_pos (Nat.le_add_left _ _)).ne'
  have hY0 : ∏ l, (m (src l)).choose (f l) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun l _ => (Nat.choose_pos (hall' l)).ne'
  have hv := congrArg (padicValNat p) htot
  rw [padicValNat.mul (exponent_factorial_ne_zero m) hX0, padicValNat.mul (exponent_factorial_ne_zero m') hY0] at hv
  rw [show padicValInt p (∏ l ∈ f.support, zf l) =
    padicValNat p (∏ l ∈ f.support, zf l).natAbs from rfl, hY]
  omega

end Formalism.MainNotions.G.GLWeightTheory
