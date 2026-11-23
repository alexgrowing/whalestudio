import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CarSumSqZeroOfAnti

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem csq_sum_univ_pm {R : Type*} [AddCommMonoid R] (ε : Fin n → Bool) (f : Fin n → R) :
    ∑ a, f a = ∑ a ∈ plusIdx ε, f a + ∑ a ∈ minusIdx ε, f a := by
  unfold plusIdx minusIdx
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun a => ε a = true) f]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext a
  simp

theorem sum_comm_pair_pair {R : Type*} [AddCommMonoid R] {ι κ ι' κ' : Type*} (s : Finset ι) (s' : Finset ι')
    (t : Finset κ) (t' : Finset κ') (f : ι → ι' → κ → κ' → R) :
    ∑ a ∈ s, ∑ b ∈ s', ∑ i ∈ t, ∑ j ∈ t', f a b i j = ∑ i ∈ t, ∑ j ∈ t', ∑ a ∈ s, ∑ b ∈ s', f a b i j := by
  calc _ = ∑ a ∈ s, ∑ i ∈ t, ∑ b ∈ s', ∑ j ∈ t', f a b i j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a ∈ s, ∑ i ∈ t, ∑ j ∈ t', ∑ b ∈ s', f a b i j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i ∈ t, ∑ a ∈ s, ∑ j ∈ t', ∑ b ∈ s', f a b i j := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem csq_filter_eq_plus (ε : Fin n → Bool) {a : Fin n} (ha : a ∈ plusIdx ε) :
    univ.filter (fun b => ε b = ε a) = plusIdx ε := by
  have h : ε a = true := by simpa [plusIdx] using ha
  ext b
  simp [plusIdx, h]

theorem csq_filter_eq_minus (ε : Fin n → Bool) {a : Fin n} (ha : a ∈ minusIdx ε) :
    univ.filter (fun b => ε b = ε a) = minusIdx ε := by
  have h : ε a = false := by simpa [minusIdx] using ha
  ext b
  simp [minusIdx, h]

theorem casimirK_pm {M : Type*} [AddCommGroup M] [Module ℂ M] (ε : Fin n → Bool)
    (F : Fin n → Fin n → Module.End ℂ M) :
    casimirK ε F = ∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε, F a b * F b a +
      ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, F a b * F b a := by
  unfold casimirK
  rw [csq_sum_univ_pm ε]
  congr 1
  · exact Finset.sum_congr rfl fun a ha => by rw [csq_filter_eq_plus ε ha]
  · exact Finset.sum_congr rfl fun a ha => by rw [csq_filter_eq_minus ε ha]

theorem csq_sgE_pp (ε : Fin n → Bool) (cp cm : Fin n → Fin n → Module.End ℂ W) {a b : Fin n}
    (ha : a ∈ plusIdx ε) (hb : b ∈ plusIdx ε) :
    sgE ε cp cm a b = ∑ x ∈ minusIdx ε, cp a x * cm b x := by
  have ha' : ε a = true := by simpa [plusIdx] using ha
  have hb' : ε b = true := by simpa [plusIdx] using hb
  simp [sgE, ha', hb']

theorem csq_sgE_mm (ε : Fin n → Bool) (cp cm : Fin n → Fin n → Module.End ℂ W) {a b : Fin n}
    (ha : a ∈ minusIdx ε) (hb : b ∈ minusIdx ε) :
    sgE ε cp cm a b = -∑ i ∈ plusIdx ε, cp i b * cm i a := by
  have ha' : ε a = false := by simpa [minusIdx] using ha
  have hb' : ε b = false := by simpa [minusIdx] using hb
  simp [sgE, ha', hb']

theorem csq_two_rhoHol_plus (ε : Fin n → Bool) {a : Fin n} (ha : a ∈ plusIdx ε) :
    (2 : ℂ) * ((rhoHol ε a : ℝ) : ℂ) = (qOf ε : ℂ) := by
  have ha' : ε a = true := by simpa [plusIdx] using ha
  rw [show rhoHol ε a = (qOf ε : ℝ) / 2 by simp [rhoHol, ha']]
  push_cast
  ring

theorem csq_two_rhoHol_minus (ε : Fin n → Bool) {a : Fin n} (ha : a ∈ minusIdx ε) :
    (2 : ℂ) * ((rhoHol ε a : ℝ) : ℂ) = -(pOf ε : ℂ) := by
  have ha' : ε a = false := by simpa [minusIdx] using ha
  rw [show rhoHol ε a = -(pOf ε : ℝ) / 2 by simp [rhoHol, ha']]
  push_cast
  ring

theorem two_rho_sum {M : Type*} [AddCommGroup M] [Module ℂ M] (ε : Fin n → Bool)
    (F : Fin n → Module.End ℂ M) :
    (2 : ℂ) • ∑ a, ((rhoHol ε a : ℝ) : ℂ) • F a =
      ∑ a ∈ plusIdx ε, (qOf ε : ℂ) • F a - ∑ a ∈ minusIdx ε, (pOf ε : ℂ) • F a := by
  rw [Finset.smul_sum, csq_sum_univ_pm ε, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun a ha => by rw [smul_smul, csq_two_rhoHol_plus ε ha]
  · exact Finset.sum_congr rfl fun a ha => by rw [smul_smul, csq_two_rhoHol_minus ε ha, neg_smul]

theorem casimir_pm {E : Fin n → Fin n → Module.End ℂ W} (hE : IsGlRep E) (ε : Fin n → Bool) :
    casimir E = casimirK ε E + (2 : ℂ) • ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, E i a * E a i -
      (2 : ℂ) • ∑ a, ((rhoHol ε a : ℝ) : ℂ) • E a a := by
  have hsplit : casimir E = (∑ a ∈ plusIdx ε, ∑ b ∈ plusIdx ε, E a b * E b a +
      ∑ a ∈ plusIdx ε, ∑ b ∈ minusIdx ε, E a b * E b a) +
      (∑ a ∈ minusIdx ε, ∑ b ∈ plusIdx ε, E a b * E b a +
      ∑ a ∈ minusIdx ε, ∑ b ∈ minusIdx ε, E a b * E b a) := by
    unfold casimir
    rw [csq_sum_univ_pm ε]
    congr 1
    · rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => csq_sum_univ_pm ε _
    · rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => csq_sum_univ_pm ε _

  have h1 : ∀ i a : Fin n, E a i * E i a = E i a * E a i - E i i + E a a := by
    intro i a
    have h := hE i a a i
    rw [if_pos rfl, if_pos rfl] at h
    rw [sub_add, ← h]
    abel
  have hcross : ∑ a ∈ minusIdx ε, ∑ b ∈ plusIdx ε, E a b * E b a =
      ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, E i a * E a i -
        (qOf ε : ℂ) • ∑ i ∈ plusIdx ε, E i i + (pOf ε : ℂ) • ∑ a ∈ minusIdx ε, E a a := by
    rw [Finset.sum_comm]
    calc ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, E a i * E i a
        = ∑ i ∈ plusIdx ε, ∑ a ∈ minusIdx ε, (E i a * E a i - E i i + E a a) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => h1 i a
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.smul_sum, Nat.cast_smul_eq_nsmul]
        rfl
  have h2 := two_rho_sum ε (fun a => E a a)
  rw [hsplit, casimirK_pm, hcross, h2, two_smul, ← Finset.smul_sum, ← Finset.smul_sum]
  abel

end ReciprocityTheory.ChartRestriction.DS
