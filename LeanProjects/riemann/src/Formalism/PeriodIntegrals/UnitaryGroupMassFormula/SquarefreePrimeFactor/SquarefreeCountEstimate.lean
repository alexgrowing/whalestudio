import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreePrimeFactor.MonicDegFnNatDegree

open Polynomial

noncomputable section

namespace PI.SqfPrimeFactor.W

open PI.SqfLab

def bad (g r p : ℕ) [Fact g.Prime] : Finset (ZMod g)[X] :=
  (irrDeg g p ×ˢ monicDeg g (r - p)).image (fun x => x.1 * x.2)

section

variable {g : ℕ} [Fact g.Prime]

theorem irr_dvd_of_dvd_mul {q q' h : (ZMod g)[X]} (hq : Irreducible q) (hh : h ≠ 0)
    (hdeg : h.natDegree < q.natDegree) (hd : q ∣ q' * h) : q ∣ q' := by
  rcases hq.prime.dvd_or_dvd hd with h1 | h1
  · exact h1
  · exact absurd (natDegree_le_of_dvd h1 hh) (not_le.2 hdeg)

theorem mul_injOn (r p : ℕ) (hp : r < 2 * p) :
    Set.InjOn (fun x : (ZMod g)[X] × (ZMod g)[X] => x.1 * x.2)
      ↑(irrDeg g p ×ˢ monicDeg g (r - p)) := by
  rintro ⟨q, h⟩ hx ⟨q', h'⟩ hx' he
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_irrDeg, mem_monicDeg] at hx hx'
  simp only at he
  obtain ⟨⟨⟨hqm, hqd⟩, hqi⟩, hhm, hhd⟩ := hx
  obtain ⟨⟨⟨hqm', hqd'⟩, hqi'⟩, hhm', hhd'⟩ := hx'
  have h1 : q ∣ q' := irr_dvd_of_dvd_mul hqi hhm'.ne_zero (by omega) ⟨h, he.symm⟩
  have hqq : q' = q := eq_of_monic_of_dvd_of_natDegree_le hqm hqm' h1 (by omega)
  subst hqq
  have : h = h' := mul_left_cancel₀ hqm.ne_zero he
  rw [this]

theorem card_bad (r p : ℕ) (hp : r < 2 * p) :
    (bad g r p).card = (irrDeg g p).card * g ^ (r - p) := by
  unfold bad
  rw [Finset.card_image_of_injOn (mul_injOn r p hp), Finset.card_product, card_monicDeg]

theorem mem_bad {r p : ℕ} {f : (ZMod g)[X]} (hf : f ∈ bad g r p) :
    ∃ q h : (ZMod g)[X], f = q * h ∧ q.Monic ∧ q.natDegree = p ∧ Irreducible q ∧
      h.Monic ∧ h.natDegree = r - p := by
  obtain ⟨⟨q, h⟩, hx, rfl⟩ := Finset.mem_image.1 hf
  simp only [Finset.mem_product, mem_irrDeg, mem_monicDeg] at hx
  obtain ⟨⟨⟨hqm, hqd⟩, hqi⟩, hhm, hhd⟩ := hx
  exact ⟨q, h, rfl, hqm, hqd, hqi, hhm, hhd⟩

theorem bad_disj {r p p' : ℕ} (hp : r < 2 * p) (hp' : r < 2 * p') (hne : p ≠ p') :
    Disjoint (bad g r p) (bad g r p') := by
  rw [Finset.disjoint_left]
  intro f hf hf'
  obtain ⟨q, h, rfl, hqm, hqd, hqi, hhm, hhd⟩ := mem_bad hf
  obtain ⟨q', h', he, hqm', hqd', hqi', hhm', hhd'⟩ := mem_bad hf'
  have h1 : q ∣ q' := irr_dvd_of_dvd_mul hqi hhm'.ne_zero (by omega) ⟨h, he.symm⟩
  have h2 : q' ∣ q := irr_dvd_of_dvd_mul hqi' hhm.ne_zero (by omega) ⟨h', he⟩
  have := natDegree_le_of_dvd h1 hqm'.ne_zero
  have := natDegree_le_of_dvd h2 hqm.ne_zero
  omega

theorem T_disj (r p : ℕ) (hp : p ∈ bigPrimes r) (T : Finset (ZMod g)[X])
    (hT : ∀ f ∈ T, Ev g r f) : Disjoint T (bad g r p) := by
  rw [Finset.disjoint_left]
  intro f hfT hfb
  obtain ⟨q, h, rfl, hqm, hqd, hqi, hhm, hhd⟩ := mem_bad hfb
  obtain ⟨hpp, h2p, hp3⟩ := (Finset.mem_filter.1 hp).2
  refine (hT _ hfT).2.2 ⟨q, hqi, dvd_mul_right q h, ?_, ?_, ?_⟩
  · rw [hqd]; exact hpp
  · rw [hqd]; exact h2p
  · rw [hqd]; exact hp3

end

theorem squarefree_count_estimate : CountA := by
  intro g r _ T hT
  classical
  set B := (bigPrimes r).biUnion (fun p => bad g r p) with hB
  have hsub : T ∪ B ⊆ monicDeg g r := by
    intro f hf
    rcases Finset.mem_union.1 hf with hf | hf
    · obtain ⟨⟨hm, hd, -⟩, -, -⟩ := hT f hf
      exact mem_monicDeg.2 ⟨hm, hd⟩
    · obtain ⟨p, hp, hfb⟩ := Finset.mem_biUnion.1 hf
      obtain ⟨q, h, rfl, hqm, hqd, hqi, hhm, hhd⟩ := mem_bad hfb
      obtain ⟨hpp, h2p, hp3⟩ := (Finset.mem_filter.1 hp).2
      refine mem_monicDeg.2 ⟨hqm.mul hhm, ?_⟩
      rw [hqm.natDegree_mul hhm]
      omega
  have hdisj : Disjoint T B := by
    rw [hB, Finset.disjoint_biUnion_right]
    intro p hp
    exact T_disj r p hp T hT
  have hcardB : B.card = ∑ p ∈ bigPrimes r, (irrDeg g p).card * g ^ (r - p) := by
    rw [hB, Finset.card_biUnion]
    · refine Finset.sum_congr rfl (fun p hp => ?_)
      obtain ⟨_, h2p, _⟩ := (Finset.mem_filter.1 hp).2
      exact card_bad r p h2p
    · intro p hp p' hp' hne
      obtain ⟨_, h2p, _⟩ := (Finset.mem_filter.1 hp).2
      obtain ⟨_, h2p', _⟩ := (Finset.mem_filter.1 hp').2
      exact bad_disj h2p h2p' hne
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hcardB, card_monicDeg] at h1
  have h2 : ((T.card + ∑ p ∈ bigPrimes r, (irrDeg g p).card * g ^ (r - p) : ℕ) : ℝ)
      ≤ ((g ^ r : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h2
  linarith

end PI.SqfPrimeFactor.W
