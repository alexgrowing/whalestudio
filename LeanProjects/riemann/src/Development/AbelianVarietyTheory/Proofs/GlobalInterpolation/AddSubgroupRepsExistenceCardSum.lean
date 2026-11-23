import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.RepsMod

variable {H : Type} [AddCommGroup H]

theorem sum_eq_of_family {M ι : Type} [AddCommMonoid M] {Λ B : AddSubgroup H} {R : Finset H}
    (hR : IsReps Λ B R) (s : Finset ι) (f : ι → H) (hf : ∀ i ∈ s, f i ∈ B)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, f i - f j ∈ Λ → i = j) (hsurj : ∀ y ∈ B, ∃ i ∈ s, y - f i ∈ Λ)
    (F : H → M) (hF : ∀ y ∈ B, ∀ l ∈ Λ, l ∈ B → F (y + l) = F y) :
    ∑ y ∈ R, F y = ∑ i ∈ s, F (f i) := by
  obtain ⟨h1, h2, h3⟩ := hR
  symm
  choose r hr hrl using fun i (hi : i ∈ s) => h3 (f i) (hf i hi)
  refine Finset.sum_bij r hr ?_ ?_ ?_
  · intro i hi j hj hij
    apply hinj i hi j hj
    have := Λ.sub_mem (hrl i hi) (hrl j hj)
    rw [hij] at this
    simpa using this
  · intro y hy
    obtain ⟨i, hi, hl⟩ := hsurj y (h1 y hy)
    refine ⟨i, hi, ?_⟩
    symm
    apply h2 y hy _ (hr i hi)
    have := Λ.add_mem hl (hrl i hi)
    simpa using this
  · intro i hi
    have := hF (r i hi) (h1 _ (hr i hi)) _ (hrl i hi) (B.sub_mem (hf i hi) (h1 _ (hr i hi)))
    simpa using this

theorem out_sub_mem_iff (Λ B : AddSubgroup H) (x y : B) :
    ((x : H) - y ∈ Λ) ↔ (QuotientAddGroup.mk x : B ⧸ Λ.addSubgroupOf B) = QuotientAddGroup.mk y := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
  simp

theorem out_inj (Λ B : AddSubgroup H) (c d : B ⧸ Λ.addSubgroupOf B)
    (h : ((c.out : B) : H) - (d.out : B) ∈ Λ) : c = d := by
  rw [out_sub_mem_iff] at h
  simpa using h

theorem out_surj (Λ B : AddSubgroup H) (y : H) (hy : y ∈ B) :
    ∃ c : B ⧸ Λ.addSubgroupOf B, y - ((c.out : B) : H) ∈ Λ := by
  refine ⟨QuotientAddGroup.mk ⟨y, hy⟩, ?_⟩
  have := (out_sub_mem_iff Λ B ⟨y, hy⟩ (Quotient.out (QuotientAddGroup.mk ⟨y, hy⟩ : B ⧸ Λ.addSubgroupOf B))).2 (by simp)
  exact this

theorem exists_reps (Λ B : AddSubgroup H) (h : Λ.relIndex B ≠ 0) : ∃ R : Finset H, IsReps Λ B R := by
  classical
  have : Finite (B ⧸ Λ.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
  have := Fintype.ofFinite (B ⧸ Λ.addSubgroupOf B)
  refine ⟨Finset.univ.image (fun c : B ⧸ Λ.addSubgroupOf B => ((c.out : B) : H)), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    exact (c.out).2
  · intro x hx y hy hxy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 hy
    rw [out_inj Λ B c d hxy]
  · intro y hy
    obtain ⟨c, hc⟩ := out_surj Λ B y hy
    exact ⟨_, Finset.mem_image.2 ⟨c, Finset.mem_univ _, rfl⟩, hc⟩

theorem card_reps (Λ B : AddSubgroup H) (R : Finset H) (hR : IsReps Λ B R) :
    R.card = Λ.relIndex B := by
  classical
  have : Finite (B ⧸ Λ.addSubgroupOf B) := by
    refine Finite.of_surjective (fun x : R => (QuotientAddGroup.mk ⟨x.1, hR.1 _ x.2⟩ : B ⧸ Λ.addSubgroupOf B)) ?_
    intro c
    obtain ⟨x, hx, hl⟩ := hR.2.2 _ (c.out).2
    refine ⟨⟨x, hx⟩, ?_⟩
    have := (out_sub_mem_iff Λ B c.out ⟨x, hR.1 _ hx⟩).1 hl
    simpa using this.symm
  have := Fintype.ofFinite (B ⧸ Λ.addSubgroupOf B)
  have h := sum_eq_of_family hR Finset.univ (fun c : B ⧸ Λ.addSubgroupOf B => ((c.out : B) : H))
    (fun c _ => (c.out).2) (fun c _ d _ h => out_inj Λ B c d h)
    (fun y hy => by
      obtain ⟨c, hc⟩ := out_surj Λ B y hy
      exact ⟨c, Finset.mem_univ _, hc⟩) (fun _ => (1 : ℕ)) (fun _ _ _ _ _ => rfl)
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] at h
  rw [h, ← Nat.card_eq_fintype_card]
  rfl

theorem sum_prod_reps (M : Type) [AddCommMonoid M] (Λ B B₁ B₂ : AddSubgroup H) (R R₁ R₂ : Finset H)
    (F : H → M) (h1 : B₁ ≤ B) (h2 : B₂ ≤ B) (hs : ∀ y ∈ B, ∃ y₁ ∈ B₁, ∃ y₂ ∈ B₂, y - (y₁ + y₂) ∈ Λ)
    (hi : ∀ y₁ ∈ B₁, ∀ y₂ ∈ B₂, y₁ + y₂ ∈ Λ → y₁ ∈ Λ) (hR : IsReps Λ B R) (hR₁ : IsReps Λ B₁ R₁)
    (hR₂ : IsReps Λ B₂ R₂) (hF : ∀ y ∈ B, ∀ l ∈ Λ, l ∈ B → F (y + l) = F y) :
    ∑ y ∈ R, F y = ∑ y₂ ∈ R₂, ∑ y₁ ∈ R₁, F (y₁ + y₂) := by
  rw [← Finset.sum_product']
  refine sum_eq_of_family hR (R₂ ×ˢ R₁) (fun p => p.2 + p.1) ?_ ?_ ?_ F hF
  · intro p hp
    rw [Finset.mem_product] at hp
    exact B.add_mem (h1 (hR₁.1 _ hp.2)) (h2 (hR₂.1 _ hp.1))
  · intro p hp q hq hpq
    rw [Finset.mem_product] at hp hq
    have e : p.2 + p.1 - (q.2 + q.1) = (p.2 - q.2) + (p.1 - q.1) := by abel
    simp only [e] at hpq
    have a1 := hi _ (B₁.sub_mem (hR₁.1 _ hp.2) (hR₁.1 _ hq.2)) _
      (B₂.sub_mem (hR₂.1 _ hp.1) (hR₂.1 _ hq.1)) hpq
    have a2 : p.1 - q.1 ∈ Λ := by
      have := Λ.sub_mem hpq a1
      simpa using this
    exact Prod.ext (hR₂.2.1 _ hp.1 _ hq.1 a2) (hR₁.2.1 _ hp.2 _ hq.2 a1)
  · intro y hy
    obtain ⟨y₁, hy₁, y₂, hy₂, hl⟩ := hs y hy
    obtain ⟨r₁, hr₁, hl₁⟩ := hR₁.2.2 _ hy₁
    obtain ⟨r₂, hr₂, hl₂⟩ := hR₂.2.2 _ hy₂
    refine ⟨(r₂, r₁), Finset.mem_product.2 ⟨hr₂, hr₁⟩, ?_⟩
    have e : y - (r₁ + r₂) = (y - (y₁ + y₂)) + (y₁ - r₁) + (y₂ - r₂) := by abel
    simp only [e]
    exact Λ.add_mem (Λ.add_mem hl hl₁) hl₂

theorem sum_char_reps (K : Type) [Field K] (Λ B : AddSubgroup H) (R : Finset H) (φ : H → K)
    (hR : IsReps Λ B R) (hm : ∀ x ∈ B, ∀ y ∈ B, φ (x + y) = φ x * φ y)
    (h1 : ∀ x ∈ B, x ∈ Λ → φ x = 1) :
    ((∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = (R.card : K)) ∧
      ((¬ ∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = 0) := by
  constructor
  · intro h
    rw [Finset.sum_congr rfl (fun y hy => h y (hR.1 y hy))]
    simp
  · intro h
    push Not at h
    obtain ⟨y₀, hy₀, hne⟩ := h
    have key := sum_eq_of_family hR R (fun y => y₀ + y) (fun y hy => B.add_mem hy₀ (hR.1 y hy))
      (fun x hx y hy hxy => hR.2.1 x hx y hy (by simpa using hxy))
      (fun y hy => by
        obtain ⟨x, hx, hl⟩ := hR.2.2 _ (B.sub_mem hy hy₀)
        exact ⟨x, hx, by rwa [← sub_sub]⟩) φ
      (fun y hy l hl hlB => by rw [hm y hy l hlB, h1 l hlB hl, mul_one])
    rw [Finset.sum_congr rfl (fun y hy => hm y₀ hy₀ y (hR.1 y hy)), ← Finset.mul_sum] at key
    have : (φ y₀ - 1) * ∑ y ∈ R, φ y = 0 := by rw [_root_.sub_mul, one_mul, ← key, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)

theorem not_dvd_relIndex (Λ B : AddSubgroup H) (g p : ℕ) (hp : p.Prime) (hc : Nat.Coprime g p)
    (h : Λ.relIndex B ≠ 0) (hg : ∀ x ∈ B, g • x ∈ Λ) : ¬ p ∣ Λ.relIndex B := by
  intro hd
  have : Finite (B ⧸ Λ.addSubgroupOf B) := Nat.finite_of_card_ne_zero h
  have := Fact.mk hp
  obtain ⟨c, hcc⟩ := exists_prime_addOrderOf_dvd_card' (G := B ⧸ Λ.addSubgroupOf B) p hd
  have h0 : g • c = 0 := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective c
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa using hg x x.2
  have hdg : p ∣ g := hcc ▸ addOrderOf_dvd_of_nsmul_eq_zero h0
  exact (hp.coprime_iff_not_dvd.1 hc.symm) hdg

theorem reps_facts : ∀ (H : Type) [AddCommGroup H], (∀ Λ B : AddSubgroup H, Λ.relIndex B ≠ 0 → ∃ R : Finset H, IsReps Λ B R) ∧ (∀ (Λ B : AddSubgroup H) (R : Finset H), IsReps Λ B R → R.card = Λ.relIndex B) ∧ (∀ (M : Type) [AddCommMonoid M] (Λ B B₁ B₂ : AddSubgroup H) (R R₁ R₂ : Finset H) (F : H → M), B₁ ≤ B → B₂ ≤ B → (∀ y ∈ B, ∃ y₁ ∈ B₁, ∃ y₂ ∈ B₂, y - (y₁ + y₂) ∈ Λ) → (∀ y₁ ∈ B₁, ∀ y₂ ∈ B₂, y₁ + y₂ ∈ Λ → y₁ ∈ Λ) → IsReps Λ B R → IsReps Λ B₁ R₁ → IsReps Λ B₂ R₂ → (∀ y ∈ B, ∀ l ∈ Λ, l ∈ B → F (y + l) = F y) → ∑ y ∈ R, F y = ∑ y₂ ∈ R₂, ∑ y₁ ∈ R₁, F (y₁ + y₂)) ∧ (∀ (K : Type) [Field K] (Λ B : AddSubgroup H) (R : Finset H) (φ : H → K), IsReps Λ B R → (∀ x ∈ B, ∀ y ∈ B, φ (x + y) = φ x * φ y) → (∀ x ∈ B, x ∈ Λ → φ x = 1) → ((∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = (R.card : K)) ∧ ((¬ ∀ y ∈ B, φ y = 1) → ∑ y ∈ R, φ y = 0)) ∧ ∀ (Λ B : AddSubgroup H) (g p : ℕ), p.Prime → Nat.Coprime g p → Λ.relIndex B ≠ 0 → (∀ x ∈ B, g • x ∈ Λ) → ¬ p ∣ Λ.relIndex B :=
  fun _ _ => ⟨exists_reps, card_reps, sum_prod_reps, sum_char_reps, not_dvd_relIndex⟩

end GlobalTheory.RepsMod
