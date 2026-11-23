import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.PrAcyc

def cone {p N : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) :
    SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N :=
  SimplexCategory.mkHom ⟨(Fin.cons (0 : Fin (N + 1)) fun k : Fin (p + 1) => a.toOrderHom k : Fin (p + 2) → Fin (N + 1)),
    by
      intro x y hxy
      induction x using Fin.cases with
      | zero => exact Fin.zero_le _
      | succ x =>
        induction y using Fin.cases with
        | zero => exact absurd hxy (by simp [Fin.le_def])
        | succ y =>
          simp only [Fin.cons_succ]
          exact a.toOrderHom.monotone (Fin.succ_le_succ_iff.1 hxy)⟩

theorem cone_succ {p N : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (k : Fin (p + 1)) :
    (cone a).toOrderHom k.succ = a.toOrderHom k := rfl

theorem δ_zero_cone {p N : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) :
    SimplexCategory.δ 0 ≫ cone a = a := by
  ext k
  simp [SimplexCategory.δ, cone_succ]

theorem δ_succ_cone {p N : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (i : Fin (p + 2)) :
    SimplexCategory.δ i.succ ≫ cone a = cone (SimplexCategory.δ i ≫ a) := by
  refine SimplexCategory.Hom.ext _ _ (OrderHom.ext _ _ (funext fun k => ?_))
  induction k using Fin.cases with
  | zero => rfl
  | succ k =>
    show (cone a).toOrderHom (i.succ.succAbove k.succ) = (cone (SimplexCategory.δ i ≫ a)).toOrderHom k.succ
    rw [Fin.succ_succAbove_succ, cone_succ, cone_succ]
    rfl

abbrev v0 (N : ℕ) : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N := SimplexCategory.const _ _ 0

theorem δ_one_cone {N : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) :
    SimplexCategory.δ 1 ≫ cone a = v0 N := by
  ext k
  fin_cases k
  rfl

theorem d₁_zero {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨0, r, a, b⟩ : Pr N) = 0 := rfl

theorem d₂_zero {N p : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, 0, a, b⟩ : Pr N) = 0 := rfl

theorem d₁_succ {N p r : ℕ} (a : SimplexCategory.mk (p + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨p + 1, r, a, b⟩ : Pr N) =
      ∑ i : Fin (p + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (⟨p, r, SimplexCategory.δ i ≫ a, b⟩ : Pr N) 1 := by
  show ∑ i : Fin (p + 2), Finsupp.single _ _ = _
  simp only [Finsupp.smul_single_one]

theorem d₂_succ {N p r : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk (r + 1) ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, r + 1, a, b⟩ : Pr N) =
      ∑ j : Fin (r + 2), ((-1 : ℤ) ^ (j : ℕ)) • Finsupp.single (⟨p, r, a, SimplexCategory.δ j ≫ b⟩ : Pr N) 1 := by
  show ∑ j : Fin (r + 2), Finsupp.single _ _ = _
  simp only [Finsupp.smul_single_one]

end GlobalTheory.PrAcyc

namespace GlobalTheory.PrAcyc

theorem d₁_cone_succ {N q r : ℕ} (a : SimplexCategory.mk (q + 1) ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨q + 1 + 1, r, cone a, b⟩ : Pr N) = Finsupp.single (⟨q + 1, r, a, b⟩ : Pr N) 1 -
      ∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (⟨q + 1, r, cone (SimplexCategory.δ i ≫ a), b⟩ : Pr N) 1 := by
  rw [d₁_succ, Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · rw [δ_zero_cone, Fin.val_zero, pow_zero, one_smul]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, δ_succ_cone]

theorem d₁_cone_zero {N r : ℕ} (a : SimplexCategory.mk 0 ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk r ⟶ SimplexCategory.mk N) :
    Pr.d₁ (⟨0 + 1, r, cone a, b⟩ : Pr N) = Finsupp.single (⟨0, r, a, b⟩ : Pr N) 1 - Finsupp.single (⟨0, r, v0 N, b⟩ : Pr N) 1 := by
  rw [d₁_succ, Fin.sum_univ_two, δ_zero_cone, δ_one_cone]
  simp [sub_eq_add_neg]

theorem d₂_cone_succ {N p s : ℕ} (a : SimplexCategory.mk p ⟶ SimplexCategory.mk N) (b : SimplexCategory.mk (s + 1) ⟶ SimplexCategory.mk N) :
    Pr.d₂ (⟨p, s + 1 + 1, a, cone b⟩ : Pr N) = Finsupp.single (⟨p, s + 1, a, b⟩ : Pr N) 1 -
      ∑ j : Fin (s + 2), ((-1 : ℤ) ^ (j : ℕ)) • Finsupp.single (⟨p, s + 1, a, cone (SimplexCategory.δ j ≫ b)⟩ : Pr N) 1 := by
  rw [d₂_succ, Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · rw [δ_zero_cone, Fin.val_zero, pow_zero, one_smul]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul, δ_succ_cone]

def hz {N : ℕ} (z : Pr N) : Pr N →₀ ℤ :=
  Finsupp.single (⟨z.1 + 1, z.2.1, cone z.2.2.1, z.2.2.2⟩ : Pr N) 1 +
    if z.1 = 0 then Finsupp.single (⟨0, z.2.1 + 1, v0 N, cone z.2.2.2⟩ : Pr N) 1 else 0

def H (N : ℕ) : (Pr N →₀ ℤ) →ₗ[ℤ] (Pr N →₀ ℤ) := Finsupp.linearCombination ℤ hz

theorem H_single {N : ℕ} (z : Pr N) : H N (Finsupp.single z 1) = hz z := by
  simp [H, Finsupp.linearCombination_single]

theorem d_single {N : ℕ} (z : Pr N) : Pr.d N (Finsupp.single z 1) = z.d₁ + (-1 : ℤ) ^ z.1 • z.d₂ := by
  simp [Pr.d, Finsupp.linearCombination_single]

theorem H_sum {N n : ℕ} (f : Fin n → Pr N) :
    H N (∑ i : Fin n, ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (f i) 1) = ∑ i : Fin n, ((-1 : ℤ) ^ (i : ℕ)) • hz (f i) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_smul, H_single]

theorem key {N : ℕ} (z : Pr N) (hpos : 0 < z.1 + z.2.1) :
    Pr.d N (H N (Finsupp.single z 1)) + H N (Pr.d N (Finsupp.single z 1)) = Finsupp.single z 1 := by
  rcases z with ⟨p, r, a, b⟩
  rw [H_single, d_single]
  cases p with
  | zero =>
    cases r with
    | zero => simp at hpos
    | succ s =>
      simp only [hz, if_pos rfl, if_true, map_add, d_single]
      rw [d₁_cone_zero, d₂_succ, d₁_zero, d₂_cone_succ, d₁_zero, d₂_succ, map_zero, map_smul, H_sum]
      simp only [hz, if_true, ↓reduceIte, Finset.sum_add_distrib, smul_add]
      module
  | succ q =>
    simp only [hz, Nat.succ_ne_zero, if_false, ↓reduceIte, add_zero, map_add, d_single, map_smul]
    rw [d₁_cone_succ, d₁_succ, H_sum]
    have hX : ∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • hz (⟨q, r, SimplexCategory.δ i ≫ a, b⟩ : Pr N) =
        ∑ i : Fin (q + 2), ((-1 : ℤ) ^ (i : ℕ)) • Finsupp.single (⟨q + 1, r, cone (SimplexCategory.δ i ≫ a), b⟩ : Pr N) 1 := by
      simp only [hz, smul_add, Finset.sum_add_distrib]
      rcases q with _ | t
      · simp [Fin.sum_univ_two]
      · simp
    rw [hX]
    cases r with
    | zero => rw [d₂_zero, d₂_zero, map_zero]; module
    | succ s =>
      rw [d₂_succ, d₂_succ, H_sum]
      simp only [hz, Nat.succ_ne_zero, if_false, ↓reduceIte, add_zero]
      rw [pow_succ]
      module

end GlobalTheory.PrAcyc

namespace GlobalTheory.PrAcyc

theorem hz_deg {N : ℕ} (w z : Pr N) (h : z ∈ (hz w).support) : z.1 + z.2.1 = w.1 + w.2.1 + 1 := by
  rcases w with ⟨p, r, a, b⟩
  have h' := Finsupp.support_add h
  rcases Finset.mem_union.1 h' with h1 | h1
  · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at h1
    split_ifs at h1 with he
    · subst he; simp; omega
    · simp at h1
  · split_ifs at h1 with hp
    · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at h1
      split_ifs at h1 with he
      · subst he; simp at hp ⊢; omega
      · simp at h1
    · simp at h1

theorem deg_H {N k : ℕ} (c : Pr N →₀ ℤ) (hc : Pr.Deg (k + 1) c) : Pr.Deg (k + 2) (H N c) := by
  intro z hz'
  rw [H, Finsupp.linearCombination_apply] at hz'
  obtain ⟨w, hw, hzw⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hz')
  have := hz_deg w z (Finsupp.support_smul hzw)
  rw [this, hc w hw]

theorem homotopy {N k : ℕ} (c : Pr N →₀ ℤ) (hc : Pr.Deg (k + 1) c) :
    Pr.d N (H N c) + H N (Pr.d N c) = c := by
  have step : ∀ z ∈ c.support, Pr.d N (H N (Finsupp.single z (c z))) + H N (Pr.d N (Finsupp.single z (c z))) =
      Finsupp.single z (c z) := by
    intro z hz'
    have := key z (by rw [hc z hz']; omega)
    rw [← Finsupp.smul_single_one, map_smul, map_smul, map_smul, map_smul, ← smul_add, this]
  calc Pr.d N (H N c) + H N (Pr.d N c)
      = Pr.d N (H N (c.sum Finsupp.single)) + H N (Pr.d N (c.sum Finsupp.single)) := by rw [Finsupp.sum_single]
    _ = ∑ z ∈ c.support, Finsupp.single z (c z) := by
        simp only [Finsupp.sum, map_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl step
    _ = c := Finsupp.sum_single c

theorem pr_acyclic : ∀ N k (c : Pr N →₀ ℤ), Pr.Deg (k + 1) c → Pr.d N c = 0 → ∃ e, Pr.Deg (k + 2) e ∧ Pr.d N e = c := by
  intro N k c hc hd
  refine ⟨H N c, deg_H c hc, ?_⟩
  have := homotopy c hc
  rwa [hd, map_zero, add_zero] at this

end GlobalTheory.PrAcyc
