import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush.LowMul

variable {K : Type} [Field K] {n : ℕ}

def Lo (L : Matrix (Fin n) (Fin n) K) : Prop := ∀ i j, i < j → L i j = 0

def AL (E : Fin n → Fin n → Prop) (C : Matrix (Fin n) (Fin n) K) : Prop := ∀ i j, i < j → ¬ E i j → C i j = 0

theorem al_mul {E : Fin n → Fin n → Prop} (hE : ∀ i j k, E k j → k ≤ i → i < j → E i j)
    {L C : Matrix (Fin n) (Fin n) K} (hL : Lo L) (hC : AL E C) : AL E (L * C) := by
  intro i j hij hn
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge i k with h | h
  · rw [hL i k h, zero_mul]
  · rw [hC k j (lt_of_le_of_lt h hij) (fun he => hn (hE i j k he h hij)), mul_zero]

theorem mul_al {E : Fin n → Fin n → Prop} (hE : ∀ i j l, E i l → j ≤ l → i < j → E i j)
    {C R : Matrix (Fin n) (Fin n) K} (hC : AL E C) (hR : Lo R) : AL E (C * R) := by
  intro i j hij hn
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge l j with h | h
  · rw [hR l j h, mul_zero]
  · rw [hC i l (lt_of_lt_of_le hij h) (fun he => hn (hE i j l he h hij)), zero_mul]

theorem diag_mul {E : Fin n → Fin n → Prop} {L C : Matrix (Fin n) (Fin n) K} (hL : Lo L) (hC : AL E C)
    (x : Fin n) (hx : ∀ k, k < x → ¬ E k x) : (L * C) x x = L x x * C x x := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single x fun k hk => ?_
  rcases lt_or_gt_of_ne hk with h | h
  · rw [hC k x h (hx k h), mul_zero]
  · rw [hL x k h, zero_mul]

theorem mul_diag {E : Fin n → Fin n → Prop} {C R : Matrix (Fin n) (Fin n) K} (hC : AL E C) (hR : Lo R)
    (x : Fin n) (hx : ∀ l, x < l → ¬ E x l) : (C * R) x x = C x x * R x x := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single x fun l hl => ?_
  rcases lt_or_gt_of_ne hl with h | h
  · rw [hR l x h, mul_zero]
  · rw [hC x l h (hx l h), zero_mul]

theorem lo_diag_ne {M : Matrix (Fin n) (Fin n) K} (hM : Lo M) (hd : M.det ≠ 0) (i : Fin n) : M i i ≠ 0 := by
  rw [Matrix.det_of_lowerTriangular M (fun i j h => hM i j (OrderDual.toDual_lt_toDual.1 h))] at hd
  exact Finset.prod_ne_zero_iff.1 hd i (Finset.mem_univ _)

section Pair
variable {a b : Fin n} {L C R : Matrix (Fin n) (Fin n) K}

theorem lower_index_pair_unique (hab : (b : ℕ) = a + 1) : ∀ i j k : Fin n, (k = a ∧ j = b) → k ≤ i → i < j → (i = a ∧ j = b) := by
  rintro i j k ⟨rfl, rfl⟩ h1 h2
  refine ⟨Fin.ext ?_, rfl⟩
  rw [Fin.le_iff_val_le_val] at h1; rw [Fin.lt_iff_val_lt_val] at h2; omega

theorem l_aa (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) a a = L a a * C a a :=
  diag_mul hL hC a fun _ _ e => absurd (congrArg Fin.val e.2) (by omega)

theorem l_ab (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) a b = L a a * C a b := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single a fun k hk => ?_
  have hk' : (k : ℕ) ≠ a := fun h => hk (Fin.ext h)
  rcases lt_or_gt_of_ne hk' with h | h
  · rw [hC k b (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hk e.1), mul_zero]
  · rw [hL a k (Fin.lt_iff_val_lt_val.2 h), zero_mul]

theorem l_ba (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) b a = L b a * C a a + L b b * C b a := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun k ⟨hka, hkb⟩ => ?_
  have hka' : (k : ℕ) ≠ a := fun h => hka (Fin.ext h)
  have hkb' : (k : ℕ) ≠ b := fun h => hkb (Fin.ext h)
  rcases lt_or_gt_of_ne hkb' with h | h
  · rw [hC k a (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hka e.1), mul_zero]
  · rw [hL b k (Fin.lt_iff_val_lt_val.2 h), zero_mul]

theorem l_bb (hab : (b : ℕ) = a + 1) (hL : Lo L) (hC : AL (fun i j => i = a ∧ j = b) C) :
    (L * C) b b = L b a * C a b + L b b * C b b := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun k ⟨hka, hkb⟩ => ?_
  have hka' : (k : ℕ) ≠ a := fun h => hka (Fin.ext h)
  have hkb' : (k : ℕ) ≠ b := fun h => hkb (Fin.ext h)
  rcases lt_or_gt_of_ne hkb' with h | h
  · rw [hC k b h (fun e => hka e.1), mul_zero]
  · rw [hL b k (Fin.lt_iff_val_lt_val.2 h), zero_mul]

theorem r_aa (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) a a = C a a * R a a + C a b * R b a := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun l ⟨hla, hlb⟩ => ?_
  have hla' : (l : ℕ) ≠ a := fun h => hla (Fin.ext h)
  have hlb' : (l : ℕ) ≠ b := fun h => hlb (Fin.ext h)
  rcases lt_or_gt_of_ne hla' with h | h
  · rw [hR l a (Fin.lt_iff_val_lt_val.2 h), mul_zero]
  · rw [hC a l (Fin.lt_iff_val_lt_val.2 h) (fun e => hlb e.2), zero_mul]

theorem r_ab (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) a b = C a b * R b b := by
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_single b fun l hl => ?_
  have hl' : (l : ℕ) ≠ b := fun h => hl (Fin.ext h)
  rcases lt_or_gt_of_ne hl' with h | h
  · rw [hR l b (Fin.lt_iff_val_lt_val.2 h), mul_zero]
  · rw [hC a l (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hl e.2), zero_mul]

theorem r_ba (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) b a = C b a * R a a + C b b * R b a := by
  have hne : a ≠ b := fun h => absurd (congrArg Fin.val h) (by omega)
  rw [Matrix.mul_apply]
  refine Fintype.sum_eq_add a b hne fun l ⟨hla, hlb⟩ => ?_
  have hla' : (l : ℕ) ≠ a := fun h => hla (Fin.ext h)
  have hlb' : (l : ℕ) ≠ b := fun h => hlb (Fin.ext h)
  rcases lt_or_gt_of_ne hla' with h | h
  · rw [hR l a (Fin.lt_iff_val_lt_val.2 h), mul_zero]
  · rw [hC b l (Fin.lt_iff_val_lt_val.2 (by omega)) (fun e => hne e.1.symm), zero_mul]

theorem r_bb (hab : (b : ℕ) = a + 1) (hC : AL (fun i j => i = a ∧ j = b) C) (hR : Lo R) :
    (C * R) b b = C b b * R b b :=
  mul_diag hC hR b fun _ _ e => absurd (congrArg Fin.val e.1) (by omega)

end Pair

section Root
variable {ι : Type} {m : ι → ℕ} {τ : ι} {a b : Fin (m τ)}

theorem root_lower_pair_unique_left (hab : (b : ℕ) = a + 1) (σ : ι) : ∀ i j k : Fin (m σ),
    ((⟨σ, k⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) → k ≤ i → i < j →
      ((⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) := by
  rintro i j k ⟨h1, h2⟩ hki hij
  obtain ⟨rfl, hk⟩ := Sigma.mk.inj_iff.1 h1
  obtain rfl := eq_of_heq hk
  obtain rfl := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
  refine ⟨congrArg (Sigma.mk _) (Fin.ext ?_), rfl⟩
  rw [Fin.le_iff_val_le_val] at hki; rw [Fin.lt_iff_val_lt_val] at hij; omega

theorem root_lower_pair_unique_right (hab : (b : ℕ) = a + 1) (σ : ι) : ∀ i j l : Fin (m σ),
    ((⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, l⟩ : Root m) = ⟨τ, b⟩) → j ≤ l → i < j →
      ((⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) := by
  rintro i j l ⟨h1, h2⟩ hjl hij
  obtain ⟨rfl, hk⟩ := Sigma.mk.inj_iff.1 h1
  obtain rfl := eq_of_heq hk
  obtain rfl := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
  refine ⟨rfl, congrArg (Sigma.mk _) (Fin.ext ?_)⟩
  rw [Fin.le_iff_val_le_val] at hjl; rw [Fin.lt_iff_val_lt_val] at hij; omega

end Root

end GlobalTheory.FlagPush.LowMul

namespace GlobalTheory.FlagPush

open LowMul in

theorem almostLow_mul_entries : ∀ (ι : Type) (m : ι → ℕ) (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ (K : Type) [Field K] (S T C : Mat m K), Par m ⊤ S → Par m ⊤ T → AlmostLow τ a b C → AlmostLow τ a b (S * C * T) ∧ (∀ x : Root m, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → (S * C * T) x.1 x.2 x.2 = S x.1 x.2 x.2 * C x.1 x.2 x.2 * T x.1 x.2 x.2) ∧ (S * C * T) τ a b = S τ a a * C τ a b * T τ b b ∧ minor τ a b (S * C * T) = S τ a a * S τ b b * minor τ a b C * (T τ a a * T τ b b) := by
  intro ι m τ a b hab K _ S T C hS hT hC
  have hSl : ∀ σ, Lo (S σ) := fun σ i j h => (hS σ).2.2.2 i j i.isLt h
  have hTl : ∀ σ, Lo (T σ) := fun σ i j h => (hT σ).2.2.2 i j i.isLt h
  have hCr : ∀ σ, AL (fun i j => (⟨σ, i⟩ : Root m) = ⟨τ, a⟩ ∧ (⟨σ, j⟩ : Root m) = ⟨τ, b⟩) (C σ) :=
    fun σ => hC.2.2 σ
  have hCt : AL (fun i j => i = a ∧ j = b) (C τ) := fun i j h hn =>
    hC.2.2 τ i j h fun e => hn ⟨eq_of_heq (Sigma.mk.inj_iff.1 e.1).2, eq_of_heq (Sigma.mk.inj_iff.1 e.2).2⟩
  have hP : AL (fun i j => i = a ∧ j = b) (S τ * C τ) := al_mul (lower_index_pair_unique hab) (hSl τ) hCt
  have h3 : (S * C * T) τ a b = S τ a a * C τ a b * T τ b b := by
    show (S τ * C τ * T τ) a b = _
    rw [r_ab hab hP (hTl τ), l_ab hab (hSl τ) hCt]
  refine ⟨⟨fun σ => ?_, ?_, fun σ => ?_⟩, fun x hxa hxb => ?_, h3, ?_⟩
  · show (S σ * C σ * T σ).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero (hS.det_ne σ) (hC.1 σ)) (hT.det_ne σ)
  · rw [h3]
    exact mul_ne_zero (mul_ne_zero (lo_diag_ne (hSl τ) (hS.det_ne τ) a) hC.2.1) (lo_diag_ne (hTl τ) (hT.det_ne τ) b)
  · exact mul_al (root_lower_pair_unique_right hab σ) (al_mul (root_lower_pair_unique_left hab σ) (hSl σ) (hCr σ)) (hTl σ)
  · show (S x.1 * C x.1 * T x.1) x.2 x.2 = _
    rw [mul_diag (al_mul (root_lower_pair_unique_left hab x.1) (hSl x.1) (hCr x.1)) (hTl x.1) x.2 (fun _ _ e => hxa e.1),
      diag_mul (hSl x.1) (hCr x.1) x.2 (fun _ _ e => hxb e.2)]
  · show (S τ * C τ * T τ) a a * (S τ * C τ * T τ) b b - (S τ * C τ * T τ) a b * (S τ * C τ * T τ) b a =
      S τ a a * S τ b b * (C τ a a * C τ b b - C τ a b * C τ b a) * (T τ a a * T τ b b)
    rw [r_aa hab hP (hTl τ), r_bb hab hP (hTl τ), r_ab hab hP (hTl τ), r_ba hab hP (hTl τ),
      l_aa hab (hSl τ) hCt, l_bb hab (hSl τ) hCt, l_ab hab (hSl τ) hCt, l_ba hab (hSl τ) hCt]
    ring

end GlobalTheory.FlagPush
