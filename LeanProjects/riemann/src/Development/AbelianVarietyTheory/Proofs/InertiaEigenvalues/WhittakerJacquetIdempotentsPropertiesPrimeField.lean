import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace CompanionTheory.Member.UnipotentColumnData

variable {g : ℕ} [Fact g.Prime]

theorem entN_mul {N : ℕ} (M M' : Mt g N) (hM : IsUniUp M) (hM' : IsUniUp M') (i j : ℕ) (hij : i < j)
    (h : ∀ b, i < b → b < j → entN M' b j = 0) :
    entN (M * M') i j = entN M i j + entN M' i j := by
  by_cases hj : j < N
  · have hi : i < N := lt_trans hij hj
    simp only [entN, hi, hj, and_self, ↓reduceDIte]
    rw [Matrix.mul_apply, Finset.sum_eq_add (⟨i, hi⟩ : Fin N) ⟨j, hj⟩]
    · rw [(hM ⟨i, hi⟩ ⟨i, hi⟩).2 rfl, (hM' ⟨j, hj⟩ ⟨j, hj⟩).2 rfl, one_mul, mul_one, add_comm]
    · intro e
      rw [Fin.mk.injEq] at e
      omega
    · intro b _ hb
      obtain ⟨hbi, hbj⟩ := hb
      rcases lt_trichotomy b ⟨i, hi⟩ with h1 | h1 | h1
      · rw [(hM _ _).1 h1, zero_mul]
      · exact absurd h1 hbi
      · rcases lt_trichotomy b ⟨j, hj⟩ with h2 | h2 | h2
        · have hz := h b.val (Fin.lt_def.mp h1) (Fin.lt_def.mp h2)
          simp only [entN, b.isLt, hj, and_self, ↓reduceDIte, Fin.eta] at hz
          rw [hz, mul_zero]
        · exact absurd h2 hbj
        · rw [(hM' _ _).1 h2, mul_zero]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · simp [entN, hj]

theorem uni_mul {N : ℕ} (M M' : Mt g N) (hM : IsUniUp M) (hM' : IsUniUp M') : IsUniUp (M * M') := by
  intro a b
  constructor
  · intro hba
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with hc | hc
    · rw [(hM a c).1 hc, zero_mul]
    · rw [(hM' c b).1 (lt_of_lt_of_le hba hc), mul_zero]
  · intro hab
    subst hab
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [(hM a a).2 rfl, (hM' a a).2 rfl, one_mul]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with hc | hc
      · rw [(hM a c).1 hc, zero_mul]
      · rw [(hM' c a).1 hc, mul_zero]
    · intro hn
      exact absurd (Finset.mem_univ a) hn

theorem uni_one {N : ℕ} : IsUniUp (1 : Mt g N) := by
  intro a b
  refine ⟨fun h => Matrix.one_apply_ne (ne_of_gt h), fun h => ?_⟩
  subst h
  exact Matrix.one_apply_eq a

theorem entN_one {N : ℕ} (i j : ℕ) (h : i < j) : entN (1 : Mt g N) i j = 0 := by
  unfold entN
  split_ifs with hN
  · refine Matrix.one_apply_ne ?_
    intro e
    rw [Fin.mk.injEq] at e
    omega
  · rfl

private theorem eDat_eq_inv_card_smul_sum_single {N : ℕ} (P : Mt g N → Prop) (φ : Mt g N → ZMod g)
    (ψ : AddChar (ZMod g) ℂ) :
    eDat g N P φ ψ = (((Finset.univ.filter fun u : Gn g N => P (u : Mt g N)).card : ℂ))⁻¹ •
      ∑ u ∈ Finset.univ.filter (fun u : Gn g N => P (u : Mt g N)),
        MonoidAlgebra.single u (ψ (φ (u : Mt g N)))⁻¹ := by
  unfold eDat
  rfl

theorem eDat_idem {N : ℕ} (P : Mt g N → Prop) (φ : Mt g N → ZMod g) (ψ : AddChar (ZMod g) ℂ)
    (h1 : P 1) (hmul : ∀ M M', P M → P M' → P (M * M'))
    (hφ : ∀ M M', P M → P M' → φ (M * M') = φ M + φ M') :
    eDat g N P φ ψ * eDat g N P φ ψ = eDat g N P φ ψ ∧
      (eDat g N P φ ψ).coeff 1 =
        ((Finset.univ.filter fun u : Gn g N => P (u : Mt g N)).card : ℂ)⁻¹ := by
  rw [eDat_eq_inv_card_smul_sum_single]
  set J := Finset.univ.filter fun u : Gn g N => P (u : Mt g N) with hJ
  have hφ1 : φ 1 = 0 := by
    have e := hφ 1 1 h1 h1
    rw [mul_one] at e
    linear_combination -e
  have h1J : (1 : Gn g N) ∈ J := by
    rw [hJ, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [Units.val_one]; exact h1⟩
  have hJne : (J.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨1, h1J⟩)
  have hmulJ : ∀ u ∈ J, ∀ v ∈ J, u * v ∈ J := by
    intro u hu v hv
    rw [hJ, Finset.mem_filter] at hu hv ⊢
    exact ⟨Finset.mem_univ _, by rw [Units.val_mul]; exact hmul _ _ hu.2 hv.2⟩
  have hx : ∀ u ∈ J, ∀ v ∈ J, (ψ (φ ((u * v : Gn g N) : Mt g N)))⁻¹ =
      (ψ (φ (u : Mt g N)))⁻¹ * (ψ (φ (v : Mt g N)))⁻¹ := by
    intro u hu v hv
    rw [hJ, Finset.mem_filter] at hu hv
    rw [Units.val_mul, hφ _ _ hu.2 hv.2, AddChar.map_add_eq_mul, mul_inv]
  have hshift : ∀ u ∈ J, ∑ v ∈ J, MonoidAlgebra.single (u * v) (ψ (φ ((u * v : Gn g N) : Mt g N)))⁻¹ =
      ∑ w ∈ J, MonoidAlgebra.single w (ψ (φ (w : Mt g N)))⁻¹ := by
    intro u hu
    have himg : J.image (fun v => u * v) = J := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        rw [Finset.mem_image] at hw
        obtain ⟨v, hv, rfl⟩ := hw
        exact hmulJ u hu v hv
      · rw [Finset.card_image_of_injective _ (mul_right_injective u)]
    conv_rhs => rw [← himg]
    rw [Finset.sum_image (mul_right_injective u).injOn]
  refine ⟨?_, ?_⟩
  · rw [smul_mul_smul_comm, Finset.sum_mul_sum]
    have hsq : ∑ u ∈ J, ∑ v ∈ J, MonoidAlgebra.single u (ψ (φ (u : Mt g N)))⁻¹ *
          MonoidAlgebra.single v (ψ (φ (v : Mt g N)))⁻¹ =
        ∑ _u ∈ J, ∑ w ∈ J, MonoidAlgebra.single w (ψ (φ (w : Mt g N)))⁻¹ := by
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [← hshift u hu]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [MonoidAlgebra.single_mul_single, hx u hu v hv]
    rw [hsq, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    rw [mul_assoc, inv_mul_cancel₀ hJne, mul_one]
  · rw [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, smul_eq_mul,
      Finset.sum_eq_single (1 : Gn g N)]
    · simp [hφ1]
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd h1J h

theorem card_uni {N : ℕ} (Q : Fin N × Fin N → Prop) (P : Mt g N → Prop)
    (hP : ∀ M, P M ↔ IsUniUp M ∧ ∀ p : Fin N × Fin N, p.1 < p.2 → Q p → M p.1 p.2 = 0) :
    (Finset.univ.filter fun u : Gn g N => P (u : Mt g N)).card =
      g ^ (Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2 ∧ ¬ Q p).card := by
  let S := {p : Fin N × Fin N // p.1 < p.2 ∧ ¬ Q p}
  let mk : (S → ZMod g) → Mt g N := fun f i j =>
    if i = j then 1 else if h : i < j ∧ ¬ Q (i, j) then f ⟨(i, j), h⟩ else 0
  have hmk_up : ∀ f, IsUniUp (mk f) := by
    intro f a b
    constructor
    · intro hba
      have hab : a ≠ b := ne_of_gt hba
      simp only [mk, if_neg hab]
      rw [dif_neg]
      intro h
      exact absurd (lt_trans h.1 hba) (lt_irrefl _)
    · intro hab
      simp only [mk, if_pos hab]
  have hmk_unit : ∀ f, IsUnit (mk f) := by
    intro f
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isUpperTriangular]
    · have hd : ∀ i, mk f i i = 1 := fun i => (hmk_up f i i).2 rfl
      simp only [hd, Finset.prod_const_one, isUnit_one]
    · intro i j hji
      exact (hmk_up f i j).1 hji
  have hPmk : ∀ f, P (mk f) := by
    intro f
    rw [hP]
    refine ⟨hmk_up f, fun p hp hq => ?_⟩
    have hne : p.1 ≠ p.2 := ne_of_lt hp
    simp only [mk, if_neg hne]
    rw [dif_neg]
    exact fun h => h.2 hq
  let e : {u : Gn g N // P (u : Mt g N)} ≃ (S → ZMod g) :=
    { toFun := fun u p => (u.1 : Mt g N) p.1.1 p.1.2
      invFun := fun f => ⟨(hmk_unit f).unit, by rw [IsUnit.unit_spec]; exact hPmk f⟩
      left_inv := by
        intro u
        apply Subtype.ext
        apply Units.ext
        rw [IsUnit.unit_spec]
        ext i j
        have hu := (hP _).1 u.2
        simp only [mk]
        by_cases hij : i = j
        · rw [if_pos hij, ← hij]
          exact ((hu.1 i i).2 rfl).symm
        · rw [if_neg hij]
          by_cases h : i < j ∧ ¬ Q (i, j)
          · rw [dif_pos h]
          · rw [dif_neg h]
            rcases lt_or_gt_of_ne hij with hlt | hgt
            · exact (hu.2 (i, j) hlt (not_not.mp fun hq => h ⟨hlt, hq⟩)).symm
            · exact ((hu.1 i j).1 hgt).symm
      right_inv := by
        intro f
        funext p
        show mk f p.1.1 p.1.2 = f p
        simp only [mk]
        rw [if_neg (ne_of_lt p.2.1), dif_pos (show p.1.1 < p.1.2 ∧ ¬ Q (p.1.1, p.1.2) from p.2)] }
  have hL : (Finset.univ.filter fun u : Gn g N => P (u : Mt g N)).card =
      Fintype.card {u : Gn g N // P (u : Mt g N)} := (Fintype.card_subtype _).symm
  have hS : Fintype.card S = (Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2 ∧ ¬ Q p).card :=
    Fintype.card_subtype _
  rw [hL, Fintype.card_congr e, Fintype.card_fun, ZMod.card, hS]

theorem card_lt (N : ℕ) :
    (Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2).card = N * (N - 1) / 2 := by
  have h1 : ∀ j : Fin N, (Finset.univ.filter fun i : Fin N => i < j).card = (j : ℕ) := fun j => by
    rw [← Fin.card_Iio j]
    congr 1
    ext i
    simp
  calc (Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2).card
      = ∑ j : Fin N, (Finset.univ.filter fun i : Fin N => i < j).card := by
        rw [Finset.card_filter, Fintype.sum_prod_type_right]
        simp only [Finset.card_filter]
    _ = ∑ j : Fin N, (j : ℕ) := Finset.sum_congr rfl fun j _ => h1 j
    _ = ∑ i ∈ Finset.range N, i := Fin.sum_univ_eq_sum_range (fun i => i) N
    _ = N * (N - 1) / 2 := Finset.sum_range_id N

theorem card_col {N : ℕ} (s k : ℕ) (hc : s + k < N) (P : Mt g N → Prop)
    (hP : ∀ M, P M ↔ IsUniUp M ∧ ∀ a, s ≤ a → a < s + k → entN M a (s + k) = 0) :
    (((Finset.univ.filter fun u : Gn g N => P (u : Mt g N)).card : ℂ))⁻¹ =
      (g : ℂ) ^ k * ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹ := by
  have hQ := card_uni (fun p : Fin N × Fin N => s ≤ (p.1 : ℕ) ∧ (p.2 : ℕ) = s + k) P (by
    intro M
    rw [hP]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h p hp hq
      have hlt : (p.1 : ℕ) < s + k := hq.2 ▸ Fin.lt_def.mp hp
      have hz := h p.1 hq.1 hlt
      rw [← hq.2] at hz
      simpa [entN] using hz
    · intro h a ha1 ha2
      have haN : a < N := by omega
      have hz := h (⟨a, haN⟩, ⟨s + k, hc⟩) (Fin.mk_lt_mk.mpr ha2) ⟨ha1, rfl⟩
      simpa [entN, haN, hc] using hz)
  have hcount : (Finset.univ.filter fun p : Fin N × Fin N =>
      p.1 < p.2 ∧ (s ≤ (p.1 : ℕ) ∧ (p.2 : ℕ) = s + k)).card = k := by
    refine (Finset.card_bij (t := Finset.range k) (fun p _ => (p.1 : ℕ) - s) ?_ ?_ ?_).trans
      (Finset.card_range k)
    · intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨_, h1, h2, h3⟩ := hp
      rw [Fin.lt_def] at h1
      rw [Finset.mem_range]
      omega
    · intro p hp q hq h
      rw [Finset.mem_filter] at hp hq
      obtain ⟨_, hp1, hp2, hp3⟩ := hp
      obtain ⟨_, hq1, hq2, hq3⟩ := hq
      apply Prod.ext <;> apply Fin.ext <;> omega
    · intro b hb
      rw [Finset.mem_range] at hb
      refine ⟨(⟨s + b, by omega⟩, ⟨s + k, hc⟩), ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, Fin.mk_lt_mk.mpr (by omega), ?_, rfl⟩
        show s ≤ s + b
        omega
      · show s + b - s = b
        omega
  have hsplit : (Finset.univ.filter fun p : Fin N × Fin N =>
        p.1 < p.2 ∧ (s ≤ (p.1 : ℕ) ∧ (p.2 : ℕ) = s + k)).card +
      (Finset.univ.filter fun p : Fin N × Fin N =>
        p.1 < p.2 ∧ ¬ (s ≤ (p.1 : ℕ) ∧ (p.2 : ℕ) = s + k)).card = N * (N - 1) / 2 := by
    rw [← card_lt N, ← Finset.card_union_of_disjoint]
    · congr 1
      ext p
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    · rw [Finset.disjoint_filter]
      intro p _ h1 h2
      exact h2.2 h1.2
  have hg0 : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero
  have hQ' : (Finset.univ.filter fun u : Gn g N => P (u : Mt g N)).card =
      g ^ (Finset.univ.filter fun p : Fin N × Fin N =>
        p.1 < p.2 ∧ ¬ (s ≤ (p.1 : ℕ) ∧ (p.2 : ℕ) = s + k)).card := by
    convert hQ
  rw [hQ']
  rw [hcount] at hsplit
  rw [← hsplit, pow_add, Nat.cast_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hg0), one_mul]

theorem sup_mul {N : ℕ} (n : ℕ) (a b : ℕ → ℕ) (hab : ∀ i, b i = a i + 1) (M M' : Mt g N)
    (hM : IsUniUp M) (hM' : IsUniUp M') :
    ∑ i ∈ Finset.range n, entN (M * M') (a i) (b i) =
      ∑ i ∈ Finset.range n, entN M (a i) (b i) + ∑ i ∈ Finset.range n, entN M' (a i) (b i) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hab i]
  exact entN_mul M M' hM hM' (a i) (a i + 1) (Nat.lt_succ_self _) (fun b h1 h2 => absurd h2 (by omega))

theorem eDat_col {N : ℕ} (s k : ℕ) (hc : s + k < N) (P : Mt g N → Prop) (φ : Mt g N → ZMod g)
    (ψ : AddChar (ZMod g) ℂ)
    (hP : ∀ M, P M ↔ IsUniUp M ∧ ∀ a, s ≤ a → a < s + k → entN M a (s + k) = 0)
    (h1 : P 1) (hmul : ∀ M M', P M → P M' → P (M * M'))
    (hφ : ∀ M M', P M → P M' → φ (M * M') = φ M + φ M') :
    eDat g N P φ ψ * eDat g N P φ ψ = eDat g N P φ ψ ∧
      (eDat g N P φ ψ).coeff 1 = (g : ℂ) ^ k * ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹ := by
  obtain ⟨e1, e2⟩ := eDat_idem P φ ψ h1 hmul hφ
  exact ⟨e1, e2.trans (card_col s k hc P hP)⟩

end CompanionTheory.Member.UnipotentColumnData

open CompanionTheory.Member.UnipotentColumnData in
theorem CompanionTheory.Member.whittakerJacquetIdempotents_idem_coeff_one : ∀ (g : ℕ) [Fact g.Prime] (N k s : ℕ) (ψ : AddChar (ZMod g) ℂ), eU g N ψ * eU g N ψ = eU g N ψ ∧ (eU g N ψ).coeff 1 = ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹ ∧ (N = k + 2 * s + 1 → eJ g N k s ψ * eJ g N k s ψ = eJ g N k s ψ ∧ (eJ g N k s ψ).coeff 1 = (g : ℂ) ^ k * ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹) ∧ (k < N → eJ' g N k ψ * eJ' g N k ψ = eJ' g N k ψ ∧ (eJ' g N k ψ).coeff 1 = (g : ℂ) ^ k * ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹) := by
  intro g _ N k s ψ
  have hP : ∀ M : Mt g N, IsUniUp M ↔
      IsUniUp M ∧ ∀ p : Fin N × Fin N, p.1 < p.2 → False → M p.1 p.2 = 0 :=
    fun M => ⟨fun h => ⟨h, fun _ _ hf => hf.elim⟩, fun h => h.1⟩
  have hcard := card_uni (fun _ => False) IsUniUp hP
  obtain ⟨e1, e2⟩ := eDat_idem (g := g) (N := N) IsUniUp
    (fun M => ∑ i ∈ Finset.range (N - 1), entN M i (i + 1)) ψ uni_one
    (fun M M' hM hM' => uni_mul M M' hM hM')
    (fun M M' hM hM' => sup_mul (N - 1) (fun i => i) (fun i => i + 1) (fun _ => rfl) M M' hM hM')
  refine ⟨e1, e2.trans ?_, ?_, ?_⟩
  · rw [hcard]
    simp only [not_false_eq_true, and_true, card_lt, Nat.cast_pow]
  · intro hN
    have hc : s + k < N := by omega
    unfold eJ
    refine eDat_col (g := g) s k hc _ (phiJ k s) ψ (fun M => Iff.rfl)
      ⟨uni_one, fun a _ ha => entN_one a (s + k) ha⟩ ?_ ?_
    · intro M M' hM hM'
      refine ⟨uni_mul M M' hM.1 hM'.1, fun a ha1 ha2 => ?_⟩
      rw [entN_mul M M' hM.1 hM'.1 a (s + k) ha2 (fun b hb1 hb2 => hM'.2 b (by omega) hb2),
        hM.2 a ha1 ha2, hM'.2 a ha1 ha2, add_zero]
    · intro M M' hM hM'
      have e1 : ∑ i ∈ Finset.range (s - 1), entN (M * M') i (i + 1) =
          ∑ i ∈ Finset.range (s - 1), entN M i (i + 1) + ∑ i ∈ Finset.range (s - 1), entN M' i (i + 1) :=
        sup_mul (s - 1) (fun i => i) (fun i => i + 1) (fun _ => rfl) M M' hM.1 hM'.1
      have e3 : ∑ i ∈ Finset.range (s - 1), entN (M * M') (s + k + 1 + i) (s + k + 2 + i) =
          ∑ i ∈ Finset.range (s - 1), entN M (s + k + 1 + i) (s + k + 2 + i) +
            ∑ i ∈ Finset.range (s - 1), entN M' (s + k + 1 + i) (s + k + 2 + i) :=
        sup_mul (s - 1) (fun i => s + k + 1 + i) (fun i => s + k + 2 + i) (fun i => by omega)
          M M' hM.1 hM'.1
      have e4 : ∑ a ∈ Finset.range (k - 1), entN (M * M') (s + a) (s + a + 1) =
          ∑ a ∈ Finset.range (k - 1), entN M (s + a) (s + a + 1) +
            ∑ a ∈ Finset.range (k - 1), entN M' (s + a) (s + a + 1) :=
        sup_mul (k - 1) (fun a => s + a) (fun a => s + a + 1) (fun _ => rfl) M M' hM.1 hM'.1
      unfold phiJ
      rw [e1, e3, e4]
      split_ifs with hs
      · rw [entN_mul M M' hM.1 hM'.1 (s - 1) (s + k) (by omega)
            (fun b hb1 hb2 => hM'.2 b (by omega) hb2),
          entN_mul M M' hM.1 hM'.1 (s + k) (s + k + 1) (by omega) (fun b hb1 hb2 => by omega)]
        ring
      · ring
  · intro hk
    unfold eJ'
    refine eDat_col (g := g) 0 k (by omega) _ _ ψ ?_
      ⟨uni_one, fun a ha => entN_one a k ha⟩ ?_
      (fun M M' hM hM' => sup_mul (N - 1) (fun i => i) (fun i => i + 1) (fun _ => rfl) M M' hM.1 hM'.1)
    · intro M
      simp only [zero_le, true_implies, zero_add]
    · intro M M' hM hM'
      refine ⟨uni_mul M M' hM.1 hM'.1, fun a ha => ?_⟩
      rw [entN_mul M M' hM.1 hM'.1 a k ha (fun b _ hb2 => hM'.2 b hb2), hM.2 a ha, hM'.2 a ha, add_zero]

end

section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
theorem _root_.GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField : ∀ (g : ℕ) [Fact g.Prime] (N k s : ℕ) (ψ : AddChar (ZMod g) ℂ), eU g N ψ * eU g N ψ = eU g N ψ ∧ (eU g N ψ).coeff 1 = ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹ ∧ (N = k + 2 * s + 1 → eJ g N k s ψ * eJ g N k s ψ = eJ g N k s ψ ∧ (eJ g N k s ψ).coeff 1 = (g : ℂ) ^ k * ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹) ∧ (k < N → eJ' g N k ψ * eJ' g N k ψ = eJ' g N k ψ ∧ (eJ' g N k ψ).coeff 1 = (g : ℂ) ^ k * ((g : ℂ) ^ (N * (N - 1) / 2))⁻¹) := by
  intro g _ N k s ψ
  exact CompanionTheory.Member.whittakerJacquetIdempotents_idem_coeff_one g N k s ψ

end
