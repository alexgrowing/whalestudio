import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemShellUIffDepth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapLtSwapIffOfAddTwo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FIwasawa

noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory.WeylCell.U21HeisenbergElement

variable {L : Type} [Field L]

def heisM {n : ℕ} (i j k : Fin n) (p q r : L) : Matrix (Fin n) (Fin n) L :=
  1 + Matrix.single i j p + Matrix.single j k q + Matrix.single i k r

theorem heisM_apply {n : ℕ} (i j k : Fin n) (p q r : L) (s t : Fin n) :
    heisM i j k p q r s t = (if s = t then 1 else 0) + (if i = s ∧ j = t then p else 0) +
      (if j = s ∧ k = t then q else 0) + (if i = s ∧ k = t then r else 0) := by
  simp [heisM, Matrix.one_apply, Matrix.single_apply]

theorem heisM_mul {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (p q r p' q' r' : L) :
    heisM i j k p q r * heisM i j k p' q' r' = heisM i j k (p + p') (q + q') (r + r' + p * q') := by
  simp only [heisM, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hij.symm, Matrix.single_mul_single_of_ne _ _ _ _ hjk.symm,
    Matrix.single_mul_single_of_ne _ _ _ _ hik.symm, Matrix.single_add]
  abel

theorem heisM_zero {n : ℕ} (i j k : Fin n) : heisM i j k (0 : L) 0 0 = 1 := by
  simp [heisM]

def Heisenberg₂ {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (p q r : L) : GL (Fin n) L :=
  ⟨heisM i j k p q r, heisM i j k (-p) (-q) (p * q - r),
    by rw [heisM_mul hij hjk hik]; convert heisM_zero i j k using 2 <;> ring,
    by rw [heisM_mul hij hjk hik]; convert heisM_zero i j k using 2 <;> ring⟩

theorem heis_val {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (p q r : L) :
    ((Heisenberg₂ hij hjk hik p q r : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = heisM i j k p q r := rfl

theorem heis_inv_val {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (p q r : L) :
    (((Heisenberg₂ hij hjk hik p q r)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      heisM i j k (-p) (-q) (p * q - r) := rfl

theorem map_heisM_rev (σ : L →+* L) {n : ℕ} {i j k : Fin n} (hr : i.rev = k) (hj : j.rev = j) (p q r : L)
    (s t : Fin n) : σ (heisM i j k p q r t.rev s.rev) = heisM i j k (σ q) (σ p) (σ r) s t := by
  have e1 : ∀ x : Fin n, i = x.rev ↔ k = x := fun x => by
    rw [← hr]; exact ⟨fun h => by rw [h, Fin.rev_rev], fun h => by rw [← h, Fin.rev_rev]⟩
  have e2 : ∀ x : Fin n, k = x.rev ↔ i = x := fun x => by rw [← hr]; exact Fin.rev_inj
  have e3 : ∀ x : Fin n, j = x.rev ↔ j = x := fun x => by
    conv_lhs => rw [← hj]
    exact Fin.rev_inj
  simp only [heisM_apply, e1, e2, e3, Fin.rev_inj, map_add, apply_ite σ, map_one, map_zero, eq_comm (a := t) (b := s),
    and_comm (a := k = t), and_comm (a := j = t)]
  ring

theorem heis_mem_GU_iff (σ : L →+* L) {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hr : i.rev = k) (hj : j.rev = j) (p q r : L) :
    Heisenberg₂ hij hjk hik p q r ∈ GU σ n ↔ σ q = -p ∧ σ p = -q ∧ σ r = p * q - r := by
  rw [GlobalTheory.LGrp.mem_GU_iff]
  simp only [heis_inv_val, heis_val, map_heisM_rev σ hr hj]
  constructor
  · intro h
    have h1 := h i j
    have h2 := h j k
    have h3 := h i k
    simp [heisM_apply, hij, hjk, hik, hij.symm, hjk.symm, hik.symm] at h1 h2 h3
    exact ⟨h1.symm, h2.symm, h3.symm⟩
  · rintro ⟨h1, h2, h3⟩ s t
    rw [h1, h2, h3]

theorem monomial_mul_apply {n : ℕ} {t : Equiv.Perm (Fin n)} {Y : GL (Fin n) L} (hY : IsWeylRep t Y)
    (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    ((Y : Matrix (Fin n) (Fin n) L) * M) i j = (Y : Matrix (Fin n) (Fin n) L) i (t⁻¹ i) * M (t⁻¹ i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (t⁻¹ i)]
  · intro l _ hl
    rw [hY i l (fun h => hl (by rw [h]; simp)), zero_mul]
  · simp

theorem heisM_mul_opp {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (b d c y x z : L)
    (h1 : 1 + b * x + c * z = 0) (h2 : b + c * y = 0) (h3 : x + d * z = 0) (s t : Fin n) :
    (heisM i j k b d c * heisM k j i y x z) s t = (if s = t then 1 else 0) - (if i = s ∧ i = t then 1 else 0) +
      (if i = s ∧ k = t then c else 0) + (if j = s ∧ j = t then d * y else 0) + (if j = s ∧ k = t then d else 0) +
      (if k = s ∧ i = t then z else 0) + (if k = s ∧ j = t then y else 0) := by
  simp only [heisM, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne _ _ _ _ hjk.symm, Matrix.single_mul_single_of_ne _ _ _ _ hjk,
    Matrix.add_apply, Matrix.single_apply, Matrix.one_apply, Matrix.zero_apply]
  have f1 : (if i = s ∧ i = t then b * x else 0) + (if i = s ∧ i = t then c * z else 0) =
      -(if i = s ∧ i = t then 1 else 0) := by
    split_ifs
    · linear_combination h1
    · ring
  have f2 : (if i = s ∧ j = t then b else 0) + (if i = s ∧ j = t then c * y else 0) = 0 := by
    split_ifs
    · exact h2
    · ring
  have f3 : (if j = s ∧ i = t then x else 0) + (if j = s ∧ i = t then d * z else 0) = 0 := by
    split_ifs
    · exact h3
    · ring
  linear_combination f1 + f2 + f3

variable [Valued L (WithZero (Multiplicative ℤ))]

theorem mem_KU_of_int {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {n : ℕ} (g : GU σ n)
    (hg : ∀ s t, Valued.v (((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) s t) ≤ 1) : g ∈ KU σ n := by
  rw [← SetLike.mem_coe, GlobalTheory.LFun.IntPtsUnitary.coe_KU]
  refine P.cartan_mem_of_entries (intL L) _ hg fun s t => ?_
  rw [(GlobalTheory.LGrp.mem_GU_iff σ n (g : GL (Fin n) L)).1 g.2 s t]
  show Valued.v (σ _) ≤ 1
  rw [hσ]; exact hg _ _

theorem v_heisM_le {n : ℕ} (i j k : Fin n) {p q r : L} (hp : Valued.v p ≤ 1) (hq : Valued.v q ≤ 1)
    (hr : Valued.v r ≤ 1) (s t : Fin n) : Valued.v (heisM i j k p q r s t) ≤ 1 := by
  rw [heisM_apply]
  refine Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_) ?_ <;>
    split_ifs <;> simp [*]

theorem ordL_one' : ordL (1 : L) = 0 :=
  P.fIwasawa_ordL_unit 1 1 (by rw [map_one]) (by rw [map_one]) (mul_one 1)

theorem ordL_inv {x : L} (hx : x ≠ 0) : ordL x⁻¹ = -ordL x := by
  have h := P.fIwasawa_ordL_mul x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, ordL_one'] at h
  omega

theorem ordL_monomial_entry {n : ℕ} {t : Equiv.Perm (Fin n)} {Y : GL (Fin n) L} (hY : IsWeylRep t Y)
    (hYK : Y ∈ GLint (Fin n) (intL L)) (i : Fin n) :
    (Y : Matrix (Fin n) (Fin n) L) i (t⁻¹ i) ≠ 0 ∧ ordL ((Y : Matrix (Fin n) (Fin n) L) i (t⁻¹ i)) = 0 := by
  have h := congrFun (congrFun (Units.mul_inv Y) i) i
  rw [monomial_mul_apply hY, Matrix.one_apply_eq] at h
  exact ⟨left_ne_zero_of_mul_eq_one h, P.fIwasawa_ordL_unit _ _ (P.cartan_entries_of_mem _ Y hYK _ _)
    (P.cartan_entries_of_mem _ _ (inv_mem hYK) _ _) (by rw [mul_comm]; exact h)⟩

theorem isBorelU_one (σ : L →+* L) (n : ℕ) : IsBorelU (1 : GU σ n) := by
  intro i j h
  simp [Matrix.one_apply, ne_of_gt h]

theorem chiDeltaU_one (σ : L →+* L) (n m q : ℕ) (α : Fin m → ℂ) : chiDeltaU q α (1 : GU σ n) = 1 := by
  unfold chiDeltaU
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs
  · simp [ordL_one']
  · rfl

theorem v_sq_le {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {b d c : L} (hb : σ b = -d)
    (hc : σ c = b * d - c) : Valued.v d = Valued.v b ∧ Valued.v b * Valued.v b ≤ Valued.v c := by
  have h1 : Valued.v d = Valued.v b := by rw [← hσ b, hb, Valuation.map_neg]
  refine ⟨h1, ?_⟩
  have : b * d = σ c + c := by rw [hc]; ring
  rw [← h1, h1, ← map_mul]
  conv_lhs => rw [map_mul]; rhs; rw [← h1]
  rw [← map_mul, this]
  exact Valuation.map_add_le _ (hσ c).le le_rfl

theorem value_point : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ (α : Fin (n / 2) → ℂ) (φ : GU σ n → ℂ), IsSphericalU q α φ → φ 1 = 1 →
    ∀ u : cellU y, φ (y⁻¹ * (u : GU σ n)) = (α k / (q : ℂ) ^ 2) ^ depthU k (u : GU σ n) := by
  intro L _ _ _ ϖ σ q hq n k hk hn y hy hyw α φ hφ hφ1 u0
  obtain ⟨u, hu0⟩ := u0
  obtain ⟨⟨hu1, hu2⟩, hu3⟩ := (mem_cellU_last_iff L ϖ σ q hq n k hk hn y hy hyw u).1 hu0
  obtain ⟨hσσ, hσ, -⟩ := hq
  have hn2 : n = 2 * k.val + 3 := by
    have h2 := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 hn)
    have := k.isLt
    omega
  show φ (y⁻¹ * u) = (α k / (q : ℂ) ^ 2) ^ depthU k u
  unfold depthU cornerU
  have hs : simpleU k = Equiv.swap (lo k) (lo k).rev := by unfold simpleU; rw [if_neg hk]
  set a : Fin n := lo k with ha
  set a' : Fin n := a.rev with ha'
  have hav : a.val = k.val := rfl
  have ha'v : a'.val = k.val + 2 := by rw [ha', Fin.val_rev]; omega
  obtain ⟨m, hmv⟩ : ∃ m : Fin n, m.val = k.val + 1 := ⟨⟨k.val + 1, by omega⟩, rfl⟩
  have haa' : a ≠ a' := fun h => by have := congrArg Fin.val h; omega
  have ham : a ≠ m := fun h => by have := congrArg Fin.val h; omega
  have hma' : m ≠ a' := fun h => by have := congrArg Fin.val h; omega
  have hra : a'.rev = a := by rw [ha', Fin.rev_rev]
  have hrm : m.rev = m := Fin.ext (by rw [Fin.val_rev]; omega)
  set b := ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a m with hb
  set d := ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) m a' with hd
  set c := ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' with hc
  have hU : (u : GL (Fin n) L) = Heisenberg₂ ham hma' haa' b d c := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [heis_val, heisM_apply]
    by_cases h1 : a = i ∧ m = j
    · obtain ⟨rfl, rfl⟩ := h1
      simp [ham, ham.symm, hma'.symm, hb]
    by_cases h2 : m = i ∧ a' = j
    · obtain ⟨rfl, rfl⟩ := h2
      simp [ham, hma', hd]
    by_cases h3 : a = i ∧ a' = j
    · obtain ⟨rfl, rfl⟩ := h3
      simp [ham.symm, hma', haa', hc]
    rw [if_neg h1, if_neg h2, if_neg h3, add_zero, add_zero, add_zero]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [if_neg h.ne]
      refine hu3 i j h ?_
      simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff] at h h1 h2 h3 ⊢
      omega
    · rw [if_pos rfl]; exact hu2 i
    · rw [if_neg h.ne']; exact hu1 i j h
  obtain ⟨hσd, hσb, hσc⟩ := (heis_mem_GU_iff σ ham hma' haa' ha'.symm hrm b d c).1 (hU ▸ u.2)
  obtain ⟨hvd, hvb⟩ := v_sq_le hσ hσb hσc
  clear_value b d c
  by_cases hv : Valued.v c ≤ 1
  · have hb1 : Valued.v b ≤ 1 := by
      by_contra h
      push Not at h
      exact absurd (hvb.trans hv) (not_le.2 (one_lt_mul'' h h))
    have huK : u ∈ KU σ n := mem_KU_of_int hσ u fun s t => by
      rw [hU, heis_val]; exact v_heisM_le _ _ _ hb1 (hvd ▸ hb1) hv s t
    have h := hφ 1 1 (y⁻¹ * u) (isBorelU_one σ n) (mul_mem (inv_mem hy) huK)
    rw [one_mul, one_mul] at h
    have h0 : (-ordL c).toNat = 0 := by
      by_cases h0 : c = 0
      · rw [h0]; simp [ordL]
      · rw [GlobalTheory.BorelUMod.v_eq_exp h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at hv
        omega
    rw [h, chiDeltaU_one, hφ1, one_mul, h0, pow_zero]
  push Not at hv
  have hc0 : c ≠ 0 := fun h => by rw [h, map_zero] at hv; exact not_lt_of_ge zero_le' hv
  have he0 : σ c ≠ 0 := (map_ne_zero σ).2 hc0
  have hvc0 : Valued.v c ≠ 0 := (map_ne_zero _).2 hc0
  have hbc : Valued.v b ≤ Valued.v c := by
    rcases le_total (Valued.v b) 1 with h | h
    · exact h.trans hv.le
    · exact (le_mul_of_one_le_left' h).trans hvb
  have hℓ : Heisenberg₂ hma'.symm ham.symm haa'.symm (-b / c) (-d / σ c) (σ c)⁻¹ ∈ GU σ n := by
    rw [heis_mem_GU_iff σ _ _ _ hra hrm]
    refine ⟨?_, ?_, ?_⟩
    · rw [map_div₀, map_neg, hσd, hσσ]; ring
    · rw [map_div₀, map_neg, hσb]; ring
    · rw [map_inv₀, hσσ]
      field_simp
      linear_combination hσc
  let κ : GU σ n := ⟨_, hℓ⟩
  have hκ : κ ∈ KU σ n := mem_KU_of_int hσ κ fun s t => by
    refine v_heisM_le _ _ _ ?_ ?_ ?_ s t
    · rw [map_div₀, Valuation.map_neg]; exact div_le_one_of_le₀ hbc zero_le'
    · rw [map_div₀, Valuation.map_neg, hσ, hvd]; exact div_le_one_of_le₀ hbc zero_le'
    · rw [map_inv₀, hσ]; exact inv_le_one_of_one_le₀ hv.le
  set Pb : GU σ n := y⁻¹ * u * κ with hPb
  have e : Pb * 1 * κ⁻¹ = y⁻¹ * u := by rw [hPb]; group
  have hyK : (y : GL (Fin n) L) ∈ GLint (Fin n) (intL L) := hy.2
  have hyiw := IsWeylRep.inv hyw
  set M : Matrix (Fin n) (Fin n) L := heisM a m a' b d c * heisM a' m a (-b / c) (-d / σ c) (σ c)⁻¹ with hMdef
  have hM := heisM_mul_opp ham hma' haa' b d c (-b / c) (-d / σ c) (σ c)⁻¹
    (by field_simp; linear_combination hσc) (by field_simp; ring) (by field_simp; ring)
  rw [← hMdef] at hM
  have hP : ∀ i j, (((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      (((y : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (Equiv.swap a a' i) *
        M (Equiv.swap a a' i) j := by
    intro i j
    have : (((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
        (((y : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M := by
      rw [hPb, hMdef, ← heis_val ham hma' haa' b d c, ← heis_val hma'.symm ham.symm haa'.symm, ← hU]
      simp [Matrix.mul_assoc, κ]
    rw [this, monomial_mul_apply hyiw, inv_inv, hs]
  have hunit : ∀ i, (((y : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (Equiv.swap a a' i) ≠ 0 ∧
      ordL ((((y : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (Equiv.swap a a' i)) = 0 :=
    fun i => by
      have := ordL_monomial_entry hyiw (inv_mem hyK) i
      rwa [inv_inv, hs] at this
  clear_value M
  have hB : IsBorelU Pb := by
    intro i j hji
    have hj : j.val < i.val := hji
    rw [hP, hM]
    apply mul_eq_zero_of_right
    have n1 : ∀ s t : Fin n, s.val ≠ t.val → ¬ s = t := fun s t h e => h (congrArg Fin.val e)
    by_cases h1 : i = a
    · rw [h1] at hj
      rw [h1, Equiv.swap_apply_left]
      simp [n1 a' j (by omega), n1 a j (by omega), n1 m j (by omega)]
    by_cases h2 : i = a'
    · rw [h2] at hj
      rw [h2, Equiv.swap_apply_right]
      simp [n1 a' j (by omega), ham.symm, haa'.symm]
    rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
    by_cases h3 : i = m
    · rw [h3] at hj
      rw [h3]
      simp [n1 a' j (by omega), n1 m j (by omega), ham, hma'.symm]
    simp [Ne.symm h1, Ne.symm h2, Ne.symm h3, n1 i j (by omega)]
  rw [← e, hφ Pb 1 κ⁻¹ hB (inv_mem hκ), hφ1, mul_one]
  have hdiag : ∀ i : Fin n, i.val < k.val →
      ordL ((((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) = 0 := by
    intro i hi
    have h1 : a ≠ i := fun h => by have := congrArg Fin.val h; omega
    have h2 : a' ≠ i := fun h => by have := congrArg Fin.val h; omega
    have h3 : m ≠ i := fun h => by have := congrArg Fin.val h; omega
    have := (hunit i).2
    rw [hP, hM]
    rw [Equiv.swap_apply_of_ne_of_ne h1.symm h2.symm] at this ⊢
    simpa [h1, h2, h3] using this
  have hdiag_a : ordL ((((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a) = -ordL c := by
    obtain ⟨h1, h2⟩ := hunit a
    have h3 : M (Equiv.swap a a' a) a = (σ c)⁻¹ := by
      rw [Equiv.swap_apply_left, hM]
      simp [haa', haa'.symm, ham.symm, hma']
    have h4 : ordL (σ c) = ordL c := by simp only [ordL, hσ]
    rw [hP, h3, P.fIwasawa_ordL_mul _ _ h1 (inv_ne_zero he0), h2, ordL_inv he0, zero_add, h4]
  obtain ⟨D, hD⟩ : ∃ D : ℕ, -ordL c = D := by
    rw [GlobalTheory.BorelUMod.v_eq_exp hc0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hv
    exact Int.eq_ofNat_of_zero_le hv.le
  unfold chiDeltaU
  rw [Finset.prod_eq_single k]
  · rw [dif_pos (by omega)]
    show α k ^ ordL ((((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a) *
        (q : ℂ) ^ (-(ordL ((((Pb : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a)) *
          ((n : ℤ) - 1 - 2 * (k.val : ℤ))) = _
    have e3 : -(D : ℤ) * ((n : ℤ) - 1 - 2 * (k.val : ℤ)) = -((2 * D : ℕ) : ℤ) := by
      rw [show (n : ℤ) - 1 - 2 * (k.val : ℤ) = 2 by omega]; push_cast; ring
    rw [hdiag_a, hD, e3, Int.toNat_natCast, zpow_neg, zpow_natCast, zpow_natCast, div_pow, ← pow_mul, div_eq_mul_inv]
  · intro i _ hik
    have hi : i.val < k.val := by
      have : i.val ≠ k.val := fun h => hik (Fin.ext h)
      omega
    rw [dif_pos (by omega), hdiag _ hi]
    simp
  · simp

end GlobalTheory.WeylCell.U21HeisenbergElement
