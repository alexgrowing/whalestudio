import Mathlib
import Formalism.PeriodIntegrals.MirabIndex

namespace PI.MirabolicIndex₂

open Finset Matrix PI.MirabIndex

theorem prod_sub_pow (q n : ℕ) :
    ∏ i : Fin n, (q ^ (n + 1) - q ^ ((i : ℕ) + 1)) =
      q ^ ((n + 1) * n / 2) * ∏ i ∈ Finset.Ico 1 (n + 1), (q ^ i - 1) := by
  have hfac : ∀ i : Fin n, q ^ (n + 1) - q ^ ((i : ℕ) + 1) = q ^ ((i : ℕ) + 1) * (q ^ (n - i) - 1) := by
    intro i
    have hi : (i : ℕ) + 1 + (n - i) = n + 1 := by omega
    rw [Nat.mul_sub_one, ← pow_add, hi]
  have h2 : ∑ i ∈ Finset.range n, (i + 1) = (n + 1) * n / 2 := by
    have h3 := Finset.sum_range_id (n + 1)
    rw [Finset.sum_range_succ'] at h3
    simpa using h3
  rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun i => i + 1) n, h2]
  congr 1
  rw [Fin.prod_univ_eq_prod_range (fun i => q ^ (n - i) - 1) n, Finset.prod_Ico_eq_prod_range,
    Nat.add_sub_cancel, ← Finset.prod_range_reflect (fun j => q ^ (1 + j) - 1) n]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  show q ^ (n - i) - 1 = q ^ (1 + (n - 1 - i)) - 1
  rw [show 1 + (n - 1 - i) = n - i by omega]

variable {k : Type} [Field k] [Fintype k]

def eLast (n : ℕ) : Fin (n + 1) → k := fun j => if j = Fin.last n then 1 else 0

theorem isMirab_iff (n : ℕ) (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :
    IsMirab h ↔ h (Fin.last n) = eLast n := by
  unfold PI.MirabIndex.IsMirab
  exact ⟨fun H => funext H, fun H j => congrFun H j⟩

theorem one_last (n : ℕ) : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) = eLast n := by
  funext j
  by_cases h : j = Fin.last n
  · subst h
    simp [eLast]
  · simp [eLast, h, Matrix.one_apply, Ne.symm h]

theorem row_mul_eq (n : ℕ) {a b : Matrix (Fin (n + 1)) (Fin (n + 1)) k}
    (c : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (h : a (Fin.last n) = b (Fin.last n)) :
    (a * c) (Fin.last n) = (b * c) (Fin.last n) := by
  have h' : ∀ x, a (Fin.last n) x = b (Fin.last n) x := fun x => congrFun h x
  funext j
  simp only [Matrix.mul_apply, h']

theorem row_ne_zero (n : ℕ) (h : GL (Fin (n + 1)) k) :
    (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) ≠ 0 := by
  intro hz
  have h0 : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k).det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero (Fin.last n) (fun j => by simp [hz])
  exact (isUnit_iff_ne_zero.mp (Matrix.isUnits_det_units h)) h0

theorem exists_row (n : ℕ) (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k, (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) = v := by
  obtain ⟨p, hp⟩ : ∃ p, v p ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (funext hcon)
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n)
  let M : Matrix (Fin (n + 1)) (Fin (n + 1)) k := fun i j =>
    if i = Fin.last n then v (σ j) else if i = j then 1 else 0
  have hM : M.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    have hi : i ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hij' (Fin.le_last j))
    have hne : i ≠ j := ne_of_lt hij'
    simp [M, hi, hne]
  have hMdet : M.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular M hM]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    by_cases hi : i = Fin.last n
    · subst hi
      simp [M, σ, hp]
    · simp [M, hi]
  have hNdet : (M.submatrix id σ).det ≠ 0 := by
    rw [Matrix.det_permute']
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs, hMdet]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (M.submatrix id σ) hNdet, ?_⟩
  funext j
  show M (Fin.last n) (σ j) = v j
  simp [M, σ]

def rowMap (n : ℕ) (h : GL (Fin (n + 1)) k) : {v : Fin (n + 1) → k // v ≠ 0} :=
  ⟨(h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n), row_ne_zero n h⟩

theorem mirab_mul_inv (n : ℕ) (h g : GL (Fin (n + 1)) k)
    (hh : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) =
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n)) :
    IsMirab ((h * g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
  rw [isMirab_iff, Units.val_mul, row_mul_eq n _ hh, Units.mul_inv, one_last]

theorem row_mul_of_mirab (n : ℕ) (p g : GL (Fin (n + 1)) k)
    (hp : IsMirab (p : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) :
    ((p * g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) =
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) := by
  rw [Units.val_mul,
    row_mul_eq n _ (((isMirab_iff n _).mp hp).trans (one_last (k := k) n).symm),
    one_mul]

noncomputable def fiberEquiv (n : ℕ) (v : {v : Fin (n + 1) → k // v ≠ 0}) :
    {h : GL (Fin (n + 1)) k // rowMap n h = v} ≃
      {h : GL (Fin (n + 1)) k // IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)} :=
  let g := (exists_row n v.1 v.2).choose
  have hg : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) = v.1 :=
    (exists_row n v.1 v.2).choose_spec
  { toFun := fun h => ⟨h.1 * g⁻¹, mirab_mul_inv n h.1 g (by rw [hg]; exact congrArg Subtype.val h.2)⟩
    invFun := fun p => ⟨p.1 * g, Subtype.ext (by
      show ((p.1 * g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) = v.1
      rw [row_mul_of_mirab n p.1 g p.2, hg])⟩
    left_inv := fun h => Subtype.ext (by simp)
    right_inv := fun p => Subtype.ext (by simp) }

theorem card_nonzero (n : ℕ) :
    Nat.card {v : Fin (n + 1) → k // v ≠ 0} = Fintype.card k ^ (n + 1) - 1 := by
  classical
  show Nat.card {v : Fin (n + 1) → k // ¬ v = 0} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fun,
    Fintype.card_fin]

theorem card_GL_eq (n : ℕ) :
    Nat.card (GL (Fin (n + 1)) k) = (Fintype.card k ^ (n + 1) - 1) *
      Nat.card {h : GL (Fin (n + 1)) k // IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)} := by
  classical
  have hfib : ∀ v : {v : Fin (n + 1) → k // v ≠ 0},
      Nat.card {h : GL (Fin (n + 1)) k // rowMap n h = v} =
        Nat.card {h : GL (Fin (n + 1)) k // PI.MirabIndex.IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)} :=
    fun v => Nat.card_congr (fiberEquiv n v)
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (rowMap (k := k) n)), Nat.card_sigma]
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, card_nonzero]

theorem card_mirab (n : ℕ) :
    Nat.card {h : GL (Fin (n + 1)) k // IsMirab (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)} =
      Fintype.card k ^ ((n + 1) * n / 2) *
        ∏ i ∈ Finset.Ico 1 (n + 1), (Fintype.card k ^ i - 1) := by
  have h1 := card_GL_eq (k := k) n
  rw [Matrix.card_GL_field, Fin.prod_univ_succ] at h1
  simp only [Fin.val_zero, pow_zero, Fin.val_succ] at h1
  rw [prod_sub_pow] at h1
  have hk : 1 < Fintype.card k := Fintype.one_lt_card
  have hp : Fintype.card k ^ 1 ≤ Fintype.card k ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  rw [pow_one] at hp
  exact (Nat.eq_of_mul_eq_mul_left (by omega) h1).symm

abbrev Pairs (n : ℕ) := {p : Fin (n + 1) × Fin (n + 1) // p.1 < p.2}

def uniMat {n : ℕ} (f : Pairs n → k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  fun i j => if i = j then 1 else if h : i < j then f ⟨(i, j), h⟩ else 0

theorem uniMat_upper {n : ℕ} (f : Pairs n → k) : (uniMat f).IsUpperTriangular := by
  intro i j hij
  have hji : j < i := hij
  simp [uniMat, ne_of_gt hji, not_lt.mpr hji.le]

theorem uniMat_det {n : ℕ} (f : Pairs n → k) : (uniMat f).det = 1 := by
  rw [Matrix.det_of_upperTriangular (uniMat_upper f)]
  simp [uniMat]

noncomputable def uniGL {n : ℕ} (f : Pairs n → k) : GL (Fin (n + 1)) k :=
  GeneralLinearGroup.mkOfDetNeZero (uniMat f) (by rw [uniMat_det]; exact one_ne_zero)

theorem uniGL_coe {n : ℕ} (f : Pairs n → k) :
    ((uniGL f : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = uniMat f :=
  rfl

theorem isUniU_uniGL {n : ℕ} (f : Pairs n → k) :
    IsUniU ((uniGL f : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
  rw [uniGL_coe]
  unfold PI.MirabIndex.IsUniU
  exact ⟨fun i => by simp [uniMat], fun i j hji => uniMat_upper f hji⟩

noncomputable def uniEquiv (n : ℕ) :
    {u : GL (Fin (n + 1)) k // IsUniU (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k)} ≃
      (Pairs n → k) where
  toFun u p := (u.1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) p.1.1 p.1.2
  invFun f := ⟨uniGL f, isUniU_uniGL f⟩
  left_inv u := by
    obtain ⟨u, hd, hl⟩ := u
    apply Subtype.ext
    apply GeneralLinearGroup.ext
    intro i j
    simp only [uniGL_coe, uniMat]
    by_cases h : i = j
    · subst h; simp [hd i]
    · by_cases h' : i < j
      · simp [h, h']
      · have : j < i := lt_of_le_of_ne (not_lt.mp h') (Ne.symm h)
        simp [h, h', hl i j this]
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    have h1 : i ≠ j := ne_of_lt h
    simp [uniGL_coe, uniMat, h1, h]

theorem card_pairs (n : ℕ) : Fintype.card (Pairs n) = (n + 1) * n / 2 := by
  have e : Pairs n ≃ Σ j : Fin (n + 1), {i : Fin (n + 1) // i < j} :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
      invFun := fun x => ⟨(x.2.1, x.1), x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hj : ∀ j : Fin (n + 1), Fintype.card {i : Fin (n + 1) // i < j} = (j : ℕ) := fun j =>
    (Fintype.card_congr
      { toFun := fun i => (⟨i.1.val, i.2⟩ : Fin j.val)
        invFun := fun x => ⟨⟨x.val, lt_trans x.2 j.2⟩, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }).trans (Fintype.card_fin _)
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [hj]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) (n + 1), Finset.sum_range_id, Nat.add_sub_cancel]

theorem card_uni (n : ℕ) :
    Nat.card {u : GL (Fin (n + 1)) k // IsUniU (u : Matrix (Fin (n + 1)) (Fin (n + 1)) k)} =
      Fintype.card k ^ ((n + 1) * n / 2) := by
  classical
  rw [Nat.card_congr (uniEquiv (k := k) n), Nat.card_eq_fintype_card, Fintype.card_fun,
    card_pairs]

theorem mirabIndex : MirabIndex := by
  unfold PI.MirabIndex.MirabIndex
  intro k _ _ n
  rw [card_mirab, card_uni]

end PI.MirabolicIndex₂
