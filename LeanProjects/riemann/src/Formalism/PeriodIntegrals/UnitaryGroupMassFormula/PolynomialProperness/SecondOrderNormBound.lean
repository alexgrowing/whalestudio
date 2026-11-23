import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.NsqMulVecLe

open Matrix Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.PolynomialProperness.CB

theorem sum_castLE {m n : ℕ} (h : n ≤ m) (f : Fin m → ℂ) (hf : ∀ l : Fin m, n ≤ l.val → f l = 0) :
    ∑ l, f l = ∑ t : Fin n, f (Fin.castLE h t) := by
  have hs := Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb h))) (f := f)
    (fun x _ hx => hf x (by
      by_contra hlt
      rw [not_le] at hlt
      exact hx (Finset.mem_map.2 ⟨⟨x.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)))
  rw [← hs, Finset.sum_map]
  rfl

def rws {m : ℕ} (i : Fin m) : Fin (i.val + 1) → Fin m := Fin.castLE (Nat.succ_le_of_lt i.isLt)

def cls {m : ℕ} (i j : Fin m) : Fin (i.val + 1) → Fin m := fun t =>
  if t.val < i.val then Fin.castLE (Nat.succ_le_of_lt i.isLt) t else j

theorem rws_val {m : ℕ} (i : Fin m) (t : Fin (i.val + 1)) : (rws i t).val = t.val := rfl

theorem det_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) {c : ℝ}
    (h : ∀ i j, ‖A i j‖ ≤ c) : ‖A.det‖ ≤ (Fintype.card ι).factorial * c ^ Fintype.card ι := by
  have h' : ∀ i j, NormedField.toAbsoluteValue ℂ (A i j) ≤ c := h
  have := Matrix.det_le h'
  rw [nsmul_eq_mul] at this
  exact this

theorem ut_entry_eq_det {m : ℕ} {L U : Matrix (Fin m) (Fin m) ℂ} (hL : L ∈ LTset m)
    (hU : U ∈ UTset m) (i j : Fin m) : U i j = ((L * U).submatrix (rws i) (cls i j)).det := by
  have hfac : (L * U).submatrix (rws i) (cls i j) =
      L.submatrix (rws i) (rws i) * U.submatrix (rws i) (cls i j) := by
    ext a b
    simp only [submatrix_apply, mul_apply]
    refine sum_castLE (Nat.succ_le_of_lt i.isLt) _ fun l hl => ?_
    have h0 : L (rws i a) l = 0 := hL.1 _ _ (by rw [Fin.lt_def, rws_val]; omega)
    rw [h0, zero_mul]
  have hlo : (L.submatrix (rws i) (rws i)).IsLowerTriangular := by
    intro a b hab
    have hab' : a < b := hab
    exact hL.1 _ _ hab'
  have hup : (U.submatrix (rws i) (cls i j)).IsUpperTriangular := by
    intro a b hab
    have hab' : b < a := hab
    have hb : b.val < i.val := by
      have := a.isLt; rw [Fin.lt_def] at hab'; omega
    show U (rws i a) (cls i j b) = 0
    simp only [cls, if_pos hb]
    exact hU.1 _ _ hab'
  rw [hfac, det_mul, det_of_isLowerTriangular _ hlo]
  have hl1 : ∀ t : Fin (i.val + 1), L.submatrix (rws i) (rws i) t t = 1 := fun t => hL.2 _
  have hcs : ∀ t : Fin i.val, U.submatrix (rws i) (cls i j) t.castSucc t.castSucc = 1 := by
    intro t
    have h2 : cls i j t.castSucc = rws i t.castSucc := by
      have ht : (t.castSucc : Fin (i.val + 1)).val < i.val := t.isLt
      simp only [cls, if_pos ht]; rfl
    show U (rws i t.castSucc) (cls i j t.castSucc) = 1
    rw [h2]; exact hU.2 _
  have hlast1 : rws i (Fin.last i.val) = i := Fin.ext rfl
  have hlast2 : cls i j (Fin.last i.val) = j := by
    simp only [cls, Fin.val_last, lt_irrefl, if_false]
  rw [Finset.prod_eq_one (fun t _ => hl1 t), one_mul, det_of_isUpperTriangular hup,
    Fin.prod_univ_castSucc, Finset.prod_eq_one (fun t _ => hcs t), one_mul]
  show U i j = U (rws i (Fin.last i.val)) (cls i j (Fin.last i.val))
  rw [hlast1, hlast2]

theorem mx_transpose {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) : mx Mᵀ = mx M := by
  apply le_antisymm
  · refine (GN.mx_le_iff _ (GN.mx_nonneg M)).2 fun i j => ?_
    rw [transpose_apply]; exact GN.entry_le_mx M j i
  · refine (GN.mx_le_iff _ (GN.mx_nonneg Mᵀ)).2 fun i j => ?_
    have := GN.entry_le_mx Mᵀ j i
    rwa [transpose_apply] at this

theorem ut_entry_bound {m : ℕ} {L U : Matrix (Fin m) (Fin m) ℂ} (hL : L ∈ LTset m)
    (hU : U ∈ UTset m) (i j : Fin m) : ‖U i j‖ ≤ m.factorial * (1 + mx (L * U)) ^ m := by
  rw [ut_entry_eq_det hL hU i j]
  have hd := det_norm_le ((L * U).submatrix (rws i) (cls i j)) (c := mx (L * U))
    (fun a b => GN.entry_le_mx (L * U) (rws i a) (cls i j b))
  rw [Fintype.card_fin] at hd
  have hx := GN.mx_nonneg (L * U)
  have hi : i.val + 1 ≤ m := Nat.succ_le_of_lt i.isLt
  have h1 : ((i.val + 1).factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le hi
  have h2 : mx (L * U) ^ (i.val + 1) ≤ (1 + mx (L * U)) ^ m :=
    (pow_le_pow_left₀ hx (by linarith) _).trans (pow_le_pow_right₀ (by linarith) hi)
  exact hd.trans (mul_le_mul h1 h2 (pow_nonneg hx _) (by positivity))

theorem lt_entry_bound {m : ℕ} {L U : Matrix (Fin m) (Fin m) ℂ} (hL : L ∈ LTset m)
    (hU : U ∈ UTset m) (i j : Fin m) : ‖L i j‖ ≤ m.factorial * (1 + mx (L * U)) ^ m := by
  have hUt : Uᵀ ∈ LTset m :=
    ⟨fun a b hab => by rw [transpose_apply]; exact hU.1 _ _ hab, fun a => hU.2 a⟩
  have hLt : Lᵀ ∈ UTset m :=
    ⟨fun a b hab => by rw [transpose_apply]; exact hL.1 _ _ hab, fun a => hL.2 a⟩
  have h := ut_entry_bound hUt hLt j i
  rwa [← transpose_mul, mx_transpose, transpose_apply] at h

theorem det_ut {m : ℕ} {U : Matrix (Fin m) (Fin m) ℂ} (hU : U ∈ UTset m) : U.det = 1 := by
  have h : U.IsUpperTriangular := fun a b hab => hU.1 _ _ hab
  rw [det_of_isUpperTriangular h]
  exact Finset.prod_eq_one fun t _ => hU.2 t

theorem det_lt {m : ℕ} {L : Matrix (Fin m) (Fin m) ℂ} (hL : L ∈ LTset m) : L.det = 1 := by
  have h : L.IsLowerTriangular := fun a b hab => hL.1 _ _ hab
  rw [det_of_isLowerTriangular _ h]
  exact Finset.prod_eq_one fun t _ => hL.2 t

theorem inv_entry_bound {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hM : M.det = 1) {c : ℝ}
    (hc : ∀ i j, ‖M i j‖ ≤ c) (i j : Fin (n + 1)) : ‖M⁻¹ i j‖ ≤ n.factorial * c ^ n := by
  rw [inv_def, hM, Ring.inverse_one, one_smul, adjugate_fin_succ_eq_det_submatrix, norm_mul,
    norm_pow, norm_neg, norm_one, one_pow, one_mul]
  have := det_norm_le (M.submatrix j.succAbove i.succAbove) (fun a b => hc _ _)
  rwa [Fintype.card_fin] at this

theorem mx_of_entry {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, ‖M i j‖ ≤ c) : mx M ≤ c := (GN.mx_le_iff M hc).2 h

theorem isUnit_det_monomialMatrix' {m : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hd : ∀ a, d a ≠ 0) :
    IsUnit (monoP w d).det := by
  have hQ : monoP w d * monoP w.symm (fun j => (d (w.symm j))⁻¹) = 1 := by
    ext i j
    simp only [monoP, mul_apply, of_apply, one_apply]
    rw [Finset.sum_eq_single (w.symm j)]
    · simp only [if_true, Equiv.apply_symm_apply]
      split_ifs with h
      · exact mul_inv_cancel₀ (hd _)
      · exact zero_mul _
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact isUnit_det_of_right_inverse hQ

def kap (m : ℕ) (P : Matrix (Fin m) (Fin m) ℂ) : ℝ := 1 + m * mx P⁻¹

def Kc (m : ℕ) (P : Matrix (Fin m) (Fin m) ℂ) : ℝ :=
  m.factorial * kap m P ^ m * (1 + (m : ℝ) ^ 2 * mx P * mx P⁻¹)

theorem kap_ge (m : ℕ) (P : Matrix (Fin m) (Fin m) ℂ) : 1 ≤ kap m P := by
  unfold kap; have := GN.mx_nonneg P⁻¹; have : (0 : ℝ) ≤ m := by positivity
  nlinarith

theorem factors_bound {m : ℕ} {P l u : Matrix (Fin m) (Fin m) ℂ} (hP : IsUnit P.det)
    (hl : l ∈ LPg P) (hu : u ∈ UTset m) :
    (∀ i j, ‖u i j‖ ≤ Kc m P * (1 + mx (l * P * u)) ^ m) ∧
    (∀ i j, ‖l i j‖ ≤ Kc m P * (1 + mx (l * P * u)) ^ m) := by
  have hPP : P⁻¹ * P = 1 := nonsing_inv_mul _ hP
  have hPP' : P * P⁻¹ = 1 := mul_nonsing_inv _ hP
  have hX := GN.mx_nonneg (l * P * u)
  have hmP := GN.mx_nonneg P
  have hmPi := GN.mx_nonneg P⁻¹
  have hm : (0 : ℝ) ≤ m := by positivity
  have hκ := kap_ge m P
  have hA : P⁻¹ * l * P * u = P⁻¹ * (l * P * u) := by simp only [Matrix.mul_assoc]
  have hmxA : 1 + mx (P⁻¹ * l * P * u) ≤ kap m P * (1 + mx (l * P * u)) := by
    rw [hA]
    have h1 := GN.mx_mul_le P⁻¹ (l * P * u)
    unfold kap
    have : (m : ℝ) * mx P⁻¹ * mx (l * P * u) ≥ 0 := by positivity
    nlinarith
  have hA1 : 0 ≤ 1 + mx (P⁻¹ * l * P * u) := by have := GN.mx_nonneg (P⁻¹ * l * P * u); linarith
  have hpow : (1 + mx (P⁻¹ * l * P * u)) ^ m ≤ kap m P ^ m * (1 + mx (l * P * u)) ^ m := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hA1 hmxA m
  have hfac : (0 : ℝ) ≤ m.factorial := by positivity
  have hK1 : ∀ i j, ‖u i j‖ ≤ m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m ∧
      ‖(P⁻¹ * l * P) i j‖ ≤ m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m := by
    intro i j
    constructor
    · refine (ut_entry_bound hl.2 hu i j).trans ?_
      exact (mul_le_mul_of_nonneg_left hpow hfac).trans_eq (by ring)
    · refine (lt_entry_bound hl.2 hu i j).trans ?_
      exact (mul_le_mul_of_nonneg_left hpow hfac).trans_eq (by ring)
  have hY : 0 ≤ m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m := by
    have : 0 ≤ kap m P := by linarith
    positivity
  have hext : 1 ≤ 1 + (m : ℝ) ^ 2 * mx P * mx P⁻¹ := by
    have : 0 ≤ (m : ℝ) ^ 2 * mx P * mx P⁻¹ := by positivity
    linarith
  have hKeq : Kc m P * (1 + mx (l * P * u)) ^ m =
      (m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m) * (1 + (m : ℝ) ^ 2 * mx P * mx P⁻¹) := by
    unfold Kc; ring
  constructor
  · intro i j
    rw [hKeq]
    exact (hK1 i j).1.trans (le_mul_of_one_le_right hY hext)
  · have hlt : mx (P⁻¹ * l * P) ≤ m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m :=
      mx_of_entry _ hY fun i j => (hK1 i j).2
    have hl_eq : l = P * (P⁻¹ * l * P) * P⁻¹ := by
      rw [show P * (P⁻¹ * l * P) * P⁻¹ = (P * P⁻¹) * l * (P * P⁻¹) by simp only [Matrix.mul_assoc],
        hPP', Matrix.one_mul, Matrix.mul_one]
    have hml : mx l ≤ (m : ℝ) ^ 2 * mx P * mx P⁻¹ * mx (P⁻¹ * l * P) := by
      have h1 := GN.mx_mul_le (P * (P⁻¹ * l * P)) P⁻¹
      have h2 := GN.mx_mul_le P (P⁻¹ * l * P)
      rw [← hl_eq] at h1
      have := GN.mx_nonneg (P * (P⁻¹ * l * P))
      have := GN.mx_nonneg (P⁻¹ * l * P)
      calc mx l ≤ m * mx (P * (P⁻¹ * l * P)) * mx P⁻¹ := h1
        _ ≤ m * (m * mx P * mx (P⁻¹ * l * P)) * mx P⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ hmPi
            exact mul_le_mul_of_nonneg_left h2 hm
        _ = (m : ℝ) ^ 2 * mx P * mx P⁻¹ * mx (P⁻¹ * l * P) := by ring
    intro i j
    rw [hKeq]
    have hc : 0 ≤ (m : ℝ) ^ 2 * mx P * mx P⁻¹ := by positivity
    calc ‖l i j‖ ≤ mx l := GN.entry_le_mx l i j
      _ ≤ (m : ℝ) ^ 2 * mx P * mx P⁻¹ * mx (P⁻¹ * l * P) := hml
      _ ≤ (m : ℝ) ^ 2 * mx P * mx P⁻¹ * (m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m) :=
          mul_le_mul_of_nonneg_left hlt hc
      _ ≤ (m.factorial * kap m P ^ m * (1 + mx (l * P * u)) ^ m) *
            (1 + (m : ℝ) ^ 2 * mx P * mx P⁻¹) := by nlinarith

end PI.PolynomialProperness.CB

namespace PI.PolynomialProperness

open CB in

theorem second_order_norm_bound : MonomialFactorizationBound := by
  intro m P hP
  obtain ⟨w, d, hd, hPeq⟩ := hP
  have hPu : IsUnit P.det := by rw [hPeq]; exact isUnit_det_monomialMatrix' w d hd
  cases m with
  | zero =>
    refine ⟨0, fun l _ u' _ => ?_⟩
    have h0 : ∀ M : Matrix (Fin 0) (Fin 0) ℂ, mx M ≤ 0 :=
      fun M => (GN.mx_le_iff M le_rfl).2 fun i => i.elim0
    simp only [zero_mul]
    exact ⟨h0 _, h0 _, h0 _, h0 _⟩
  | succ n =>
    have hK0 : 0 ≤ Kc (n + 1) P := by
      unfold Kc
      have := kap_ge (n + 1) P
      have := GN.mx_nonneg P; have := GN.mx_nonneg P⁻¹
      have : (0 : ℝ) ≤ 1 + ((n + 1 : ℕ) : ℝ) ^ 2 * mx P * mx P⁻¹ := by positivity
      have : (0 : ℝ) ≤ kap (n + 1) P := by linarith
      positivity
    refine ⟨n.factorial * Kc (n + 1) P ^ n + Kc (n + 1) P, fun l hl u' hu' => ?_⟩
    obtain ⟨hbu, hbl⟩ := factors_bound hPu hl hu'
    set X := mx (l * P * u') with hXdef
    have hX : 0 ≤ X := GN.mx_nonneg _
    have hY : 0 ≤ Kc (n + 1) P * (1 + X) ^ (n + 1) := by positivity
    have hfn : (0 : ℝ) ≤ n.factorial * Kc (n + 1) P ^ n := by positivity
    have hCge : Kc (n + 1) P ≤ n.factorial * Kc (n + 1) P ^ n + Kc (n + 1) P := by linarith
    have hmain : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        (∀ i j, ‖M i j‖ ≤ Kc (n + 1) P * (1 + X) ^ (n + 1)) →
        mx M ≤ (n.factorial * Kc (n + 1) P ^ n + Kc (n + 1) P) * (1 + X) ^ (n + 1) := by
      intro M hM
      refine mx_of_entry M (by positivity) fun i j => (hM i j).trans ?_
      exact mul_le_mul_of_nonneg_right hCge (by positivity)
    have hinv : ∀ M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, M.det = 1 →
        (∀ i j, ‖M i j‖ ≤ Kc (n + 1) P * (1 + X) ^ (n + 1)) →
        mx M⁻¹ ≤ (n.factorial * Kc (n + 1) P ^ n + Kc (n + 1) P) * (1 + X) ^ ((n + 1 - 1) * (n + 1)) := by
      intro M hdet hM
      have e : (1 + X) ^ ((n + 1 - 1) * (n + 1)) = ((1 + X) ^ (n + 1)) ^ n := by
        rw [Nat.add_sub_cancel, ← pow_mul, mul_comm]
      rw [e]
      refine mx_of_entry _ (by positivity) fun i j => (inv_entry_bound M hdet hM i j).trans ?_
      rw [mul_pow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    refine ⟨hmain l hbl, hmain u' hbu, hinv l (det_lt hl.1) hbl, hinv u' (det_ut hu') hbu⟩

end PI.PolynomialProperness
