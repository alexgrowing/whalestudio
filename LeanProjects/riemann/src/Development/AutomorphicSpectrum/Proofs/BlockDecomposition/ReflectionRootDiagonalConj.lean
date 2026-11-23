import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjTransposeAntidiagFixed

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SwapRoot Matrix

namespace GlobalTheory.CompanionTheory.SwapRoot.Torus

section Mat

variable {L : Type} [Field L] {n : ℕ}

theorem blockM_mul_diag (a : ℕ) (h : 2 * (a + 2) ≤ n) (X Y X' Y' : Matrix (Fin 2) (Fin 2) L) (d d' : Fin n → L)
    (hI : ∀ p r, X p r * d (cI n a h r) = d' (cI n a h p) * X' p r)
    (hJ : ∀ p r, Y p r * d (cJ n a h r) = d' (cJ n a h p) * Y' p r)
    (hO : ∀ b, (∀ p, b ≠ cI n a h p) → (∀ p, b ≠ cJ n a h p) → d b = d' b) :
    blockM a h X Y * Matrix.diagonal d = Matrix.diagonal d' * blockM a h X' Y' := by
  ext b e
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hbI : ∃ p, b = cI n a h p
  · obtain ⟨p, rfl⟩ := hbI
    by_cases heI : ∃ r, e = cI n a h r
    · obtain ⟨r, rfl⟩ := heI
      rw [blockM_cI, blockM_cI]; exact hI p r
    · push_neg at heI
      have hb : ∀ r, cI n a h p ≠ cJ n a h r := cI_ne_cJ a h p
      rw [blockM_out a h _ _ (Or.inr heI) (Or.inl hb), blockM_out a h _ _ (Or.inr heI) (Or.inl hb)]
      have hne : cI n a h p ≠ e := fun hh => heI p hh.symm
      simp [Matrix.one_apply, hne]
  · push_neg at hbI
    by_cases hbJ : ∃ p, b = cJ n a h p
    · obtain ⟨p, rfl⟩ := hbJ
      by_cases heJ : ∃ r, e = cJ n a h r
      · obtain ⟨r, rfl⟩ := heJ
        rw [blockM_cJ, blockM_cJ]; exact hJ p r
      · push_neg at heJ
        rw [blockM_out a h _ _ (Or.inl hbI) (Or.inr heJ), blockM_out a h _ _ (Or.inl hbI) (Or.inr heJ)]
        have hne : cJ n a h p ≠ e := fun hh => heJ p hh.symm
        simp [Matrix.one_apply, hne]
    · push_neg at hbJ
      rw [blockM_out a h _ _ (Or.inl hbI) (Or.inl hbJ), blockM_out a h _ _ (Or.inl hbI) (Or.inl hbJ)]
      by_cases hbe : b = e
      · subst hbe
        simp [hO b hbI hbJ]
      · simp [Matrix.one_apply, hbe]

theorem partner_nU (σ : L →+* L) (x : L) : partner σ (nU x) = !![1, -σ x; 0, 1] := by
  have hc : cT σ (!![1, -x; 0, 1] : Matrix (Fin 2) (Fin 2) L) = !![1, 0; -σ x, 1] := by
    ext p r
    fin_cases p <;> fin_cases r <;> simp [cT]
  show w2 L * cT σ (!![1, -x; 0, 1] : Matrix (Fin 2) (Fin 2) L) * w2 L = _
  rw [hc]
  ext p r
  fin_cases p <;> fin_cases r <;> simp [w2, Matrix.mul_apply, Fin.sum_univ_two]

theorem partner_wU (σ : L →+* L) : partner σ (wU L) = w2 L := by
  show w2 L * cT σ (w2 L) * w2 L = _
  rw [conj_transpose_antidiag_fixed, weyl_mul_weyl, Matrix.one_mul]

theorem diag_unitary (σ : L →+* L) (t : GU σ n) (d : Fin n → L)
    (ht : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d) (p r : Fin n)
    (hpr : p.val + r.val + 1 = n) : σ (d p) * d r = 1 := by
  have h2 : cT σ ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * antiJ L n *
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = antiJ L n := t.2
  rw [ht] at h2
  have hc : cT σ (Matrix.diagonal d) = Matrix.diagonal (fun k => σ (d k)) := by
    ext b e
    by_cases hbe : b = e
    · subst hbe; simp [cT]
    · have : e ≠ b := fun hh => hbe hh.symm
      simp [cT, Matrix.diagonal_apply, hbe, this]
  rw [hc] at h2
  have h3 := congrFun (congrFun h2 p) r
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h3
  simpa [antiJ, hpr] using h3

theorem uR_mul_diag (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (t : GU σ n) (d : Fin n → L)
    (ht : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d)
    (hd : ∀ k, d k ≠ 0) (x : L) :
    uR σ hσ a h x * t = t * uR σ hσ a h (d (cI n a h 1) * (d (cI n a h 0))⁻¹ * x) := by
  have e0 : σ (d (cI n a h 0)) * d (cJ n a h 1) = 1 :=
    diag_unitary σ t d ht _ _ (by simp only [cI, cJ]; simp; omega)
  have e1 : σ (d (cI n a h 1)) * d (cJ n a h 0) = 1 :=
    diag_unitary σ t d ht _ _ (by simp only [cI, cJ]; simp; omega)
  have hd0 := hd (cI n a h 0)
  have hσ0 : σ (d (cI n a h 0)) ≠ 0 := by simpa using hd0
  apply Subtype.ext
  apply Units.ext
  show (((uR σ hσ a h x : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((uR σ hσ a h (d (cI n a h 1) * (d (cI n a h 0))⁻¹ * x) : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  rw [ht]
  simp only [uR, rootHom_val, partner_nU]
  refine blockM_mul_diag a h _ _ _ _ d d ?_ ?_ fun _ _ _ => rfl
  · intro p r
    fin_cases p <;> fin_cases r <;> simp [nU]
    field_simp
  · intro p r
    fin_cases p <;> fin_cases r <;> simp
    have e1' : d (cJ n a h 1) = (σ (d (cI n a h 0)))⁻¹ := eq_inv_of_mul_eq_one_right e0
    rw [e1']
    field_simp
    linear_combination (-(σ x)) * e1

def dS (a : ℕ) (h : 2 * (a + 2) ≤ n) (d : Fin n → L) (k : Fin n) : L :=
  if k = cI n a h 0 then d (cI n a h 1) else if k = cI n a h 1 then d (cI n a h 0) else
  if k = cJ n a h 0 then d (cJ n a h 1) else if k = cJ n a h 1 then d (cJ n a h 0) else d k

theorem sR_conj_val (σ : L →+* L) (hσ : ∀ x, σ (σ x) = x) (a : ℕ) (h : 2 * (a + 2) ≤ n) (t : GU σ n) (d : Fin n → L)
    (ht : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d) :
    (((sR σ hσ a h * t * sR σ hσ a h : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal (dS a h d) := by
  have n01 : cI n a h 0 ≠ cI n a h 1 := fun e => by simpa using cI_injective a h e
  have m01 : cJ n a h 0 ≠ cJ n a h 1 := fun e => by simpa using cJ_injective a h e
  have hne := cI_ne_cJ (n := n) a h
  have key : blockM a h (w2 L) (w2 L) * Matrix.diagonal d =
      Matrix.diagonal (dS a h d) * blockM a h (w2 L) (w2 L) := by
    refine blockM_mul_diag a h _ _ _ _ d _ ?_ ?_ ?_
    · intro p r
      fin_cases p <;> fin_cases r <;> simp [w2, dS, n01, n01.symm]
    · intro p r
      fin_cases p <;> fin_cases r <;> simp [w2, dS, m01, m01.symm, (hne _ _).symm]
    · intro b h1 h2
      simp [dS, h1, h2]
  have hs : (((sR σ hσ a h : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = blockM a h (w2 L) (w2 L) := by
    simp only [sR, rootHom_val, partner_wU]
    rfl
  show (((sR σ hσ a h : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((sR σ hσ a h : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = _
  rw [ht, hs, key, Matrix.mul_assoc, blockM_mul, weyl_mul_weyl, blockM_one, Matrix.mul_one]

end Mat

theorem prod_compare {m : ℕ} (χ : Fin m → ℂˣ) (Q : ℂ) (hQ : Q ≠ 0) (N : ℤ) (i j : Fin m) (hij : j.val = i.val + 1)
    (o o' : Fin m → ℤ) (h1 : o' i = o j) (h2 : o' j = o i) (h3 : ∀ k, k ≠ i → k ≠ j → o' k = o k) :
    (∏ k : Fin m, (χ k : ℂ) ^ (o' k) * Q ^ (-(o' k) * (N - 2 * (k.val : ℤ)))) * Q ^ (2 * (o j - o i)) =
      ∏ k : Fin m, ((χ (Equiv.swap i j k)) : ℂ) ^ (o k) * Q ^ (-(o k) * (N - 2 * (k.val : ℤ))) := by
  have hne : j ≠ i := fun e => by rw [e] at hij; omega
  have split : ∀ f : Fin m → ℂ, ∏ k, f k = f i * (f j * ∏ k ∈ (Finset.univ.erase i).erase j, f k) := fun f => by
    rw [Finset.mul_prod_erase (Finset.univ.erase i) f (by simp [hne]),
      Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
  rw [split, split (fun k => ((χ (Equiv.swap i j k)) : ℂ) ^ (o k) * Q ^ (-(o k) * (N - 2 * (k.val : ℤ))))]
  have hrest : ∏ k ∈ (Finset.univ.erase i).erase j, (χ k : ℂ) ^ (o' k) * Q ^ (-(o' k) * (N - 2 * (k.val : ℤ))) =
      ∏ k ∈ (Finset.univ.erase i).erase j, ((χ (Equiv.swap i j k)) : ℂ) ^ (o k) * Q ^ (-(o k) * (N - 2 * (k.val : ℤ))) := by
    refine Finset.prod_congr rfl fun k hk => ?_
    have hkj : k ≠ j := (Finset.mem_erase.1 hk).1
    have hki : k ≠ i := (Finset.mem_erase.1 (Finset.mem_erase.1 hk).2).1
    rw [h3 k hki hkj, Equiv.swap_apply_of_ne_of_ne hki hkj]
  rw [hrest, h1, h2, Equiv.swap_apply_left, Equiv.swap_apply_right, hij]
  generalize (∏ k ∈ (Finset.univ.erase i).erase j, ((χ (Equiv.swap i j k)) : ℂ) ^ (o k) * Q ^ (-(o k) * (N - 2 * (k.val : ℤ)))) = P
  have hq : Q ^ (-(o j) * (N - 2 * (i.val : ℤ))) * Q ^ (-(o i) * (N - 2 * ((i.val + 1 : ℕ) : ℤ))) * Q ^ (2 * (o j - o i)) =
      Q ^ (-(o i) * (N - 2 * (i.val : ℤ))) * Q ^ (-(o j) * (N - 2 * ((i.val + 1 : ℕ) : ℤ))) := by
    rw [← zpow_add₀ hQ, ← zpow_add₀ hQ, ← zpow_add₀ hQ]
    congr 1
    push_cast
    ring
  linear_combination ((χ i : ℂ) ^ (o j) * (χ j : ℂ) ^ (o i) * P) * hq

section Ord

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_mul' {x y : L} (hx : x ≠ 0) (hy : y ≠ 0) : ordL (x * y) = ordL x + ordL y := by
  have h1 := v_eq_exp' (mul_ne_zero hx hy)
  rw [map_mul, v_eq_exp' hx, v_eq_exp' hy, ← WithZero.exp_add] at h1
  have := WithZero.exp_injective h1
  omega

end Ord

theorem torus_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n : ℕ) (hU : IsUnramInv ϖ σ q) (a : ℕ) (h : 2 * (a + 2) ≤ n) (χ : Fin (n / 2) → ℂˣ) (i j : Fin (n / 2)), i.val = a → j.val = a + 1 → ∀ t : GU σ n, PositivityTheory.SphericalProduct.IsDiagM (t : GL (Fin n) L) →
    ∃ c : L, c ≠ 0 ∧ ∃ t' : GU σ n, IsBorelU t' ∧
      (∀ x : L, sR σ hU.1 a h * uR σ hU.1 a h x * t = t' * (sR σ hU.1 a h * uR σ hU.1 a h (c * x))) ∧
      chiDeltaU q (fun k => (χ k : ℂ)) t' * (q : ℂ) ^ (2 * ordL c) =
        chiDeltaU q (fun k => ((χ ∘ Equiv.swap i j) k : ℂ)) t := by
  intro L _ _ ϖ σ q n hU a h χ i j hi hj t hdiag
  have hσ := hU.1
  set d : Fin n → L := fun k => ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) k k with hddef
  have ht : ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal d := by
    ext b e
    by_cases hbe : b = e
    · subst hbe; simp [hddef]
    · rw [hdiag b e hbe]; simp [hbe]
  have hd : ∀ k, d k ≠ 0 := fun k hk => by
    have := diag_unitary σ t d ht (⟨n - 1 - k.val, by omega⟩ : Fin n) k (by simp; omega)
    rw [hk, mul_zero] at this
    exact zero_ne_one this
  have hq : (q : ℂ) ≠ 0 := by
    have : 2 ≤ q := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  have hsv := sR_conj_val σ hσ a h t d ht
  refine ⟨d (cI n a h 1) * (d (cI n a h 0))⁻¹, mul_ne_zero (hd _) (inv_ne_zero (hd _)),
    sR σ hσ a h * t * sR σ hσ a h, ?_, ?_, ?_⟩
  · intro b e hbe
    rw [hsv, Matrix.diagonal_apply_ne _ (ne_of_gt hbe)]
  · intro x
    have hs := sR_mul_sR σ hσ a h
    rw [mul_assoc (sR σ hσ a h) (uR σ hσ a h x) t, uR_mul_diag σ hσ a h t d ht hd x,
      mul_assoc (sR σ hσ a h * t), ← mul_assoc (sR σ hσ a h) (sR σ hσ a h), hs, one_mul, ← mul_assoc (sR σ hσ a h) t]
  · have hlt : ∀ k : Fin (n / 2), k.val < n := fun k => by have := k.2; omega
    set o : Fin (n / 2) → ℤ := fun k => ordL (d ⟨k.val, hlt k⟩) with hodef
    set o' : Fin (n / 2) → ℤ := fun k => ordL (dS a h d ⟨k.val, hlt k⟩) with ho'def
    have hL : chiDeltaU q (fun k => (χ k : ℂ)) (sR σ hσ a h * t * sR σ hσ a h) =
        ∏ k : Fin (n / 2), (χ k : ℂ) ^ (o' k) * (q : ℂ) ^ (-(o' k) * (((n : ℤ) - 1) - 2 * (k.val : ℤ))) := by
      unfold chiDeltaU
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [dif_pos (hlt k), hsv, Matrix.diagonal_apply_eq]
    have hR : chiDeltaU q (fun k => ((χ ∘ Equiv.swap i j) k : ℂ)) t =
        ∏ k : Fin (n / 2), (χ (Equiv.swap i j k) : ℂ) ^ (o k) * (q : ℂ) ^ (-(o k) * (((n : ℤ) - 1) - 2 * (k.val : ℤ))) := by
      unfold chiDeltaU
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [dif_pos (hlt k)]
      rfl
    have hci : (⟨i.val, hlt i⟩ : Fin n) = cI n a h 0 := Fin.ext (by simp [cI, hi])
    have hcj : (⟨j.val, hlt j⟩ : Fin n) = cI n a h 1 := Fin.ext (by simp [cI, hj])
    have n01 : cI n a h 0 ≠ cI n a h 1 := fun e => by simpa using cI_injective a h e
    have hoi : o i = ordL (d (cI n a h 0)) := by simp only [hodef, hci]
    have hoj : o j = ordL (d (cI n a h 1)) := by simp only [hodef, hcj]
    have hc : ordL (d (cI n a h 1) * (d (cI n a h 0))⁻¹) = o j - o i := by
      rw [ordL_mul' (hd _) (inv_ne_zero (hd _)), ordL_inv' (hd _), hoi, hoj]
      ring
    rw [hL, hR, hc]
    refine prod_compare χ _ hq _ i j (by omega) o o' ?_ ?_ ?_
    · simp only [ho'def, hci, hoj]
      simp [dS]
    · simp only [ho'def, hcj, hoi]
      simp [dS, n01.symm]
    · intro k hki hkj
      have hkn := k.2
      have e1 : ∀ p, (⟨k.val, hlt k⟩ : Fin n) ≠ cI n a h p := fun p e => by
        have := congrArg Fin.val e
        simp only [cI] at this
        have hp := p.2
        have hp' : p = 0 ∨ p = 1 := by omega
        rcases hp' with rfl | rfl
        · exact hki (Fin.ext (by simp at this; omega))
        · exact hkj (Fin.ext (by simp at this; omega))
      have e2 : ∀ p, (⟨k.val, hlt k⟩ : Fin n) ≠ cJ n a h p := fun p e => by
        have := congrArg Fin.val e
        simp only [cJ] at this
        have hp := p.2
        omega
      simp only [ho'def, hodef]
      simp [dS, e1, e2]

end GlobalTheory.CompanionTheory.SwapRoot.Torus

end
