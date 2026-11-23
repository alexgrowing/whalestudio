import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PairSym

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.PolynomialWeightAction

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

abbrev FinalTheorems (m n : ℕ) := (Fin n × Fin m) ⊕ (Fin n × Fin m)

def phi (ε : Fin m → Bool) : FinalTheorems m n → (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool)
  | Sum.inl x => if ε x.2 then Sum.inl (x.2, x.1, false) else Sum.inr (x.2, x.1, true)
  | Sum.inr y => if ε y.2 then Sum.inr (y.2, y.1, false) else Sum.inl (y.2, y.1, true)

theorem phi_injective (ε : Fin m → Bool) : Function.Injective (phi (n := n) ε) := by
  rintro (⟨i, a⟩ | ⟨i, a⟩) (⟨j, b⟩ | ⟨j, b⟩) h <;> simp only [phi] at h <;> split_ifs at h <;> simp_all

theorem mem_range_phi (ε : Fin m → Bool) (v : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool))
    (h : inF1 ε (Sum.elim id id v)) : v ∈ Set.range (phi ε) := by
  rcases v with ⟨a, i, b⟩ | ⟨a, i, b⟩
  · simp only [inF1, Sum.elim_inl, id] at h
    subst h
    cases hε : ε a
    · exact ⟨Sum.inr (i, a), by simp [phi, hε]⟩
    · exact ⟨Sum.inl (i, a), by simp [phi, hε]⟩
  · simp only [inF1, Sum.elim_inr, id] at h
    subst h
    cases hε : ε a
    · exact ⟨Sum.inl (i, a), by simp [phi, hε]⟩
    · exact ⟨Sum.inr (i, a), by simp [phi, hε]⟩

theorem vars_subset (ε : Fin m → Bool) (s : Sym m n) (hs : SymbolInFirstFamily ε s) :
    (↑s.vars : Set ((Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool))) ⊆ Set.range (phi ε) := by
  intro v hv
  rw [Finset.mem_coe, mem_vars_iff_mem_support] at hv
  obtain ⟨d, hd, hvd⟩ := hv
  apply mem_range_phi
  rcases v with k | k
  · exact hs d hd k (Or.inl (Finsupp.mem_support_iff.mp hvd))
  · exact hs d hd k (Or.inr (Finsupp.mem_support_iff.mp hvd))

theorem rename_vec (ε : Fin m → Bool) (a : Fin m) (i : Fin n) :
    rename (phi ε) (X (Sum.inl (i, a)) : MvPolynomial (FinalTheorems m n) ℂ) = vecVar ε a i := by
  simp only [rename_X, phi, vecVar]; split_ifs <;> rfl

theorem rename_cov (ε : Fin m → Bool) (b : Fin m) (i : Fin n) :
    rename (phi ε) (X (Sum.inr (i, b)) : MvPolynomial (FinalTheorems m n) ℂ) = covVar ε b i := by
  simp only [rename_X, phi, covVar]; split_ifs <;> rfl

def Dsrc (i j : Fin n) : Derivation ℂ (MvPolynomial (FinalTheorems m n) ℂ) (MvPolynomial (FinalTheorems m n) ℂ) :=
  mkDerivation ℂ (Sum.elim (fun x : Fin n × Fin m => if x.1 = j then X (Sum.inl (i, x.2)) else 0)
    (fun y : Fin n × Fin m => if y.1 = i then -X (Sum.inr (j, y.2)) else 0))

theorem Dsrc_inl (i j l : Fin n) (a : Fin m) :
    Dsrc (m := m) i j (X (Sum.inl (l, a))) = if l = j then X (Sum.inl (i, a)) else 0 := by
  simp [Dsrc, mkDerivation_X]

theorem Dsrc_inr (i j l : Fin n) (b : Fin m) :
    Dsrc (m := m) i j (X (Sum.inr (l, b))) = if l = i then -X (Sum.inr (j, b)) else 0 := by
  simp [Dsrc, mkDerivation_X]

theorem symK_rename_X (ε : Fin m → Bool) (i j : Fin n) (v : FinalTheorems m n) :
    symK ε i j (rename (phi ε) (X v)) = rename (phi ε) (Dsrc (m := m) i j (X v)) := by
  rcases v with ⟨l, a⟩ | ⟨l, b⟩
  · rw [Dsrc_inl]
    by_cases hl : l = j <;> cases h : ε a <;> simp [phi, symK, mkDerivation_X, h, hl]
  · rw [Dsrc_inr]
    by_cases hl : l = i <;> cases h : ε b <;> simp [phi, symK, mkDerivation_X, h, hl]

theorem symK_rename (ε : Fin m → Bool) (i j : Fin n) (p : MvPolynomial (FinalTheorems m n) ℂ) :
    symK ε i j (rename (phi ε) p) = rename (phi ε) (Dsrc (m := m) i j p) := by
  refine MvPolynomial.induction_on (motive := fun p => symK ε i j (rename (phi ε) p) =
    rename (phi ε) (Dsrc (m := m) i j p)) p ?_ ?_ ?_
  · intro a
    simp [MvPolynomial.derivation_C]
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro p v hp
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hp, symK_rename_X]

theorem Dsrc_eq_zero (ε : Fin m → Bool) (i j : Fin n) (p : MvPolynomial (FinalTheorems m n) ℂ)
    (h : symK ε i j (rename (phi ε) p) = 0) : Dsrc (m := m) i j p = 0 := by
  rw [symK_rename] at h
  exact rename_injective _ (phi_injective ε) (h.trans (map_zero _).symm)

def act (g : Matrix (Fin n) (Fin n) ℂ) : MvPolynomial (FinalTheorems m n) ℂ →ₐ[ℂ] MvPolynomial (FinalTheorems m n) ℂ :=
  aeval (Sum.elim (fun x : Fin n × Fin m => ∑ k, C (g x.1 k) * X (Sum.inl (k, x.2)))
    (fun y : Fin n × Fin m => ∑ k, C (g⁻¹ k y.1) * X (Sum.inr (k, y.2))))

theorem act_comp (A B : Matrix (Fin n) (Fin n) ℂ) :
    act (m := m) (B * A) = (act A).comp (act B) := by
  apply MvPolynomial.algHom_ext
  rintro (⟨l, a⟩ | ⟨l, b⟩)
  · simp only [act, AlgHom.comp_apply, aeval_X, Sum.elim_inl, map_sum, map_mul, aeval_C,
      MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  · simp only [act, AlgHom.comp_apply, aeval_X, Sum.elim_inr, map_sum, map_mul, aeval_C,
      MvPolynomial.algebraMap_eq, Matrix.mul_inv_rev, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum,
      mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    ring

theorem act_mul (A B : Matrix (Fin n) (Fin n) ℂ) (q : MvPolynomial (FinalTheorems m n) ℂ) :
    act (A * B) q = act B (act A q) := by
  rw [act_comp]; rfl

theorem fix_of_exp (δ : Derivation ℂ (MvPolynomial (FinalTheorems m n) ℂ) (MvPolynomial (FinalTheorems m n) ℂ))
    (φ : MvPolynomial (FinalTheorems m n) ℂ →ₐ[ℂ] MvPolynomial (FinalTheorems m n) ℂ) (c : ℂ)
    (hφ : ∀ v, φ (X v) = X v + C c * δ (X v))
    (hδ : ∀ v, ∃ (w : FinalTheorems m n) (r : ℂ), δ (X v) = C r * X w ∧ δ (X w) = 0)
    (p : MvPolynomial (FinalTheorems m n) ℂ) (hp : δ p = 0) : φ p = p := by
  classical
  let Φ : MvPolynomial (FinalTheorems m n) ℂ →ₐ[ℂ] Polynomial (MvPolynomial (FinalTheorems m n) ℂ) :=
    aeval (fun v => Polynomial.C (X v) + Polynomial.X * Polynomial.C (C c * δ (X v)))
  have hΦδ : ∀ v, Φ (δ (X v)) = Polynomial.C (δ (X v)) := by
    intro v
    obtain ⟨w, r, h1, h2⟩ := hδ v
    rw [h1]
    simp [Φ, h2, MvPolynomial.algebraMap_eq, Polynomial.C_mul]
  have hC : Φ (C c) = Polynomial.C (C c) := by
    simp [Φ, MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply]
  have hX : ∀ v, Φ (X v) = Polynomial.C (X v) + Polynomial.X * Polynomial.C (C c * δ (X v)) := by
    intro v; simp [Φ]
  have hder : ∀ q, Polynomial.derivative (Φ q) = Φ (C c * δ q) := by
    intro q
    refine MvPolynomial.induction_on (motive := fun q => Polynomial.derivative (Φ q) = Φ (C c * δ q)) q ?_ ?_ ?_
    · intro a
      simp [Φ, MvPolynomial.derivation_C, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
    · intro p q hp hq
      simp only [map_add, Polynomial.derivative_add, hp, hq, mul_add]
    · intro p v hp
      rw [map_mul, Polynomial.derivative_mul, hp, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      simp only [mul_add, map_add, map_mul, hΦδ, hX, hC, Polynomial.derivative_add, Polynomial.derivative_C,
        Polynomial.derivative_mul, Polynomial.derivative_X, zero_add, one_mul, mul_zero, add_zero, Polynomial.C_mul]
      ring
  have hev1 : ∀ q, Polynomial.eval 1 (Φ q) = φ q := by
    intro q
    refine MvPolynomial.induction_on (motive := fun q => Polynomial.eval 1 (Φ q) = φ q) q ?_ ?_ ?_
    · intro a
      simp [Φ, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
    · intro p q hp hq
      simp only [map_add, Polynomial.eval_add, hp, hq]
    · intro p v hp
      rw [map_mul, map_mul, Polynomial.eval_mul, hp, hX, hφ]
      simp
  have hev0 : ∀ q, Polynomial.eval 0 (Φ q) = q := by
    intro q
    refine MvPolynomial.induction_on (motive := fun q => Polynomial.eval 0 (Φ q) = q) q ?_ ?_ ?_
    · intro a
      simp [Φ, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
    · intro p q hp hq
      simp only [map_add, Polynomial.eval_add, hp, hq]
    · intro p v hp
      rw [map_mul, Polynomial.eval_mul, hp, hX]
      simp
  have h0 : Polynomial.derivative (Φ p) = 0 := by rw [hder, hp, mul_zero, map_zero]
  have hdeg : (Φ p).natDegree = 0 := Polynomial.derivative_eq_zero.mp h0
  calc φ p = Polynomial.eval 1 (Φ p) := (hev1 p).symm
    _ = Polynomial.eval 0 (Φ p) := by rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]; simp
    _ = p := hev0 p

theorem transvection_inv (i j : Fin n) (hij : i ≠ j) (c : ℂ) :
    (Matrix.transvection i j c)⁻¹ = Matrix.transvection i j (-c) := by
  apply Matrix.inv_eq_right_inv
  have h := Matrix.transvection_mul_transvection_same (i := i) (j := j) hij c (-c)
  rwa [add_neg_cancel, Matrix.transvection_zero] at h

theorem sum_ite_l (g : Fin n → ℂ) (F : Fin n → MvPolynomial (FinalTheorems m n) ℂ) (j0 : Fin n) :
    ∑ x, C (if j0 = x then g x else 0) * F x = C (g j0) * F j0 := by
  rw [Finset.sum_eq_single j0]
  · simp
  · intro x _ hx; rw [if_neg (Ne.symm hx)]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

theorem sum_ite_r (g : Fin n → ℂ) (F : Fin n → MvPolynomial (FinalTheorems m n) ℂ) (j0 : Fin n) :
    ∑ x, C (if x = j0 then g x else 0) * F x = C (g j0) * F j0 := by
  rw [Finset.sum_eq_single j0]
  · simp
  · intro x _ hx; rw [if_neg hx]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

theorem act_transvection (t : Matrix.TransvectionStruct (Fin n) ℂ) (p : MvPolynomial (FinalTheorems m n) ℂ)
    (hp : Dsrc (m := m) t.j t.i p = 0) : act t.toMatrix p = p := by
  obtain ⟨i0, j0, hij, c⟩ := t
  simp only [Matrix.TransvectionStruct.toMatrix_mk] at hp ⊢
  refine fix_of_exp (Dsrc j0 i0) (act (Matrix.transvection i0 j0 c)) c ?_ ?_ p hp
  · rintro (⟨l, a⟩ | ⟨l, b⟩)
    · rw [Dsrc_inl]
      have hT : ∀ k, Matrix.transvection i0 j0 c l k = (if l = k then 1 else 0) + (if i0 = l ∧ j0 = k then c else 0) := by
        intro k; simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]
      simp only [act, aeval_X, Sum.elim_inl, hT]
      by_cases hl : l = i0
      · subst hl
        rw [Fintype.sum_eq_add l j0 hij (fun x hx => by simp [Ne.symm hx.1, Ne.symm hx.2])]
        simp [hij, Ne.symm hij]
      · rw [Fintype.sum_eq_single l (fun x hx => by simp [Ne.symm hx, Ne.symm hl])]
        simp [hl, Ne.symm hl]
    · rw [Dsrc_inr]
      simp only [act, aeval_X, Sum.elim_inr]
      rw [transvection_inv i0 j0 hij]
      have hT : ∀ k, Matrix.transvection i0 j0 (-c) k l = (if k = l then 1 else 0) + (if i0 = k ∧ j0 = l then -c else 0) := by
        intro k; simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]
      simp only [hT]
      by_cases hl : l = j0
      · subst hl
        rw [Fintype.sum_eq_add l i0 (Ne.symm hij) (fun x hx => by simp [hx.1, Ne.symm hx.2])]
        simp [hij, Ne.symm hij]
      · rw [Fintype.sum_eq_single l (fun x hx => by simp [hx, Ne.symm hl])]
        simp [hl, Ne.symm hl]
  · rintro (⟨l, a⟩ | ⟨l, b⟩)
    · by_cases hl : l = i0
      · exact ⟨Sum.inl (j0, a), 1, by simp [Dsrc_inl, hl], by simp [Dsrc_inl, Ne.symm hij]⟩
      · exact ⟨Sum.inl (j0, a), 0, by simp [Dsrc_inl, hl], by simp [Dsrc_inl, Ne.symm hij]⟩
    · by_cases hl : l = j0
      · exact ⟨Sum.inr (i0, b), -1, by simp [Dsrc_inr, hl], by simp [Dsrc_inr, hij]⟩
      · exact ⟨Sum.inr (i0, b), 0, by simp [Dsrc_inr, hl], by simp [Dsrc_inr, hij]⟩

def wgt (l : Fin n) (d : FinalTheorems m n →₀ ℕ) : ℤ :=
  ∑ a : Fin m, (d (Sum.inl (l, a)) : ℤ) - ∑ b : Fin m, (d (Sum.inr (l, b)) : ℤ)

theorem Dsrc_diag_X (l : Fin n) (v : FinalTheorems m n) :
    Dsrc (m := m) l l (X v) = C ((wgt l (Finsupp.single v 1) : ℤ) : ℂ) * X v := by
  rcases v with ⟨k, a⟩ | ⟨k, b⟩
  · rw [Dsrc_inl]
    by_cases hk : k = l
    · subst hk; simp [wgt, Finsupp.single_apply]
    · simp [wgt, Finsupp.single_apply, hk, Ne.symm hk]
  · rw [Dsrc_inr]
    by_cases hk : k = l
    · subst hk; simp [wgt, Finsupp.single_apply]
    · simp [wgt, Finsupp.single_apply, hk, Ne.symm hk]

theorem wgt_add (l : Fin n) (d e : FinalTheorems m n →₀ ℕ) : wgt l (d + e) = wgt l d + wgt l e := by
  simp only [wgt, Finsupp.add_apply, Nat.cast_add, Finset.sum_add_distrib]; ring

theorem wgt_single (l : Fin n) (k : ℕ) (v : FinalTheorems m n) :
    wgt l (Finsupp.single v k) = k * wgt l (Finsupp.single v 1) := by
  simp only [wgt, Finsupp.single_apply]
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun x _ => ?_ <;> split_ifs <;> simp

theorem Dsrc_monomial (l : Fin n) (d : FinalTheorems m n →₀ ℕ) (r : ℂ) :
    Dsrc (m := m) l l (monomial d r) = C ((wgt l d : ℤ) : ℂ) * monomial d r := by
  induction d using Finsupp.induction with
  | zero =>
    rw [monomial_zero', MvPolynomial.derivation_C]; simp [wgt]
  | single_add v k f _ hk ih =>
    rw [monomial_single_add, Derivation.leibniz, ih, Derivation.leibniz_pow, Dsrc_diag_X, wgt_add,
      wgt_single l k v]
    have hX : (X v : MvPolynomial (FinalTheorems m n) ℂ) ^ (k - 1) * X v = X v ^ k := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk)]
    simp only [smul_eq_mul, nsmul_eq_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast, map_add, map_mul,
      map_natCast]
    calc _ = (k : MvPolynomial (FinalTheorems m n) ℂ) * C ((wgt l (Finsupp.single v 1) : ℤ) : ℂ) * (X v ^ (k - 1) * X v) *
            monomial f r + C ((wgt l f : ℤ) : ℂ) * (X v ^ k * monomial f r) := by ring
      _ = _ := by rw [hX]; ring

theorem coeff_Dsrc (l : Fin n) (p : MvPolynomial (FinalTheorems m n) ℂ) (d : FinalTheorems m n →₀ ℕ) :
    coeff d (Dsrc (m := m) l l p) = ((wgt l d : ℤ) : ℂ) * coeff d p := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum, coeff_sum]
  simp only [Dsrc_monomial, coeff_C_mul, coeff_monomial]
  rw [Finset.sum_eq_single d]
  · simp
  · intro b _ hb; simp [hb]
  · intro hd; simp [MvPolynomial.notMem_support_iff.mp hd]

theorem act_diag (D : Fin n → ℂ) (hD : ∀ l, D l ≠ 0) (p : MvPolynomial (FinalTheorems m n) ℂ)
    (hp : ∀ l, Dsrc (m := m) l l p = 0) : act (Matrix.diagonal D) p = p := by
  have hinv : (Matrix.diagonal D)⁻¹ = Matrix.diagonal (fun l => (D l)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    simp [mul_inv_cancel₀ (hD _)]
  let cv : FinalTheorems m n → ℂ := Sum.elim (fun x => D x.1) (fun y => (D y.1)⁻¹)
  have hgen : ∀ v, act (m := m) (Matrix.diagonal D) (X v) = C (cv v) * X v := by
    rintro (⟨l, a⟩ | ⟨l, b⟩)
    · simp only [act, aeval_X, Sum.elim_inl, Matrix.diagonal_apply]
      rw [sum_ite_l (fun _ => D l) (fun x => X (Sum.inl (x, a))) l]
      rfl
    · simp only [act, aeval_X, Sum.elim_inr, hinv, Matrix.diagonal_apply]
      rw [sum_ite_r (fun x => (D x)⁻¹) (fun x => X (Sum.inr (x, b))) l]
      rfl
  have hmono : ∀ (d : FinalTheorems m n →₀ ℕ) (r : ℂ), act (m := m) (Matrix.diagonal D) (monomial d r) =
      C (d.prod fun v k => cv v ^ k) * monomial d r := by
    intro d r
    rw [monomial_eq, map_mul, map_finsuppProd]
    simp only [map_pow, hgen, mul_pow, Finsupp.prod_mul, map_finsuppProd, map_pow]
    have hCr : act (m := m) (Matrix.diagonal D) (C r) = C r := by
      simp [act, MvPolynomial.algebraMap_eq]
    rw [hCr]
    ring
  have hw : ∀ d ∈ p.support, ∀ l, wgt l d = 0 := by
    intro d hd l
    have h := congrArg (coeff d) (hp l)
    rw [coeff_Dsrc, coeff_zero] at h
    have hc : coeff d p ≠ 0 := mem_support_iff.mp hd
    exact_mod_cast (mul_eq_zero.mp h).resolve_right hc
  have hprod : ∀ d ∈ p.support, (d.prod fun v k => cv v ^ k) = 1 := by
    intro d hd
    rw [Finsupp.prod_fintype _ _ (fun v => pow_zero _), Fintype.prod_sum_type]
    simp only [cv, Sum.elim_inl, Sum.elim_inr]
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun l _ => ?_
    dsimp only
    have h := hw d hd l
    simp only [wgt, sub_eq_zero] at h
    rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, inv_pow, ← div_eq_mul_inv,
      div_eq_one_iff_eq (pow_ne_zero _ (hD l))]
    congr 1
    exact_mod_cast h
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  conv_rhs => rw [p.as_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [hmono, hprod d hd, map_one, one_mul]

theorem act_unitary (u : Matrix (Fin n) (Fin n) ℂ) (hu : u ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (act (m := m) u : MvPolynomial (FinalTheorems m n) ℂ →ₐ[ℂ] MvPolynomial (FinalTheorems m n) ℂ) =
      aeval (Sum.elim (fun x : Fin n × Fin m => ∑ j, C (u x.1 j) * (X (Sum.inl (j, x.2)) : MvPolynomial (FinalTheorems m n) ℂ))
        (fun y : Fin n × Fin m => ∑ j, C (star (u y.1 j)) * X (Sum.inr (j, y.2)))) := by
  have hinv : u⁻¹ = star u := Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp hu)
  simp only [act, hinv, Matrix.star_apply]

theorem fftSym : FFTSym := by
  intro hFFT m n ε s hs hK
  obtain ⟨p, rfl⟩ := exists_rename_eq_of_vars_subset_range s (phi ε) (phi_injective ε) (vars_subset ε s hs)
  have hD : ∀ i j, Dsrc (m := m) i j p = 0 := fun i j => Dsrc_eq_zero ε i j p (hK i j)
  have hinv : ∀ g : Matrix (Fin n) (Fin n) ℂ, IsUnit g → act g p = p := by
    intro g hg
    refine Matrix.diagonal_transvection_induction (fun M => IsUnit M → act M p = p) g ?_ ?_ ?_ hg
    · intro D _ hU
      apply act_diag D _ p (fun l => hD l l)
      intro l hl
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal] at hU
      exact (Finset.prod_ne_zero_iff.mp hU.ne_zero) l (Finset.mem_univ l) hl
    · intro t _
      exact act_transvection t p (hD t.j t.i)
    · intro A B hA hB hAB
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, IsUnit.mul_iff] at hAB
      rw [act_mul, hA ((Matrix.isUnit_iff_isUnit_det A).mpr hAB.1),
        hB ((Matrix.isUnit_iff_isUnit_det B).mpr hAB.2)]
  have hu := hFFT (Fin n) (Fin m) (Fin m) p (fun u hu => by
    rw [← act_unitary u hu]
    exact hinv u ((Matrix.isUnit_iff_isUnit_det u).mpr
      (isUnit_iff_exists_inv.mpr ⟨(star u).det, by
        rw [← Matrix.det_mul, Matrix.mem_unitaryGroup_iff.mp hu, Matrix.det_one]⟩)))
  have h2 : rename (phi ε) p ∈ (Algebra.adjoin ℂ (Set.range fun ab : Fin m × Fin m =>
      ∑ i, (X (Sum.inl (i, ab.1)) : MvPolynomial (FinalTheorems m n) ℂ) * X (Sum.inr (i, ab.2)))).map (rename (phi ε)) :=
    Subalgebra.mem_map.mpr ⟨p, hu, rfl⟩
  rw [AlgHom.map_adjoin, ← Set.range_comp] at h2
  convert h2 using 3
  funext ab
  simp only [Function.comp_apply, map_sum, map_mul, rename_vec, rename_cov, pairSym]

end PositivityTheory.Rg.Sw.LC.PolynomialWeightAction

namespace PositivityTheory.Rg.Sw.LC

theorem fftSym : FFTSym := PolynomialWeightAction.fftSym

end PositivityTheory.Rg.Sw.LC
