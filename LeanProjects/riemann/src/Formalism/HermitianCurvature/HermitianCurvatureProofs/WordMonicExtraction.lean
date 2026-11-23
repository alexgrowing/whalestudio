import Formalism.HermitianCurvature.LevelRecursionCondNeeded

namespace Formalism.FourierDecayAlt.P.WordMonicExtraction

open Finset Polynomial Formalism.FourierDecayAlt.F7

private theorem lagsum_lemma {F : Type} [Field F] {d : ℕ} (v : Fin (d + 1) → F)
    (hv : Function.Injective v) (P : Polynomial F) (hP : P.natDegree ≤ d) :
    ∑ j, (∏ i ∈ Finset.univ.erase j, (v j - v i)⁻¹) * P.eval (v j) = P.coeff d := by
  have hdeg : P.degree < ((Finset.univ : Finset (Fin (d + 1))).card : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le hP)
  have hI := Lagrange.eq_interpolate (s := Finset.univ) (v := v) hv.injOn hdeg
  conv_rhs => rw [hI]
  rw [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hb : Lagrange.basis Finset.univ v j =
      Polynomial.C (∏ i ∈ Finset.univ.erase j, (v j - v i)⁻¹) *
        Lagrange.nodal (Finset.univ.erase j) v := by
    unfold Lagrange.basis Lagrange.basisDivisor Lagrange.nodal
    rw [Finset.prod_mul_distrib, map_prod]
  have hn : (Lagrange.nodal (Finset.univ.erase j) v).natDegree = d := by
    rw [Lagrange.natDegree_nodal, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, Nat.add_sub_cancel]
  have hm := (Lagrange.nodal_monic (s := Finset.univ.erase j) (v := v)).coeff_natDegree
  rw [hn] at hm
  rw [Polynomial.coeff_C_mul, hb, Polynomial.coeff_C_mul, hm]
  ring

theorem moment (d : ℕ) (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (k : ℕ) (hk : k ≤ d) :
    ∑ j, lagCo y j * y j ^ k = if k = d then 1 else 0 := by
  have h := lagsum_lemma y hy (Polynomial.X ^ k) (by rw [Polynomial.natDegree_X_pow]; exact hk)
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.coeff_X_pow] at h
  simp only [lagCo]
  rw [h]
  exact if_congr eq_comm rfl rfl

theorem lead_c {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (y : Fin (d + 1) → ℝ)
    (hy : Function.Injective y) (c : Fin (d + 1) → V) :
    c (Fin.last d) = ∑ j, ((lagCo y j : ℝ) : ℂ) • ∑ k : Fin (d + 1), ((y j : ℂ) ^ (k : ℕ)) • c k := by
  have hm : ∀ k : Fin (d + 1), (∑ j, ((lagCo y j : ℝ) : ℂ) * (y j : ℂ) ^ (k : ℕ)) =
      if (k : ℕ) = d then 1 else 0 := by
    intro k
    have h1 := moment d y hy k (Nat.lt_succ_iff.mp k.2)
    have h2 : (∑ j, ((lagCo y j : ℝ) : ℂ) * (y j : ℂ) ^ (k : ℕ)) =
        ((∑ j, lagCo y j * y j ^ (k : ℕ) : ℝ) : ℂ) := by
      push_cast
      try rfl
    rw [h2, h1]
    split_ifs <;> simp
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hm]
  rw [Finset.sum_eq_single (Fin.last d)]
  · simp
  · intro b _ hb
    have hbd : (b : ℕ) ≠ d := fun h => hb (Fin.ext (by simp [h]))
    simp [hbd]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem top_extract {W : ℝ → ℂ} {d : ℕ} {c : ℂ} (h : IsTopCoeff W d c) (y : Fin (d + 1) → ℝ)
    (hy : Function.Injective y) : ∑ i, ((lagCo y i : ℝ) : ℂ) * W (y i) = c := by
  unfold IsTopCoeff at h
  obtain ⟨P, hPd, hPc, hW⟩ := h
  have h1 := lagsum_lemma (fun i => ((y i : ℝ) : ℂ)) (fun a b hab => hy (Complex.ofReal_injective hab)) P hPd
  rw [hPc] at h1
  rw [← h1]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hW]
  simp only [lagCo]
  push_cast
  try rfl

section

variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]

theorem evR_smul (P : R[X]) (a : ℕ) (ha : P.natDegree ≤ a) (Y : ℝ) (X : M) :
    evR P Y • X = ∑ i ∈ range (a + 1), ((Y : ℂ) ^ i) • (P.coeff i • X) := by
  unfold evR
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le ha), Finset.sum_smul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← map_pow, ← Algebra.commutes, mul_smul, algebraMap_smul]

end

theorem isTop_sub {W W' : ℝ → ℂ} {d : ℕ} {c c' : ℂ} (h : IsTopCoeff W d c)
    (h' : IsTopCoeff W' d c') : IsTopCoeff (fun Y => W Y - W' Y) d (c - c') := by
  unfold IsTopCoeff at h h' ⊢
  obtain ⟨P, hP, hPc, hW⟩ := h
  obtain ⟨P', hP', hPc', hW'⟩ := h'
  exact ⟨P - P', (Polynomial.natDegree_sub_le _ _).trans (max_le hP hP'),
    by rw [Polynomial.coeff_sub, hPc, hPc'], fun Y => by simp only [Polynomial.eval_sub, hW, hW']⟩

theorem isTop_const_mul {W : ℝ → ℂ} {d : ℕ} {c : ℂ} (k : ℂ) (h : IsTopCoeff W d c) :
    IsTopCoeff (fun Y => k * W Y) d (k * c) := by
  unfold IsTopCoeff at h ⊢
  obtain ⟨P, hP, hPc, hW⟩ := h
  exact ⟨Polynomial.C k * P, (Polynomial.natDegree_C_mul_le _ _).trans hP,
    by rw [Polynomial.coeff_C_mul, hPc], fun Y => by simp only [Polynomial.eval_C_mul, hW]⟩

theorem natDegree_mono (h : ℂ) (i j : ℕ) :
    ((X : ℂ[X]) ^ i * (X + C h) ^ j).natDegree = i + j := by
  rw [(Polynomial.monic_X_pow i).natDegree_mul ((Polynomial.monic_X_add_C h).pow j),
    Polynomial.natDegree_X_pow, (Polynomial.monic_X_add_C h).natDegree_pow, Polynomial.natDegree_X_add_C,
    mul_one]

theorem coeff_mono (h : ℂ) (a b i j : ℕ) (hi : i ≤ a) (hj : j ≤ b) :
    ((X : ℂ[X]) ^ i * (X + C h) ^ j).coeff (a + b) = if i = a ∧ j = b then 1 else 0 := by
  by_cases hij : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := hij
    rw [if_pos ⟨rfl, rfl⟩]
    have hm := ((Polynomial.monic_X_pow i).mul ((Polynomial.monic_X_add_C h).pow j)).coeff_natDegree
    rw [natDegree_mono] at hm
    exact hm
  · rw [if_neg hij]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [natDegree_mono]
    omega

section

variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]

theorem pairTop (Ξ : Sesq M) (P₁ P₂ : R[X]) (a b : ℕ) (h : ℝ) (X X' : M)
    (ha : P₁.natDegree ≤ a) (hb : P₂.natDegree ≤ b) :
    IsTopCoeff (fun Y => Ξ (evR P₁ Y • X) (evR P₂ (Y + h) • X')) (a + b)
      (Ξ (P₁.coeff a • X) (P₂.coeff b • X')) := by
  unfold IsTopCoeff
  refine ⟨∑ i ∈ range (a + 1), ∑ k ∈ range (b + 1),
    Polynomial.C (Ξ (P₁.coeff i • X) (P₂.coeff k • X')) *
      (Polynomial.X ^ i * (Polynomial.X + Polynomial.C (h : ℂ)) ^ k), ?_, ?_, ?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k hk
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_mono]
    rw [Finset.mem_range] at hi hk
    omega
  · rw [Polynomial.finset_sum_coeff]
    simp_rw [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul]
    rw [Finset.sum_eq_single_of_mem a (Finset.mem_range.mpr (Nat.lt_succ_self a)) ?_]
    · rw [Finset.sum_eq_single_of_mem b (Finset.mem_range.mpr (Nat.lt_succ_self b)) ?_]
      · rw [coeff_mono _ _ _ _ _ le_rfl le_rfl, if_pos ⟨rfl, rfl⟩, mul_one]
      · intro k hk hkb
        rw [coeff_mono _ _ _ _ _ le_rfl (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)),
          if_neg (fun hh => hkb hh.2), mul_zero]
    · intro i hi hia
      apply Finset.sum_eq_zero
      intro k hk
      rw [coeff_mono _ _ _ _ _ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)), if_neg (fun hh => hia hh.1), mul_zero]
  · intro Y
    beta_reduce
    rw [evR_smul P₁ a ha Y X, evR_smul P₂ b hb (Y + h) X']
    simp only [map_sum, LinearMap.sum_apply, map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_add, map_pow, map_add, Complex.conj_ofReal,
      Complex.ofReal_add, Finset.mul_sum, Finset.sum_mul]
    first
      | (refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_)); ring)
      | (rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_)); ring)

noncomputable def letterVal (Ξ : Sesq M) (D : Dat R) (y : ℝ) (x x' : M) : ℂ :=
  Ξ ((evR D.B y + algebraMap ℂ R D.s * evR D.A y) • x) (evR D.Av (y + 1) • x') -
    Ξ (evR D.A y • x) (evR D.Bv (y + 1) • x')

theorem planeLetter (Ξ : Sesq M) (n : ℕ) (D : Dat R) (x x' : M) (hS : Shape n D.A D.B)
    (hSv : Shape n D.Av D.Bv) :
    IsTopCoeff (fun Y => letterVal Ξ D Y x x') (2 * n) (D.s * Ξ x x') := by
  obtain ⟨hAm, hAn, hBd⟩ := hS
  obtain ⟨hAvm, hAvn, hBvd⟩ := hSv
  have hBn : D.B.natDegree ≤ n := Polynomial.natDegree_le_of_degree_le hBd.le
  have hBvn : D.Bv.natDegree ≤ n := Polynomial.natDegree_le_of_degree_le hBvd.le
  have hB0 : D.B.coeff n = 0 := Polynomial.coeff_eq_zero_of_degree_lt hBd
  have hBv0 : D.Bv.coeff n = 0 := Polynomial.coeff_eq_zero_of_degree_lt hBvd
  have hA1 : D.A.coeff n = 1 := by
    rw [← hAn]
    exact hAm.coeff_natDegree
  have hAv1 : D.Av.coeff n = 1 := by
    rw [← hAvn]
    exact hAvm.coeff_natDegree
  have hP₁n : (D.B + Polynomial.C (algebraMap ℂ R D.s) * D.A).natDegree ≤ n :=
    (Polynomial.natDegree_add_le _ _).trans
      (max_le hBn ((Polynomial.natDegree_C_mul_le _ _).trans hAn.le))
  have hev : ∀ Y : ℝ, evR D.B Y + algebraMap ℂ R D.s * evR D.A Y =
      evR (D.B + Polynomial.C (algebraMap ℂ R D.s) * D.A) Y := by
    intro Y
    simp only [evR, Polynomial.eval_add, Polynomial.eval_C_mul]
  have t1 := pairTop Ξ (D.B + Polynomial.C (algebraMap ℂ R D.s) * D.A) D.Av n n 1 x x' hP₁n hAvn.le
  have t2 := pairTop Ξ D.A D.Bv n n 1 x x' hAn.le hBvn
  have ht := isTop_sub t1 t2
  unfold letterVal
  simp_rw [hev]
  rw [two_mul]
  convert ht using 1
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, hB0, hA1, hAv1, hBv0, zero_add, mul_one,
    one_smul, zero_smul, map_zero, sub_zero, algebraMap_smul, map_smul, LinearMap.smul_apply,
    smul_eq_mul]

theorem liftLetter (Ξ : Sesq M) (n s : ℕ) (D : Dat R) (A₀ A₀v : R[X]) (e t t' : ℂ) (x x' : M)
    (hs : D.s = 0) (he : e = 1 ∨ e = -1)
    (hA : D.A.Monic) (hAn : D.A.natDegree = n + s) (hAv : D.Av.Monic) (hAvn : D.Av.natDegree = n + s)
    (hA₀ : A₀.Monic) (hA₀n : A₀.natDegree = n) (hA₀v : A₀v.Monic) (hA₀vn : A₀v.natDegree = n)
    (hB : ∀ Y Y' : ℝ, Ξ (evR D.B Y • x) (evR D.Av Y' • x') =
      Ξ ((e * t⁻¹) • evR A₀ Y • x) (evR D.Av Y' • x'))
    (hBv : ∀ Y Y' : ℝ, Ξ (evR D.A Y • x) (evR D.Bv Y' • x') =
      Ξ (evR D.A Y • x) ((e * (starRingEnd ℂ t')⁻¹) • evR A₀v Y' • x')) :
    IsTopCoeff (fun Y => letterVal Ξ D Y x x') (2 * n + s) (e * (1 / t - 1 / t') * Ξ x x') := by
  have hA1 : D.A.coeff (n + s) = 1 := by
    rw [← hAn]
    exact hA.coeff_natDegree
  have hAv1 : D.Av.coeff (n + s) = 1 := by
    rw [← hAvn]
    exact hAv.coeff_natDegree
  have hA₀1 : A₀.coeff n = 1 := by
    rw [← hA₀n]
    exact hA₀.coeff_natDegree
  have hA₀v1 : A₀v.coeff n = 1 := by
    rw [← hA₀vn]
    exact hA₀v.coeff_natDegree
  have hce : starRingEnd ℂ e = e := by
    rcases he with rfl | rfl <;> simp
  have t1 := isTop_const_mul (e * t⁻¹) (pairTop Ξ A₀ D.Av n (n + s) 1 x x' hA₀n.le hAvn.le)
  have t2 := isTop_const_mul (e * t'⁻¹) (pairTop Ξ D.A A₀v (n + s) n 1 x x' hAn.le hA₀vn.le)
  have hdeg1 : n + (n + s) = 2 * n + s := by ring
  have hdeg2 : n + s + n = 2 * n + s := by ring
  rw [hdeg1] at t1
  rw [hdeg2] at t2
  have ht := isTop_sub t1 t2
  have hfun : (fun Y => letterVal Ξ D Y x x') = (fun Y =>
      e * t⁻¹ * Ξ (evR A₀ Y • x) (evR D.Av (Y + 1) • x') -
        e * t'⁻¹ * Ξ (evR D.A Y • x) (evR A₀v (Y + 1) • x')) := by
    funext Y
    unfold letterVal
    rw [hs, map_zero, zero_mul, add_zero, hB Y (Y + 1), hBv Y (Y + 1)]
    simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, map_mul,
      map_inv₀, Complex.conj_conj, hce]
  rw [hfun]
  convert ht using 1
  simp only [hA1, hAv1, hA₀1, hA₀v1, one_smul, one_div]
  ring

theorem Fw_concat (Ξ : Sesq M) (X X' : M) (l : Dat R × ℝ) (w : List (Dat R × ℝ)) (P P' : R) :
    Fw Ξ X X' (w ++ [l]) P P' =
      Fw Ξ ((evR l.1.B l.2 + algebraMap ℂ R l.1.s * evR l.1.A l.2) • X) (evR l.1.Av (l.2 + 1) • X')
          w P P' -
        Fw Ξ (evR l.1.A l.2 • X) (evR l.1.Bv (l.2 + 1) • X') w P P' := by
  induction w generalizing P P' with
  | nil =>
    simp only [List.nil_append, Fw, mul_smul]
  | cons m w ih =>
    simp only [List.cons_append, Fw]
    rw [ih, ih]
    ring

private theorem sumsnoc_lemma_2 {K m : ℕ} {β : Type} [AddCommMonoid β] (f : (Fin (K + 1) → Fin m) → β) :
    ∑ j, f j = ∑ jl : Fin m, ∑ j' : Fin K → Fin m, f (Fin.snoc j' jl) := by
  rw [← (Fin.snocEquiv (fun _ => Fin m)).sum_comp f, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  congr 1

private theorem sumlin_lemma_3 {ι κ : Type} [Fintype ι] [Fintype κ] (P : κ → ℝ) (L : ι → ℝ)
    (F G : ι → κ → ℂ) :
    ∑ i, ∑ k, ((P k * L i : ℝ) : ℂ) * (F i k - G i k) =
      ∑ i, ((L i : ℝ) : ℂ) * ((∑ k, ((P k : ℝ) : ℂ) * F i k) - ∑ k, ((P k : ℝ) : ℂ) * G i k) := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  push_cast
  ring

theorem word_gen (Ξ : Sesq M) (d : ℕ) (X X' : M) : ∀ (K : ℕ) (dat : Fin K → Dat R)
    (grid : Fin K → Fin (d + 1) → ℝ) (c : Fin K → ℂ),
    (∀ a (Q Q' : R), ∑ i, ((lagCo (grid a) i : ℝ) : ℂ) *
      letterVal Ξ (dat a) (grid a i) (Q • X) (Q' • X') = c a * Ξ (Q • X) (Q' • X')) →
    ∀ Q Q' : R, (∏ a, c a) * Ξ (Q • X) (Q' • X') =
      ∑ j : Fin K → Fin (d + 1), ((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) *
        Fw Ξ (Q • X) (Q' • X') (List.ofFn fun a => (dat a, grid a (j a))) 1 1 := by
  intro K
  induction K with
  | zero =>
    intro dat grid c _ Q Q'
    simp [Fw]
  | succ K ih =>
    intro dat grid c hc Q Q'
    have ih' := ih (fun a => dat a.castSucc) (fun a => grid a.castSucc) (fun a => c a.castSucc)
      (fun a => hc a.castSucc)
    beta_reduce at ih'
    have hl := hc (Fin.last K) Q Q'
    unfold letterVal at hl
    simp only [← mul_smul] at hl
    rw [sumsnoc_lemma_2]
    simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, List.ofFn_succ',
      List.concat_eq_append, Fw_concat]
    simp only [← mul_smul]
    rw [sumlin_lemma_3]
    simp only [← ih']
    calc (∏ a : Fin K, c a.castSucc) * c (Fin.last K) * Ξ (Q • X) (Q' • X') =
        (∏ a : Fin K, c a.castSucc) * (c (Fin.last K) * Ξ (Q • X) (Q' • X')) := by ring
      _ = _ := by
        rw [← hl, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring

theorem monic_extract {V : Type} [AddCommGroup V] [Module ℂ V] (ev : M →ₗ[ℂ] V) (n : ℕ) (A₀ : R[X])
    (hA : A₀.Monic) (hn : A₀.natDegree = n) (y : Fin (n + 1) → ℝ) (hy : Function.Injective y)
    (x : M) : ∑ i, ((lagCo y i : ℝ) : ℂ) • ev (evR A₀ (y i) • x) = ev x := by
  have hc1 : A₀.coeff n = 1 := by
    rw [← hn]
    exact hA.coeff_natDegree
  have h := lead_c n y hy (fun k : Fin (n + 1) => ev (A₀.coeff k • x))
  simp only [Fin.val_last, hc1, one_smul] at h
  rw [h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [evR_smul A₀ n hn.le (y i) x, map_sum, Finset.sum_range]
  simp only [map_smul]

end

end Formalism.FourierDecayAlt.P.WordMonicExtraction

namespace Formalism.FourierDecayAlt.P

open Finset Polynomial Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.WordMonicExtraction

theorem plane_wave_word_formula : Formalism.FourierDecayAlt.F7.PlaneWaveWord := by
  intro R M _ _ _ _ _ _ Ξ n K dat grid X X' hS hg
  have h := word_gen Ξ (2 * n) X X' K dat grid (fun a => (dat a).s)
    (fun a Q Q' => top_extract (planeLetter Ξ n (dat a) (Q • X) (Q' • X') (hS a).1 (hS a).2)
      (grid a) (hg a)) 1 1
  simpa only [one_smul] using h

theorem lift_word_formula : Formalism.FourierDecayAlt.F7.LiftWord := by
  unfold LiftWord
  intro R M _ _ _ _ _ _ Ξ n s K dat A₀ A₀v e t t' grid X X' hs1 hs0 he ht hA hA0 hB hBv hg
  have h := word_gen Ξ (2 * n + s) X X' K dat grid (fun a => e a * (1 / t a - 1 / t' a))
    (fun a Q Q' => top_extract (liftLetter Ξ n s (dat a) (A₀ a) (A₀v a) (e a) (t a) (t' a) (Q • X)
      (Q' • X') (hs0 a) (he a) (hA a).1 (hA a).2.1 (hA a).2.2.1 (hA a).2.2.2 (hA0 a).1 (hA0 a).2.1
      (hA0 a).2.2.1 (hA0 a).2.2.2
      (fun Y Y' => by
        have hh := hB a Y Q (evR (dat a).Av Y' * Q')
        rw [mul_smul (evR (dat a).Av Y') Q' X'] at hh
        exact hh)
      (fun Y Y' => by
        have hh := hBv a Y' (evR (dat a).A Y * Q) Q'
        rw [mul_smul (evR (dat a).A Y) Q X] at hh
        exact hh)) (grid a) (hg a)) 1 1
  simp only [one_smul] at h
  exact h

private theorem liftvec_lemma_4 {R M V : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M]
    [Module R M] [IsScalarTower ℂ R M] [AddCommGroup V] [Module ℂ V] (ev : M →ₗ[ℂ] V) (n : ℕ)
    (X₀ : M) :
    ∀ (K : ℕ) (G : Fin K → ℝ → R) (A₀ : Fin K → Polynomial R) (c : Fin K → ℂ)
      (grid : Fin K → Fin (n + 1) → ℝ),
      (∀ a, (A₀ a).Monic ∧ (A₀ a).natDegree = n) →
      (∀ a (Y : ℝ) (Q : R), ev (G a Y • Q • X₀) = c a • ev (evR (A₀ a) Y • Q • X₀)) →
      (∀ a, Function.Injective (grid a)) →
      ∀ Q : R, (∏ a, c a) • ev (Q • X₀) =
        ∑ j : Fin K → Fin (n + 1), ((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) •
          ev ((List.ofFn fun a => G a (grid a (j a))).prod • Q • X₀) := by
  intro K
  induction K with
  | zero =>
    intro G A₀ c grid _ _ _ Q
    simp
  | succ K ih =>
    intro G A₀ c grid hA hG hg Q
    have ih' := ih (fun a => G a.castSucc) (fun a => A₀ a.castSucc) (fun a => c a.castSucc)
      (fun a => grid a.castSucc) (fun a => hA a.castSucc) (fun a => hG a.castSucc)
      (fun a => hg a.castSucc)
    beta_reduce at ih'
    rw [sumsnoc_lemma_2]
    simp only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, List.ofFn_succ',
      List.concat_eq_append, List.prod_append, List.prod_singleton, mul_smul]
    have inner : ∀ jl : Fin (n + 1), ∑ j' : Fin K → Fin (n + 1),
        (((∏ a : Fin K, lagCo (grid a.castSucc) (j' a)) * lagCo (grid (Fin.last K)) jl : ℝ) : ℂ) •
          ev ((List.ofFn fun a : Fin K => G a.castSucc (grid a.castSucc (j' a))).prod •
            G (Fin.last K) (grid (Fin.last K) jl) • Q • X₀) =
        ((lagCo (grid (Fin.last K)) jl : ℝ) : ℂ) •
          ((∏ a : Fin K, c a.castSucc) • ev (G (Fin.last K) (grid (Fin.last K) jl) • Q • X₀)) := by
      intro jl
      have e := ih' (G (Fin.last K) (grid (Fin.last K) jl) * Q)
      simp only [mul_smul] at e
      rw [e, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun j' _ => ?_)
      rw [smul_smul ((lagCo (grid (Fin.last K)) jl : ℝ) : ℂ)]
      congr 1
      push_cast
      ring
    simp only [inner]
    have hm := monic_extract ev n (A₀ (Fin.last K)) (hA (Fin.last K)).1 (hA (Fin.last K)).2
      (grid (Fin.last K)) (hg (Fin.last K)) (Q • X₀)
    simp_rw [hG (Fin.last K)]
    rw [← hm, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [smul_smul]
    congr 1
    ring

theorem lift_vector_word : Formalism.FourierDecayAlt.F7.LiftVectorWord := by
  unfold LiftVectorWord
  intro R M V _ _ _ _ _ _ _ _ ev n K G A₀ c grid X₀ hA hG hg
  have h := liftvec_lemma_4 ev n X₀ K G A₀ c grid hA hG hg 1
  simp only [one_smul] at h
  exact h

end Formalism.FourierDecayAlt.P
