import Mathlib
import Formalism.DropLevelBounds.Statement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LeWeightOfCoeffPow
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds
open scoped BigOperators

noncomputable section

namespace GlobalTheory.DiagBlock

lemma embV_inj {n0 n : ℕ} (hn : n0 ≤ n) : Function.Injective (embV hn) :=
  ((Fin.castLE_injective hn).prodMap (Fin.castLE_injective hn)).sumMap
    ((Fin.castLE_injective hn).prodMap (Fin.castLE_injective hn))

lemma restr_eq {C : Type} [Field C] {n0 n : ℕ} (hn : n0 ≤ n) (G : MvPowerSeries (PVar n) C) :
    restr hn G = MvPowerSeries.killCompl ⟨embV hn, embV_inj hn⟩ G := by
  ext m
  rw [MvPowerSeries.coeff_killCompl, Finsupp.embDomain_eq_mapDomain]
  rfl

theorem restrictMul : RestrictMul := by
  intro C _ n0 n hn G G'
  rw [restr_eq, restr_eq, restr_eq, map_mul]

private lemma coeff_mvExp' {C : Type} [Field C] {σ : Type} (h : MvPowerSeries σ C)
    (m : σ →₀ ℕ) : MvPowerSeries.coeff m (mvExp h) =
      ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (h ^ k) / (k.factorial : C) := rfl

theorem restrictExp : RestrictExp := by
  intro C _ _ n0 n hn h
  ext m
  rw [restr_eq, restr_eq, MvPowerSeries.coeff_killCompl, coeff_mvExp', coeff_mvExp']
  have hdeg : (Finsupp.embDomain ⟨embV hn, embV_inj hn⟩ m).degree = m.degree := by
    rw [Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain]
  rw [hdeg]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_pow, MvPowerSeries.coeff_killCompl]

section Kill

variable {R : Type} [CommRing R] {σ : Type}

def kill (S : σ → Prop) [DecidablePred S] : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval fun x => if S x then 0 else MvPolynomial.X x

lemma kill_X (S : σ → Prop) [DecidablePred S] (x : σ) :
    kill (R := R) S (MvPolynomial.X x) = if S x then 0 else MvPolynomial.X x := by
  rw [kill, MvPolynomial.aeval_X]

open Classical in
lemma kill_monomial (S : σ → Prop) [DecidablePred S] (m : σ →₀ ℕ) (c : R) :
    kill S (MvPolynomial.monomial m c) =
      if ∀ x, S x → m x = 0 then MvPolynomial.monomial m c else 0 := by
  rw [kill, MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  split_ifs with h
  · rw [MvPolynomial.monomial_eq]
    congr 1
    refine Finsupp.prod_congr fun x hx => ?_
    rw [if_neg]
    intro hS
    exact (Finsupp.mem_support_iff.1 hx) (h x hS)
  · push Not at h
    obtain ⟨x, hS, hx⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hx), mul_zero]
    rw [if_pos hS, zero_pow hx]

open Classical in
lemma coeff_kill (S : σ → Prop) [DecidablePred S] (P : MvPolynomial σ R) (e : σ →₀ ℕ) :
    MvPolynomial.coeff e (kill S P) =
      if ∀ x, S x → e x = 0 then MvPolynomial.coeff e P else 0 := by
  refine MvPolynomial.induction_on' P (fun m c => ?_) (fun p q hp hq => ?_)
  · rw [kill_monomial]
    by_cases hme : m = e
    · subst hme
      split_ifs <;> simp
    · split_ifs <;> simp [MvPolynomial.coeff_monomial, hme]
  · rw [map_add, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add]
    split_ifs <;> simp

end Kill

lemma det_diag_rows {A : Type} [CommRing A] {n0 n : ℕ} (hn : n0 ≤ n) (M : Matrix (Fin n) (Fin n) A)
    (hM : ∀ ρ c : Fin n, n0 ≤ ρ.val → c ≠ ρ → M ρ c = 0) :
    M.det = (M.submatrix (Fin.castLE hn) (Fin.castLE hn)).det *
      ∏ ρ ∈ (Finset.univ : Finset (Fin n)).filter (fun ρ => n0 ≤ ρ.val), M ρ ρ := by
  classical
  have hblock := Matrix.twoBlockTriangular_det M (fun i : Fin n => i.val < n0) (by
    intro i hi j hj
    refine hM i j (not_lt.1 hi) ?_
    rintro rfl
    exact hi hj)
  rw [hblock]
  congr 1
  · let e : Fin n0 ≃ {i : Fin n // i.val < n0} :=
      { toFun := fun b => ⟨Fin.castLE hn b, b.isLt⟩
        invFun := fun i => ⟨i.1.val, i.2⟩
        left_inv := fun b => rfl
        right_inv := fun i => rfl }
    rw [← Matrix.det_submatrix_equiv_self e]
    rfl
  · have hdiag : (Matrix.toSquareBlockProp M fun i : Fin n => ¬ i.val < n0) =
        Matrix.diagonal fun i : {i : Fin n // ¬ i.val < n0} => M i i := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.toSquareBlockProp, Matrix.toBlock]
      · rw [Matrix.diagonal_apply_ne _ hij]
        exact hM i j (not_lt.1 i.2) (fun h => hij (Subtype.ext h.symm))
    rw [hdiag, Matrix.det_diagonal]
    exact (Finset.prod_subtype _ (fun ρ => by simp) (fun ρ => M ρ ρ)).symm

lemma kill_det_pow {R : Type} [CommRing R] {σ : Type} (S : σ → Prop) [DecidablePred S]
    {n0 n : ℕ} (hn : n0 ≤ n) (f : Fin n → Fin n → σ)
    (hf : ∀ ρ c, S (f ρ c) ↔ n0 ≤ ρ.val ∧ c ≠ ρ) (Y : ℕ) :
    kill S ((Matrix.of fun b c : Fin n => (MvPolynomial.X (f b c) : MvPolynomial σ R)).det ^ Y) =
      (Matrix.of fun b c : Fin n0 =>
        (MvPolynomial.X (f (Fin.castLE hn b) (Fin.castLE hn c)) : MvPolynomial σ R)).det ^ Y *
      MvPolynomial.monomial
        (∑ ρ ∈ (Finset.univ : Finset (Fin n)).filter (fun ρ => n0 ≤ ρ.val),
          Finsupp.single (f ρ ρ) Y) 1 := by
  rw [map_pow, AlgHom.map_det]
  have hM : (kill (R := R) S).mapMatrix (Matrix.of fun b c : Fin n => (MvPolynomial.X (f b c) : MvPolynomial σ R)) =
      Matrix.of fun b c : Fin n => if S (f b c) then 0 else MvPolynomial.X (f b c) := by
    ext b c
    simp [AlgHom.mapMatrix_apply, kill_X]
  rw [hM, det_diag_rows hn _ (by
    intro ρ c hρ hc
    simp [(hf ρ c).2 ⟨hρ, hc⟩])]
  have hsub : (Matrix.of fun b c : Fin n => if S (f b c) then (0 : MvPolynomial σ R) else MvPolynomial.X (f b c)).submatrix
      (Fin.castLE hn) (Fin.castLE hn) =
      Matrix.of fun b c : Fin n0 => (MvPolynomial.X (f (Fin.castLE hn b) (Fin.castLE hn c)) : MvPolynomial σ R) := by
    ext b c
    simp [hf, not_le.2 b.isLt]
  have hdiag : ∀ ρ : Fin n, (Matrix.of fun b c : Fin n =>
      if S (f b c) then (0 : MvPolynomial σ R) else MvPolynomial.X (f b c)) ρ ρ = MvPolynomial.X (f ρ ρ) := by
    intro ρ
    simp [hf]
  rw [hsub, Finset.prod_congr rfl (fun ρ _ => hdiag ρ), mul_pow, ← Finset.prod_pow,
    MvPolynomial.monomial_sum_one]
  congr 1
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [MvPolynomial.X_pow_eq_monomial]

private lemma diag_single_sum_apply (n0 n Y : ℕ) (ρ c : Fin n) :
    (∑ ρ' ∈ (Finset.univ : Finset (Fin n)).filter (fun ρ' => n0 ≤ ρ'.val), Finsupp.single (ρ', ρ') Y) (ρ, c) =
      if n0 ≤ ρ.val ∧ c = ρ then Y else 0 := by
  rw [Finsupp.finsetSum_apply]
  by_cases hρ : n0 ≤ ρ.val
  · rw [Finset.sum_eq_single ρ]
    · by_cases hc : c = ρ
      · subst hc; simp [hρ]
      · simp [hc]
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ ρ, hρ⟩) h
  · rw [if_neg (fun h => hρ h.1)]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hb' : b ≠ ρ := fun h => hρ (h ▸ (Finset.mem_filter.1 hb).2)
    simp [hb']

theorem detPowDiag : DetPowDiag := by
  intro R _ n0 n hn Y e he
  classical
  have hS : ∀ x : Fin n × Fin n, (n0 ≤ x.1.val ∧ x.2 ≠ x.1) → e x = 0 := by
    rintro ⟨ρ, c⟩ ⟨h1, h2⟩
    rw [he ρ c h1, if_neg h2]
  have hk := coeff_kill (R := R) (fun x : Fin n × Fin n => n0 ≤ x.1.val ∧ x.2 ≠ x.1)
    ((Matrix.of fun b c : Fin n => (MvPolynomial.X (b, c) : MvPolynomial (Fin n × Fin n) R)).det ^ Y) e
  rw [if_pos hS] at hk
  rw [← hk, kill_det_pow _ hn (fun b c => (b, c)) (fun ρ c => Iff.rfl) Y]
  have hsplit : e = e.filter (fun x => x.1.val < n0) +
      ∑ ρ ∈ (Finset.univ : Finset (Fin n)).filter (fun ρ => n0 ≤ ρ.val), Finsupp.single (ρ, ρ) Y := by
    ext ⟨ρ, c⟩
    rw [Finsupp.add_apply, Finsupp.filter_apply, diag_single_sum_apply]
    by_cases hρ : n0 ≤ ρ.val
    · simp [hρ, he ρ c hρ, not_lt.2 hρ]
    · simp [hρ, not_le.1 hρ]
  conv_lhs => rw [hsplit]
  rw [MvPolynomial.coeff_mul_monomial, mul_one]

lemma coeff_mul_split {C : Type} [Field C] {σ : Type} (p : σ → Prop)
    (G H : MvPowerSeries σ C)
    (hG : ∀ m, MvPowerSeries.coeff m G ≠ 0 → ∀ x ∈ m.support, p x)
    (hH : ∀ m, MvPowerSeries.coeff m H ≠ 0 → ∀ x ∈ m.support, ¬ p x)
    (a b : σ →₀ ℕ) (ha : ∀ x ∈ a.support, p x) (hb : ∀ x ∈ b.support, ¬ p x) :
    MvPowerSeries.coeff (a + b) (G * H) = MvPowerSeries.coeff a G * MvPowerSeries.coeff b H := by
  classical
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (a, b)]
  · rintro ⟨u, v⟩ huv hne
    have huv' := Finset.HasAntidiagonal.mem_antidiagonal.1 huv
    simp only at huv'
    by_contra hprod
    have hu := hG u (left_ne_zero_of_mul hprod)
    have hv := hH v (right_ne_zero_of_mul hprod)
    apply hne
    have key : ∀ x, u x = a x ∧ v x = b x := by
      intro x
      have hx := congrArg (fun f => f x) huv'
      simp only [Finsupp.add_apply] at hx
      by_cases hpx : p x
      · have h1 : v x = 0 := by
          by_contra h0; exact hv x (Finsupp.mem_support_iff.2 h0) hpx
        have h2 : b x = 0 := by
          by_contra h0; exact hb x (Finsupp.mem_support_iff.2 h0) hpx
        omega
      · have h1 : u x = 0 := by
          by_contra h0; exact hpx (hu x (Finsupp.mem_support_iff.2 h0))
        have h2 : a x = 0 := by
          by_contra h0; exact hpx (ha x (Finsupp.mem_support_iff.2 h0))
        omega
    exact Prod.ext (Finsupp.ext fun x => (key x).1) (Finsupp.ext fun x => (key x).2)
  · intro h
    exact (h (by simp)).elim

lemma det_homog {C : Type} [Field C] {σ : Type} {n : ℕ} (w : σ → ℕ) (f : Fin n → Fin n → σ)
    (r : Fin n → ℕ) (h : ∀ b c, w (f b c) = r b) :
    (Matrix.of fun b c : Fin n =>
      (MvPolynomial.X (f b c) : MvPolynomial σ C)).det.IsWeightedHomogeneous w (∑ b, r b) := by
  rw [Matrix.det_apply, ← MvPolynomial.mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun τ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem ?_ _
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
  have hprod := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun i => (Matrix.of fun b c : Fin n => (MvPolynomial.X (f b c) : MvPolynomial σ C)) (τ i) i)
    (fun i => r (τ i)) (w := w) (fun i _ => by
      simpa [Matrix.of_apply, h] using MvPolynomial.isWeightedHomogeneous_X C w (f (τ i) i))
  rwa [Equiv.sum_comp τ r] at hprod

lemma rowDeg_of_mem {C : Type} [Field C] {n : ℕ} (a b : ℕ) (m : PVar n →₀ ℕ)
    (hm : MvPolynomial.coeff m (detL C n ^ a * detR C n ^ b) ≠ 0) (ρ : Fin n) :
    rowDegZ m ρ = a ∧ rowDegZ' m ρ = b := by
  classical
  let wL : PVar n → ℕ := Sum.elim (fun p => if p.1 = ρ then 1 else 0) (fun _ => 0)
  let wR : PVar n → ℕ := Sum.elim (fun _ => 0) (fun p => if p.1 = ρ then 1 else 0)
  have hLL : (detL C n).IsWeightedHomogeneous wL 1 := by
    have := det_homog (C := C) wL (fun b c => Sum.inl (b, c)) (fun b => if b = ρ then 1 else 0)
      (fun b c => rfl)
    simpa [detL] using this
  have hRL : (detR C n).IsWeightedHomogeneous wL 0 := by
    have := det_homog (C := C) wL (fun b c => Sum.inr (b, c)) (fun _ => 0) (fun b c => rfl)
    simpa [detR] using this
  have hLR : (detL C n).IsWeightedHomogeneous wR 0 := by
    have := det_homog (C := C) wR (fun b c => Sum.inl (b, c)) (fun _ => 0) (fun b c => rfl)
    simpa [detL] using this
  have hRR : (detR C n).IsWeightedHomogeneous wR 1 := by
    have := det_homog (C := C) wR (fun b c => Sum.inr (b, c)) (fun b => if b = ρ then 1 else 0)
      (fun b c => rfl)
    simpa [detR] using this
  have h1 := ((hLL.pow a).mul (hRL.pow b)) hm
  have h2 := ((hLR.pow a).mul (hRR.pow b)) hm
  have hwL : Finsupp.weight wL m = rowDegZ m ρ := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp [rowDegZ, Fintype.sum_sum_type, Fintype.sum_prod_type, wL]
    rw [Finset.sum_eq_single ρ (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ ρ) h)]
    simp
  have hwR : Finsupp.weight wR m = rowDegZ' m ρ := by
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp [rowDegZ', Fintype.sum_sum_type, Fintype.sum_prod_type, wR]
    rw [Finset.sum_eq_single ρ (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ ρ) h)]
    simp
  rw [hwL] at h1
  rw [hwR] at h2
  simp at h1 h2
  exact ⟨h1, h2⟩

lemma diagMon_inl (n0 n L y : ℕ) (ρ c : Fin n) :
    diagMon n0 n L y (Sum.inl (ρ, c)) = if n0 ≤ ρ.val ∧ c = ρ then L * y else 0 := by
  rw [diagMon, Finsupp.finsetSum_apply]
  by_cases hρ : n0 ≤ ρ.val
  · rw [Finset.sum_eq_single ρ]
    · by_cases hc : c = ρ
      · subst hc; simp [hρ]
      · simp [hc]
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ ρ, hρ⟩) h
  · rw [if_neg (fun h => hρ h.1)]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hb' : b ≠ ρ := fun h => hρ (h ▸ (Finset.mem_filter.1 hb).2)
    simp [hb']

lemma diagMon_inr (n0 n L y : ℕ) (ρ c : Fin n) :
    diagMon n0 n L y (Sum.inr (ρ, c)) = if n0 ≤ ρ.val ∧ c = ρ then y else 0 := by
  rw [diagMon, Finsupp.finsetSum_apply]
  by_cases hρ : n0 ≤ ρ.val
  · rw [Finset.sum_eq_single ρ]
    · by_cases hc : c = ρ
      · subst hc; simp [hρ]
      · simp [hc]
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ ρ, hρ⟩) h
  · rw [if_neg (fun h => hρ h.1)]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hb' : b ≠ ρ := fun h => hρ (h ▸ (Finset.mem_filter.1 hb).2)
    simp [hb']

lemma diagMon_row {n0 n L y : ℕ} (x : PVar n) (hx : x ∈ (diagMon n0 n L y).support) :
    n0 ≤ (rowOf x).val := by
  rw [Finsupp.mem_support_iff] at hx
  rcases x with ⟨ρ, c⟩ | ⟨ρ, c⟩
  · rw [diagMon_inl] at hx
    split_ifs at hx with h
    · exact h.1
    · exact absurd rfl hx
  · rw [diagMon_inr] at hx
    split_ifs at hx with h
    · exact h.1
    · exact absurd rfl hx

lemma mfact_diagMon {n0 n : ℕ} (L y : ℕ) :
    mfact (diagMon n0 n L y) = ((L * y).factorial * y.factorial) ^ (n - n0) := by
  classical
  have hcard : ((Finset.univ : Finset (Fin n)).filter fun ρ => n0 ≤ ρ.val).card = n - n0 := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun ρ : Fin n => ρ.val < n0)
    rw [Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin] at h1
    simp only [not_lt] at h1
    omega
  have key : ∀ t : ℕ, ∏ ρ : Fin n, ∏ c : Fin n, (if n0 ≤ ρ.val ∧ c = ρ then t else 0).factorial =
      t.factorial ^ (n - n0) := by
    intro t
    have hrow : ∀ ρ : Fin n, ∏ c : Fin n, (if n0 ≤ ρ.val ∧ c = ρ then t else 0).factorial =
        if n0 ≤ ρ.val then t.factorial else 1 := by
      intro ρ
      by_cases hρ : n0 ≤ ρ.val
      · rw [if_pos hρ, Finset.prod_eq_single ρ]
        · simp [hρ]
        · intro c _ hc
          simp [hc]
        · intro h
          exact absurd (Finset.mem_univ ρ) h
      · simp [hρ]
    rw [Finset.prod_congr rfl (fun ρ _ => hrow ρ), ← Finset.prod_filter, Finset.prod_const, hcard]
  rw [mfact, Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero), Fintype.prod_sum_type,
    Fintype.prod_prod_type, Fintype.prod_prod_type]
  simp only [diagMon_inl, diagMon_inr]
  rw [key, key, mul_pow]

lemma rowDeg_filter_le {n : ℕ} (p : PVar n → Prop) [DecidablePred p] (m : PVar n →₀ ℕ) (ρ : Fin n) :
    rowDegZ (m.filter p) ρ ≤ rowDegZ m ρ ∧ rowDegZ' (m.filter p) ρ ≤ rowDegZ' m ρ := by
  constructor <;>
  · refine Finset.sum_le_sum fun c _ => ?_
    rw [Finsupp.filter_apply]
    split_ifs <;> simp

private lemma kill_detL_pow_mul_detR_pow {C : Type} [Field C] {n0 n : ℕ} (hn : n0 ≤ n) (L y : ℕ)
    (S : PVar n → Prop) [DecidablePred S]
    (hS1 : ∀ ρ c : Fin n, S (Sum.inl (ρ, c)) ↔ n0 ≤ ρ.val ∧ c ≠ ρ)
    (hS2 : ∀ ρ c : Fin n, S (Sum.inr (ρ, c)) ↔ n0 ≤ ρ.val ∧ c ≠ ρ) :
    kill S (detL C n ^ (L * y) * detR C n ^ y) =
      MvPolynomial.rename (embV hn) (detL C n0 ^ (L * y) * detR C n0 ^ y) *
        MvPolynomial.monomial (diagMon n0 n L y) 1 := by
  rw [show detL C n = (Matrix.of fun b c : Fin n =>
      (MvPolynomial.X (Sum.inl (b, c)) : MvPolynomial (PVar n) C)).det from rfl,
    show detR C n = (Matrix.of fun b c : Fin n =>
      (MvPolynomial.X (Sum.inr (b, c)) : MvPolynomial (PVar n) C)).det from rfl,
    show detL C n0 = (Matrix.of fun b c : Fin n0 =>
      (MvPolynomial.X (Sum.inl (b, c)) : MvPolynomial (PVar n0) C)).det from rfl,
    show detR C n0 = (Matrix.of fun b c : Fin n0 =>
      (MvPolynomial.X (Sum.inr (b, c)) : MvPolynomial (PVar n0) C)).det from rfl]
  rw [map_mul, kill_det_pow S hn (fun b c => Sum.inl (b, c)) hS1,
    kill_det_pow S hn (fun b c => Sum.inr (b, c)) hS2, map_mul, map_pow, map_pow,
    AlgHom.map_det, AlgHom.map_det]
  have e1 : (MvPolynomial.rename (R := C) (embV hn)).mapMatrix (Matrix.of fun b c : Fin n0 =>
      (MvPolynomial.X (Sum.inl (b, c)) : MvPolynomial (PVar n0) C)) =
      Matrix.of fun b c : Fin n0 => MvPolynomial.X (Sum.inl (Fin.castLE hn b, Fin.castLE hn c)) := by
    ext b c
    simp [AlgHom.mapMatrix_apply, embV]
  have e2 : (MvPolynomial.rename (R := C) (embV hn)).mapMatrix (Matrix.of fun b c : Fin n0 =>
      (MvPolynomial.X (Sum.inr (b, c)) : MvPolynomial (PVar n0) C)) =
      Matrix.of fun b c : Fin n0 => MvPolynomial.X (Sum.inr (Fin.castLE hn b, Fin.castLE hn c)) := by
    ext b c
    simp [AlgHom.mapMatrix_apply, embV]
  have hmon : ∀ a b : PVar n →₀ ℕ, MvPolynomial.monomial (a + b) (1 : C) =
      MvPolynomial.monomial a 1 * MvPolynomial.monomial b 1 := fun a b => by
    rw [MvPolynomial.monomial_mul, one_mul]
  rw [e1, e2, diagMon, Finset.sum_add_distrib, hmon]
  ring

private lemma filter_nondiag_eq_diagMon_of_coeff_ne_zero {C : Type} [Field C] {n0 n : ℕ} (L y : ℕ) (G1 H : MvPowerSeries (PVar n) C)
    (hG1 : ∀ m : PVar n →₀ ℕ, MvPowerSeries.coeff m G1 ≠ 0 → ∀ x ∈ m.support, (rowOf x).val < n0)
    (hH : ∀ m : PVar n →₀ ℕ, MvPowerSeries.coeff m H ≠ 0 → ∀ x ∈ m.support, n0 ≤ (rowOf x).val)
    (hHd : ∀ m : PVar n →₀ ℕ, (∀ x ∈ m.support, n0 ≤ (rowOf x).val) →
      (∀ ρ : Fin n, n0 ≤ ρ.val → rowDegZ m ρ ≤ L * y ∧ rowDegZ' m ρ ≤ y) →
      MvPowerSeries.coeff m H = if m = diagMon n0 n L y then 1 else 0)
    (m : PVar n →₀ ℕ) (hm : MvPolynomial.coeff m (detL C n ^ (L * y) * detR C n ^ y) ≠ 0)
    (hmG : MvPowerSeries.coeff m (G1 * H) ≠ 0) :
    m.filter (fun x => ¬ (rowOf x).val < n0) = diagMon n0 n L y := by
  classical
  have hab := Finsupp.filter_add_filter_not m (fun x => (rowOf x).val < n0)
  have hsplit := coeff_mul_split (fun x => (rowOf x).val < n0) G1 H hG1
    (fun m' hm' x hx => not_lt.2 (hH m' hm' x hx))
    (m.filter fun x => (rowOf x).val < n0) (m.filter fun x => ¬ (rowOf x).val < n0)
    (fun x hx => by
      rw [Finsupp.support_filter, Finset.mem_filter] at hx
      exact hx.2)
    (fun x hx => by
      rw [Finsupp.support_filter, Finset.mem_filter] at hx
      exact hx.2)
  rw [hab] at hsplit
  rw [hsplit] at hmG
  have hb := right_ne_zero_of_mul hmG
  have hrow := rowDeg_of_mem (L * y) y m hm
  rw [hHd _ (fun x hx => by
      rw [Finsupp.support_filter, Finset.mem_filter] at hx
      exact not_lt.1 hx.2)
    (fun ρ _ => ⟨(rowDeg_filter_le _ m ρ).1.trans (hrow ρ).1.le,
      (rowDeg_filter_le _ m ρ).2.trans (hrow ρ).2.le⟩)] at hb
  split_ifs at hb with hbeq
  · exact hbeq
  · exact absurd rfl hb

theorem blockJet : BlockJet := by
  intro C _ _ n0 n hn L y G1 H hG1 hH hHd
  classical
  have hkill := kill_detL_pow_mul_detR_pow (C := C) hn L y
    (fun x : PVar n => n0 ≤ (rowOf x).val ∧ Sum.elim Prod.snd Prod.snd x ≠ rowOf x)
    (fun ρ c => Iff.rfl) (fun ρ c => Iff.rfl)
  have havoid : ∀ m : PVar n →₀ ℕ, MvPolynomial.coeff m (detL C n ^ (L * y) * detR C n ^ y) ≠ 0 →
      MvPowerSeries.coeff m (G1 * H) ≠ 0 →
      ∀ x, (n0 ≤ (rowOf x).val ∧ Sum.elim Prod.snd Prod.snd x ≠ rowOf x) → m x = 0 := by
    intro m hm hmG x hx
    have hb := filter_nondiag_eq_diagMon_of_coeff_ne_zero L y G1 H hG1 hH hHd m hm hmG
    have hmx : m x = (m.filter fun x => ¬ (rowOf x).val < n0) x := by
      rw [Finsupp.filter_apply, if_pos (not_lt.2 hx.1)]
    rw [hmx, hb]
    rcases x with ⟨ρ, c⟩ | ⟨ρ, c⟩
    · rw [diagMon_inl, if_neg]
      rintro ⟨-, rfl⟩
      exact hx.2 rfl
    · rw [diagMon_inr, if_neg]
      rintro ⟨-, rfl⟩
      exact hx.2 rfl
  have h3 : jetAt0 (detL C n ^ (L * y) * detR C n ^ y) (G1 * H) =
      jetAt0 (kill (fun x : PVar n => n0 ≤ (rowOf x).val ∧ Sum.elim Prod.snd Prod.snd x ≠ rowOf x)
        (detL C n ^ (L * y) * detR C n ^ y)) (G1 * H) := by
    rw [GlobalTheory.UnitCase.jetAt0_eq_sum (kill (fun x : PVar n => n0 ≤ (rowOf x).val ∧
      Sum.elim Prod.snd Prod.snd x ≠ rowOf x) (detL C n ^ (L * y) * detR C n ^ y)) (G1 * H)
      (detL C n ^ (L * y) * detR C n ^ y).support ?_, jetAt0]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [coeff_kill]
      split_ifs with h
      · rfl
      · by_cases h0 : MvPowerSeries.coeff m (G1 * H) = 0
        · simp [h0]
        · by_cases h1 : MvPolynomial.coeff m (detL C n ^ (L * y) * detR C n ^ y) = 0
          · simp [h1]
          · exact absurd (havoid m h1 h0) h
    · intro m hm
      rw [MvPolynomial.mem_support_iff, coeff_kill] at hm
      rw [MvPolynomial.mem_support_iff]
      split_ifs at hm
      · exact hm
      · exact absurd rfl hm
  rw [h3, hkill]
  have hsupp : (MvPolynomial.rename (embV hn) (detL C n0 ^ (L * y) * detR C n0 ^ y) *
      MvPolynomial.monomial (diagMon n0 n L y) (1 : C)).support ⊆
      (detL C n0 ^ (L * y) * detR C n0 ^ y).support.image
        (fun u => u.mapDomain (embV hn) + diagMon n0 n L y) := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul_monomial'] at hm
    split_ifs at hm with hle
    · rw [mul_one] at hm
      have hm' : m - diagMon n0 n L y ∈
          (MvPolynomial.rename (embV hn) (detL C n0 ^ (L * y) * detR C n0 ^ y)).support :=
        MvPolynomial.mem_support_iff.2 hm
      rw [MvPolynomial.support_rename_of_injective (embV_inj hn), Finset.mem_image] at hm'
      obtain ⟨u, hu, hue⟩ := hm'
      exact Finset.mem_image.2 ⟨u, hu, by rw [hue, tsub_add_cancel_of_le hle]⟩
    · exact absurd rfl hm
  rw [GlobalTheory.UnitCase.jetAt0_eq_sum _ _ _ hsupp,
    Finset.sum_image (fun u _ v _ h => Finsupp.mapDomain_injective (embV_inj hn) (add_right_cancel h)),
    jetAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [MvPolynomial.coeff_mul_monomial, mul_one, MvPolynomial.coeff_rename_mapDomain _ (embV_inj hn)]
  have hU : ∀ x ∈ (u.mapDomain (embV hn)).support, (rowOf x).val < n0 := by
    intro x hx
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
    rcases v with ⟨b, c⟩ | ⟨b, c⟩
    · exact b.isLt
    · exact b.isLt
  have hDrow : ∀ x ∈ (diagMon n0 n L y).support, ¬ (rowOf x).val < n0 :=
    fun x hx => not_lt.2 (diagMon_row x hx)
  rw [coeff_mul_split (fun x => (rowOf x).val < n0) G1 H hG1
    (fun m hm x hx => not_lt.2 (hH m hm x hx)) _ _ hU hDrow]
  have hHD : MvPowerSeries.coeff (diagMon n0 n L y) H = 1 := by
    rw [hHd _ (fun x hx => diagMon_row x hx) (fun ρ hρ => ⟨by simp [rowDegZ, diagMon_inl, hρ],
      by simp [rowDegZ', diagMon_inr, hρ]⟩), if_pos rfl]
  have hdisj : Disjoint (u.mapDomain (embV hn)).support (diagMon n0 n L y).support :=
    Finset.disjoint_left.2 fun x hx1 hx2 => hDrow x hx2 (hU x hx1)
  have hmf : mfact (u.mapDomain (embV hn) + diagMon n0 n L y) =
      mfact u * ((L * y).factorial * y.factorial) ^ (n - n0) := by
    rw [← mfact_diagMon, mfact, mfact, mfact, Finsupp.prod_add_index_of_disjoint hdisj,
      Finsupp.prod_mapDomain_index_inj (embV_inj hn)]
  have hr : MvPowerSeries.coeff u (restr hn G1) = MvPowerSeries.coeff (u.mapDomain (embV hn)) G1 := rfl
  rw [hHD, mul_one, hmf, hr]
  push_cast
  ring

theorem main : DetPowDiag ∧ BlockJet ∧ RestrictMul ∧ RestrictExp := ⟨detPowDiag, blockJet, restrictMul, restrictExp⟩

end GlobalTheory.DiagBlock
