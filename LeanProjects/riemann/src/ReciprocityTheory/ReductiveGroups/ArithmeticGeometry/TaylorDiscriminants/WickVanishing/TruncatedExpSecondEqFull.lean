import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SecondColumnOperator
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GaugeExp

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

open SecondColumnDegree DegreeTruncationOperator

section abelian₂

variable {k : Type} [CommRing k] {σ : Type}

def lam (W : (σ →₀ ℕ) → k) (R : MvPolynomial σ k) : k := ∑ m ∈ R.support, R.coeff m * W m

theorem lam_eq (W : (σ →₀ ℕ) → k) (R : MvPolynomial σ k) (S : Finset (σ →₀ ℕ)) (hS : R.support ⊆ S) :
    lam W R = ∑ m ∈ S, R.coeff m * W m := by
  classical
  unfold lam
  refine Finset.sum_subset hS fun e _ he => ?_
  rw [MvPolynomial.mem_support_iff, not_not] at he
  rw [he, zero_mul]

def lamL (W : (σ →₀ ℕ) → k) : MvPolynomial σ k →ₗ[k] k where
  toFun := lam W
  map_add' P Q := by
    classical
    rw [lam_eq W (P + Q) (P.support ∪ Q.support) support_add,
      lam_eq W P (P.support ∪ Q.support) subset_union_left,
      lam_eq W Q (P.support ∪ Q.support) subset_union_right, ← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [coeff_add, add_mul]
  map_smul' r P := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [lam_eq W (r • P) P.support support_smul, lam, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [coeff_smul, smul_eq_mul, mul_assoc]

theorem lamL_apply (W : (σ →₀ ℕ) → k) (R : MvPolynomial σ k) : lamL W R = lam W R := rfl

theorem lam_monomial (W : (σ →₀ ℕ) → k) (m : σ →₀ ℕ) (r : k) : lam W (monomial m r) = r * W m := by
  classical
  rw [lam_eq W _ {m} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

end abelian₂

theorem nabVal_eq_lam {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] (k : Type)
    [CommRing k] [Algebra ℚ k] [Algebra R k] [Nontrivial k] (B : FB R d O) (h : PS k 2 d) (w0 : O) (m : ℕ)
    (f : PS k 1 d) {ι : Type} [Fintype ι] (u : ι → Fin d → k) (Q : MvPolynomial ι k) :
    B.nabVal k h w0 m f u Q = lam (fun e => B.nabVal k h w0 m f u (monomial e 1)) Q := by
  classical
  unfold FB.nabVal lam
  simp only [DpolyOf, map_sum, map_mul, MvPowerSeries.constantCoeff_C]
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 1
  simp [MvPolynomial.support_monomial, MvPolynomial.coeff_monomial]

section Glue

variable {k : Type} [CommRing k] {ι : Type} [Fintype ι] {n : ℕ}

def glue (g : Fin n → (ι →₀ ℕ)) : (ι × Fin n) →₀ ℕ := ∑ b, Finsupp.mapDomain (fun l => (l, b)) (g b)

theorem glue_apply (g : Fin n → (ι →₀ ℕ)) (l : ι) (b : Fin n) : glue g (l, b) = g b l := by
  classical
  unfold glue
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single b]
  · exact Finsupp.mapDomain_apply (fun x y h => congrArg Prod.fst h) _ _
  · intro b' _ hb
    apply Finsupp.mapDomain_notin_range
    rintro ⟨x, hx⟩
    exact hb (congrArg Prod.snd hx)
  · intro h
    exact absurd (Finset.mem_univ b) h

theorem colM_glue (g : Fin n → (ι →₀ ℕ)) (b : Fin n) : colM (glue g) b = g b := by
  ext l
  first
  | simp [colM, glue_apply]
  | exact glue_apply g l b

theorem glue_colM (mo : (ι × Fin n) →₀ ℕ) : glue (fun b => colM mo b) = mo := by
  ext ⟨l, b⟩
  rw [glue_apply]
  first
  | simp [colM]
  | rfl

theorem prodQ_monomial (g : Fin n → (ι →₀ ℕ)) :
    prodQ (fun b => (monomial (g b) (1 : k) : MvPolynomial ι k)) = monomial (glue g) 1 := by
  unfold prodQ glue
  rw [MvPolynomial.monomial_sum_one]
  refine Finset.prod_congr rfl fun b _ => ?_
  exact MvPolynomial.rename_monomial _ _ _

theorem lam_prodQ (V : Fin n → (ι →₀ ℕ) → k) (Q : Fin n → MvPolynomial ι k) :
    lam (fun mo => ∏ b, V b (colM mo b)) (prodQ Q) = ∏ b, lam (V b) (Q b) := by
  classical
  have hP : prodQ Q = ∑ g ∈ Fintype.piFinset (fun b => (Q b).support),
      (monomial (glue g) (∏ b, (Q b).coeff (g b)) : MvPolynomial (ι × Fin n) k) := by
    have h1 : ∀ b, colE b (Q b) = ∑ e ∈ (Q b).support,
        (monomial (Finsupp.mapDomain (fun l => (l, b)) e) ((Q b).coeff e) : MvPolynomial (ι × Fin n) k) := by
      intro b
      conv_lhs => rw [(Q b).as_sum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      exact MvPolynomial.rename_monomial _ _ _
    unfold prodQ
    simp_rw [h1]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [glue, MvPolynomial.monomial_sum_index, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [MvPolynomial.C_mul_monomial, mul_one]
  rw [hP, ← lamL_apply, map_sum]
  simp only [lamL_apply, lam_monomial, colM_glue]
  simp only [lam]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.prod_mul_distrib]

end Glue

section Trunc

variable {k : Type} [CommRing k] [Algebra ℚ k]

private lemma totalDegree_pderiv_le_of_le_succ {σ : Type} (l : σ) (q : MvPolynomial σ k) (D : ℕ)
    (hq : q.totalDegree ≤ D + 1) : (pderiv l q).totalDegree ≤ D := by
  classical
  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [MvPolynomial.pderiv_monomial]
  by_cases hsl : s l = 0
  · rw [hsl, Nat.cast_zero, mul_zero, MvPolynomial.monomial_zero, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _
  · refine le_trans (b := (s - Finsupp.single l 1).sum fun _ e => e) ?_ ?_
    · first
      | exact MvPolynomial.totalDegree_monomial_le _ _
      | (by_cases hc : coeff s q * (s l : k) = 0
         · rw [hc, MvPolynomial.monomial_zero, MvPolynomial.totalDegree_zero]
           exact Nat.zero_le _
         · rw [MvPolynomial.totalDegree_monomial _ hc])
    · have hs' : (s.sum fun _ e => e) ≤ D + 1 := (MvPolynomial.le_totalDegree hs).trans hq
      have hsplit : s = (s - Finsupp.single l 1) + Finsupp.single l 1 := by
        ext x
        by_cases hx : l = x
        · subst hx
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_eq_same]
          omega
        · simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply,
            if_neg hx]
          omega
      have hsum : (s.sum fun _ e => e) = ((s - Finsupp.single l 1).sum fun _ e => e) + 1 := by
        conv_lhs => rw [hsplit]
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
      omega

private lemma totalDegree_secondOrder_le_of_le_add_two {σ : Type} [Fintype σ] (c : σ → σ → k) (q : MvPolynomial σ k) (D : ℕ)
    (hq : q.totalDegree ≤ D + 2) : (secondOrder k c q).totalDegree ≤ D := by
  unfold secondOrder
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun l _ => ?_)
  refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun l' _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact totalDegree_pderiv_le_of_le_succ l _ D (totalDegree_pderiv_le_of_le_succ l' q (D + 1) hq)

private lemma secondOrder_eq_zero_of_totalDegree_eq_zero {σ : Type} [Fintype σ] (c : σ → σ → k) (q : MvPolynomial σ k)
    (hq : q.totalDegree = 0) : secondOrder k c q = 0 := by
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hq
  rw [hq]
  unfold secondOrder
  simp [MvPolynomial.pderiv_C]

private lemma iterate_secondOrder_eq_zero_of_totalDegree_lt {σ : Type} [Fintype σ] (c : σ → σ → k) (i : ℕ) :
    ∀ q : MvPolynomial σ k, q.totalDegree + 1 ≤ i → (secondOrder k c)^[i] q = 0 := by
  induction i with
  | zero => intro q hq; omega
  | succ i ih =>
    intro q hq
    rw [Function.iterate_succ_apply]
    by_cases h0 : q.totalDegree = 0
    · rw [secondOrder_eq_zero_of_totalDegree_eq_zero c q h0]
      exact Function.iterate_fixed (secondOrder_eq_zero_of_totalDegree_eq_zero c 0 MvPolynomial.totalDegree_zero) i
    · exact ih _ (by have := totalDegree_secondOrder_le_of_le_add_two c q (q.totalDegree - 2) (by omega); omega)

theorem truncated_exp_second_eq_full {ι : Type} [Fintype ι] (c : ι → ι → k) (t : k) (D N : ℕ) (hDN : D ≤ N)
    (y : MvPolynomial ι k) (hy : y.totalDegree ≤ D) : expSecond k c t D y = E1 c t N y := by
  unfold expSecond E1
  have h1 : ∑ i ∈ Finset.range (D + 1),
        (t ^ i * algebraMap ℚ k (1 / (i.factorial : ℚ))) • (secondOrder k c)^[i] y =
      ∑ i ∈ Finset.range (N + 1),
        (t ^ i * algebraMap ℚ k (1 / (i.factorial : ℚ))) • (secondOrder k c)^[i] y := by
    apply Finset.sum_subset (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
    intro i _ hi
    simp only [Finset.mem_range] at hi
    rw [iterate_secondOrder_eq_zero_of_totalDegree_lt c i y (by omega), smul_zero]
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [one_div]
  ring

def TL {σ : Type} [Fintype σ] (c : σ → σ → k) (t : k) (N : ℕ) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  ∑ i ∈ range (N + 1), (algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * t ^ i) • (soL c) ^ i

theorem TL_apply {σ : Type} [Fintype σ] (c : σ → σ → k) (t : k) (N : ℕ) (x : MvPolynomial σ k) :
    TL c t N x = ∑ i ∈ range (N + 1),
      (algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * t ^ i) • (secondOrder k c)^[i] x := by
  rw [TL, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply]
  congr 1
  first
  | exact Module.End.pow_apply _ _ _
  | exact LinearMap.pow_apply _ _ _
  | (rw [Module.End.coe_pow]; rfl)
  | (rw [LinearMap.coe_pow]; rfl)

end Trunc

theorem gauge_second_columns_of_exp (hG : GaugeExpSt) : GaugeIndependenceColumns := by
  intro R _ d O _ _ _ _ _ k _ _ _ B h h' hh hh' w0 mm n ι _ u P hP f
  rcases subsingleton_or_nontrivial k with hk | hk
  · exact Subsingleton.elim _ _
  classical
  set c : ι → ι → k := fun l l' =>
    dotProduct (u l) ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l'))) +
      dotProduct (u l') ((bilinPart k (h' - h)).mulVec ((dAct k B w0).mulVec (u l))) with hc
  set cD : ι × Fin n → ι × Fin n → k := fun p q => if p.2 = q.2 then c p.1 q.1 else 0 with hcD
  have hP' : secondOrder k cD P = 0 := hP
  set t : k := (mm : k) * algebraMap ℚ k (1 / 2) with ht
  set N := P.totalDegree with hN
  set V : Fin n → (ι →₀ ℕ) → k := fun b e => B.nabVal k h w0 mm (f b) u (monomial e 1) with hV
  set W : (ι × Fin n →₀ ℕ) → k := fun mo => ∏ b, V b (colM mo b) with hW
  have hLHS : (∑ mo ∈ P.support, P.coeff mo *
      ∏ b, B.nabVal k h w0 mm (f b) u (monomial (colM mo b) 1)) = lam W P := rfl
  rw [hLHS]
  have hcol : ∀ (mo : (ι × Fin n) →₀ ℕ) (b : Fin n) (l : ι), colM mo b l = mo (l, b) := by
    intro mo b l
    simp [colM]
  have hsum : ∀ mo ∈ P.support, ∑ b, (monomial (colM mo b) (1 : k)).totalDegree ≤ N := by
    intro mo hmo
    have h1 := le_totalDegree hmo
    have h2 : ∀ b, (monomial (colM mo b) (1 : k)).totalDegree = ∑ l, mo (l, b) := by
      intro b
      rw [totalDegree_monomial _ one_ne_zero, Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact sum_congr rfl fun l _ => hcol mo b l
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type] at h1
    simp only [h2]
    rw [sum_comm]
    exact h1
  have key : ∀ mo ∈ P.support, ∏ b, B.nabVal k h' w0 mm (f b) u (monomial (colM mo b) 1) =
      lam W (TL cD t N (monomial mo 1)) := by
    intro mo hmo
    have hbN : ∀ b, (monomial (colM mo b) (1 : k)).totalDegree ≤ N := fun b =>
      (single_le_sum (f := fun b => (monomial (colM mo b) (1 : k)).totalDegree) (fun _ _ => Nat.zero_le _)
        (mem_univ b)).trans (hsum mo hmo)
    have h1 : ∀ b, B.nabVal k h' w0 mm (f b) u (monomial (colM mo b) 1) =
        lam (V b) (E1 c t N (monomial (colM mo b) 1)) := by
      intro b
      rw [hG R d O k B h h' hh hh' w0 mm u _ (f b), nabVal_eq_lam,
        truncated_exp_second_eq_full c t _ N (hbN b) _ le_rfl]
    rw [prod_congr rfl fun b _ => h1 b, ← lam_prodQ V (fun b => E1 c t N (monomial (colM mo b) 1))]
    have hE := exp_cols c t N (fun b => (monomial (colM mo b) (1 : k)).totalDegree) (hsum mo hmo) univ
      (fun b => monomial (colM mo b) 1) (fun _ => le_rfl)
    simp only [mem_univ, if_true] at hE
    have hmoN : (monomial mo (1 : k)).totalDegree ≤ N :=
      (totalDegree_monomial_le _ _).trans (le_totalDegree hmo)
    rw [← hE, cS_univ, prodQ_monomial, glue_colM, exp_opA_apply _ _ _ _ hmoN, TL_apply]
  have hRHS : (∑ mo ∈ P.support, P.coeff mo *
      ∏ b, B.nabVal k h' w0 mm (f b) u (monomial (colM mo b) 1)) = lam W (TL cD t N P) := by
    rw [sum_congr rfl fun mo hmo => by rw [key mo hmo]]
    conv_rhs => rw [as_sum P]
    rw [map_sum, ← lamL_apply, map_sum]
    refine sum_congr rfl fun mo _ => ?_
    rw [show (monomial mo (P.coeff mo) : MvPolynomial (ι × Fin n) k) = P.coeff mo • monomial mo 1 by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, map_smul, lamL_apply, smul_eq_mul]
  have hTP : TL cD t N P = P := by
    rw [TL_apply, sum_eq_single 0]
    · simp
    · intro i _ hi
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
      rw [Function.iterate_succ_apply, hP', Function.iterate_fixed (so_zero _) j, smul_zero]
    · intro h0
      simp at h0
  rw [hRHS, hTP]

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
