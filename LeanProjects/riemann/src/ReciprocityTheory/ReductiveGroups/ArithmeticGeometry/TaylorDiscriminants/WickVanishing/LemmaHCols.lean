import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GermSCCols
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SecondColumnOperator
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LemmaH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick

set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols

variable {k : Type} [CommRing k] {ι : Type} [Fintype ι] {n : ℕ}

def Mf (mu : Fin n → MvPolynomial ι k →ₗ[k] k) (P : MvPolynomial (ι × Fin n) k) : k :=
  ∑ mo ∈ P.support, P.coeff mo * ∏ b, mu b (monomial (colM mo b) 1)

variable (mu : Fin n → MvPolynomial ι k →ₗ[k] k)

theorem Mf_subset (P : MvPolynomial (ι × Fin n) k) (S : Finset (ι × Fin n →₀ ℕ)) (hS : P.support ⊆ S) :
    Mf mu P = ∑ mo ∈ S, P.coeff mo * ∏ b, mu b (monomial (colM mo b) 1) := by
  unfold Mf
  refine Finset.sum_subset hS (fun mo _ h => ?_)
  first
    | rw [MvPolynomial.notMem_support_iff.mp h, zero_mul]
    | rw [MvPolynomial.not_mem_support_iff.mp h, zero_mul]

theorem Mf_add (P Q : MvPolynomial (ι × Fin n) k) : Mf mu (P + Q) = Mf mu P + Mf mu Q := by
  classical
  rw [Mf_subset mu (P + Q) (P.support ∪ Q.support) MvPolynomial.support_add,
    Mf_subset mu P _ Finset.subset_union_left, Mf_subset mu Q _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun mo _ => ?_)
  rw [MvPolynomial.coeff_add, add_mul]

theorem Mf_smul (a : k) (P : MvPolynomial (ι × Fin n) k) : Mf mu (a • P) = a * Mf mu P := by
  rw [Mf_subset mu (a • P) P.support MvPolynomial.support_smul, Mf, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun mo _ => ?_)
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc]

theorem Mf_zero : Mf mu (0 : MvPolynomial (ι × Fin n) k) = 0 := by
  simp [Mf]

theorem Mf_sum {α : Type} (s : Finset α) (P : α → MvPolynomial (ι × Fin n) k) :
    Mf mu (∑ a ∈ s, P a) = ∑ a ∈ s, Mf mu (P a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Mf_zero mu]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Mf_add, ih]

theorem Mf_monomial (mo : ι × Fin n →₀ ℕ) (a : k) :
    Mf mu (monomial mo a) = a * ∏ b, mu b (monomial (colM mo b) 1) := by
  classical
  rw [Mf_subset mu _ {mo} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

def combine (f : Fin n → (ι →₀ ℕ)) : ι × Fin n →₀ ℕ :=
  ∑ b, Finsupp.mapDomain (fun l => (l, b)) (f b)

theorem combine_apply (f : Fin n → (ι →₀ ℕ)) (l : ι) (b : Fin n) : combine f (l, b) = f b l := by
  classical
  unfold combine
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single b]
  · exact Finsupp.mapDomain_apply (fun x y h => (Prod.mk.inj h).1) (f b) l
  · intro b' _ hb'
    apply Finsupp.mapDomain_notin_range
    rintro ⟨l', hl'⟩
    exact hb' (Prod.mk.inj hl').2
  · intro h
    exact absurd (Finset.mem_univ b) h

theorem colM_combine (f : Fin n → (ι →₀ ℕ)) (b : Fin n) : colM (combine f) b = f b := by
  ext l
  simp [colM, combine_apply]

theorem combine_colM (mo : ι × Fin n →₀ ℕ) : combine (colM mo) = mo := by
  ext ⟨l, b⟩
  rw [combine_apply]
  simp [colM]

theorem prod_monomial' {β : Type} (s : Finset β) (g : β → ι × Fin n →₀ ℕ) (a : β → k) :
    ∏ b ∈ s, monomial (g b) (a b) = monomial (∑ b ∈ s, g b) (∏ b ∈ s, a b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, ih, MvPolynomial.monomial_mul, Finset.sum_insert hx, Finset.prod_insert hx]

theorem prodQ_monomial (f : Fin n → (ι →₀ ℕ)) (a : Fin n → k) :
    prodQ (fun b => monomial (f b) (a b)) = monomial (combine f) (∏ b, a b) := by
  unfold prodQ
  simp only [colE, MvPolynomial.rename_monomial]
  rw [prod_monomial']
  rfl

theorem Mf_prodQ (R : Fin n → MvPolynomial ι k) : Mf mu (prodQ R) = ∏ b, mu b (R b) := by
  classical
  have hR : ∀ b, colE b (R b) = ∑ α ∈ (R b).support, colE b (monomial α (coeff α (R b))) := by
    intro b
    conv_lhs => rw [as_sum (R b)]
    rw [map_sum]
  have hmu : ∀ b, mu b (R b) = ∑ α ∈ (R b).support, coeff α (R b) * mu b (monomial α 1) := by
    intro b
    conv_lhs => rw [as_sum (R b)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun α _ => by
      rw [show monomial α (coeff α (R b)) = coeff α (R b) • monomial α (1 : k) by
        rw [smul_monomial, smul_eq_mul, mul_one], map_smul, smul_eq_mul]
  rw [prodQ, Finset.prod_congr rfl (fun b _ => hR b), Finset.prod_univ_sum, Mf_sum,
    Finset.prod_congr rfl (fun b _ => hmu b), Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hp := prodQ_monomial x (fun b => coeff (x b) (R b))
  simp only [prodQ] at hp
  rw [hp, Mf_monomial, Finset.prod_mul_distrib]
  simp only [colM_combine]

theorem degree_colM (mo : ι × Fin n →₀ ℕ) : ∑ b, (colM mo b).degree = mo.degree := by
  classical
  have hd : ∀ {σ : Type} [Fintype σ] (m : σ →₀ ℕ), m.degree = ∑ i, m i := by
    intro σ _ m
    unfold Finsupp.degree
    exact Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => Finsupp.notMem_support_iff.mp hi)
  simp only [hd]
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp [colM]

theorem totalDegree_monomial_one_le (α : ι →₀ ℕ) : (monomial α (1 : k)).totalDegree ≤ α.degree := by
  classical
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro s hs
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hs)]
  exact le_rfl

theorem iter_linear (c : ι × Fin n → ι × Fin n → k) (i : ℕ) :
    ∀ x : MvPolynomial (ι × Fin n) k, (secondOrder k c)^[i] x = ((soL c) ^ i) x := by
  induction i with
  | zero => intro x; simp
  | succ i ih =>
    intro x
    rw [Function.iterate_succ_apply', ih, pow_succ']
    rfl

theorem iter_zero' (c : ι × Fin n → ι × Fin n → k) (i : ℕ) :
    (secondOrder k c)^[i] (0 : MvPolynomial (ι × Fin n) k) = 0 := by
  rw [iter_linear]
  exact map_zero _

variable [Algebra ℚ k]

theorem colAlg (κ : ι → ι → k) (lam : Fin n → (ι →₀ ℕ) → k)
    (hlm : ∀ b α, lam b α = ∑ i ∈ Finset.range ((monomial α (1 : k)).totalDegree + 1),
        mu b (((i.factorial : ℚ)⁻¹) • (secondOrder k κ)^[i] (monomial α 1)))
    (P : MvPolynomial (ι × Fin n) k)
    (hP : secondOrder k (fun p q : ι × Fin n => if p.2 = q.2 then κ p.1 q.1 else 0) P = 0) :
    ∑ mo ∈ P.support, P.coeff mo * ∏ b, lam b (colM mo b) = Mf mu P := by
  classical
  set N := P.totalDegree with hN
  set cc : ι × Fin n → ι × Fin n → k := cS κ (Finset.univ : Finset (Fin n)) with hcc
  have hccu : cc = fun p q : ι × Fin n => if p.2 = q.2 then κ p.1 q.1 else 0 := cS_univ κ
  have hE : ∀ b α, (monomial α (1 : k)).totalDegree ≤ N →
      lam b α = mu b (E1 κ 1 N (monomial α 1)) := by
    intro b α hα
    rw [hlm, E1, map_sum]
    refine Finset.sum_subset (Finset.range_subset_range.2 (Nat.succ_le_succ hα)) (fun i hi hi' => ?_) |>.trans ?_
    · rw [so_iter_eq_zero κ i _ (by simp only [Finset.mem_range] at hi'; omega), smul_zero, map_zero]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [one_pow, mul_one, ← algebraMap_smul k ((i.factorial : ℚ)⁻¹)]
  have hmo : ∀ mo ∈ P.support, ∏ b, lam b (colM mo b) =
      ∑ i ∈ Finset.range (N + 1), (algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * 1 ^ i) *
        Mf mu ((secondOrder k cc)^[i] (monomial mo 1)) := by
    intro mo hmo
    have hdeg : mo.degree ≤ N := by
      have := le_totalDegree hmo
      exact le_of_eq_of_le (by rfl) this
    have hD : ∀ b, (monomial (colM mo b) (1 : k)).totalDegree ≤ (colM mo b).degree :=
      fun b => totalDegree_monomial_one_le _
    have hsum : ∑ b, (colM mo b).degree ≤ N := (degree_colM mo).le.trans hdeg
    have hb : ∀ b, (monomial (colM mo b) (1 : k)).totalDegree ≤ N := fun b =>
      (hD b).trans ((Finset.single_le_sum (fun b _ => Nat.zero_le _) (Finset.mem_univ b)).trans hsum)
    rw [Finset.prod_congr rfl (fun b _ => hE b (colM mo b) (hb b)), ← Mf_prodQ]
    have hx := exp_cols κ 1 N (fun b => (colM mo b).degree) hsum Finset.univ
      (fun b => monomial (colM mo b) 1) hD
    simp only [Finset.mem_univ, if_true] at hx
    rw [← hx, prodQ_monomial, Finset.prod_const_one, combine_colM,
      exp_opA_apply _ _ _ _ ((totalDegree_monomial_one_le mo).trans hdeg), Mf_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Mf_smul]
  rw [Finset.sum_congr rfl fun mo hmo' => by rw [hmo mo hmo']]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hlin : ∀ i, ∑ mo ∈ P.support, P.coeff mo * ((algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * 1 ^ i) *
      Mf mu ((secondOrder k cc)^[i] (monomial mo 1))) =
      (algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * 1 ^ i) * Mf mu ((secondOrder k cc)^[i] P) := by
    intro i
    conv_rhs => rw [as_sum P]
    rw [iter_linear, map_sum, Mf_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun mo _ => ?_
    rw [show monomial mo (P.coeff mo) = P.coeff mo • monomial mo (1 : k) by
      rw [smul_monomial, smul_eq_mul, mul_one], map_smul, Mf_smul, ← iter_linear]
    ring
  rw [Finset.sum_congr rfl fun i _ => hlin i, Finset.sum_range_succ', Finset.sum_eq_zero]
  · simp
  · intro i _
    rw [Function.iterate_succ_apply, hccu, hP, iter_zero', Mf_zero, mul_zero]

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def valL {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O] {k : Type} [CommRing k]
    [Algebra ℚ k] [Algebra R k] (B : FB R d O) {ι : Type} [Fintype ι] (u : ι → Fin d → k) (g : PS k 1 d) :
    MvPolynomial ι k →ₗ[k] k where
  toFun Q := MvPowerSeries.constantCoeff (DpolyOf (B.FK k) u Q g)
  map_add' P Q := by rw [GE.dpolyOf_add_P, map_add]
  map_smul' a Q := by
    rw [GE.dpolyOf_smul_P, map_mul, MvPowerSeries.constantCoeff_C, RingHom.id_apply, smul_eq_mul]

theorem lemmaHCols_of (hV : ValueSt) (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) : LemmaHColsSt := by
  intro R _ d O _ _ k _ _ _ B h hax m ι π _ _ c s u φ _ hUF hFU n P hP g
  have hP' : secondOrder k (fun p q : ι × Fin n =>
      if p.2 = q.2 then SCPf.kapH m c s u φ p.1 q.1 else 0) P = 0 := by
    rw [← hP]
    congr 1
    funext p q
    unfold SCPf.kapH
    by_cases h1 : p.2 = q.2
    · simp [h1]
    · simp [h1]
  have key := colAlg (fun b => valL B u (g b)) (SCPf.kapH m c s u φ)
    (fun b α => MvPowerSeries.constantCoeff (ordNabla k B h m s (fun l => (u l, φ l))
      (MvPolynomial.monomial α 1) (liftX k (g b))))
    (fun b α => SCPf.ordNabla_value_expand hV hN2 hN3 B h hax m c s u φ hUF hFU _ (g b)) P hP'
  exact key

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols
