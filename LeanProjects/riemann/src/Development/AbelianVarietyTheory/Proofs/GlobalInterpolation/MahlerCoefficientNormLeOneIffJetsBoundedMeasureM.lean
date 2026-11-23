import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMeasureOfBoundedMoments
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor

open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate ContDiff

noncomputable section

namespace GlobalTheory.MomCrit

variable {q : ℕ} [Fact q.Prime] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem continuous_zc' : Continuous (zc : ℤ_[q] → ℂ_[q]) :=
  (continuous_algebraMap ℚ_[q] ℂ_[q]).comp continuous_subtype_val

def evalFn (ι : ℂ ≃+* ℂ_[q]) {κ : Type} (P : MvPolynomial κ ℂ) : C(κ → ℤ_[q], ℂ_[q]) :=
  ⟨fun a => MvPolynomial.eval (fun i => zc (a i)) (MvPolynomial.map (ι : ℂ →+* ℂ_[q]) P),
    (MvPolynomial.continuous_eval _).comp
      (continuous_pi fun i => continuous_zc'.comp (continuous_apply i))⟩

theorem evalFn_apply (ι : ℂ ≃+* ℂ_[q]) {κ : Type} (P : MvPolynomial κ ℂ) (a : κ → ℤ_[q]) :
    evalFn ι P a = MvPolynomial.eval₂ (ι : ℂ →+* ℂ_[q]) (fun i => zc (a i)) P := by
  show MvPolynomial.eval _ _ = _
  rw [MvPolynomial.eval_map]

theorem evalFn_add (ι : ℂ ≃+* ℂ_[q]) {κ : Type} (P Q : MvPolynomial κ ℂ) :
    evalFn ι (P + Q) = evalFn ι P + evalFn ι Q := by
  ext a; simp [evalFn_apply]

theorem evalFn_zero (ι : ℂ ≃+* ℂ_[q]) {κ : Type} : evalFn ι (0 : MvPolynomial κ ℂ) = 0 := by
  ext a; simp [evalFn_apply]

theorem evalFn_smul (ι : ℂ ≃+* ℂ_[q]) {κ : Type} (c : ℂ) (P : MvPolynomial κ ℂ) :
    evalFn ι (c • P) = ι c • evalFn ι P := by
  ext a; simp [evalFn_apply, MvPolynomial.smul_eq_C_mul]

theorem prod_pow_eq_list {σ M : Type} [CommMonoid M] (F : σ → M) (e : σ →₀ ℕ) {n : ℕ} (f : Fin n → σ)
    (hm : Finsupp.toMultiset e = (↑(List.ofFn f) : Multiset σ)) :
    (e.prod fun k n => F k ^ n) = ∏ i, F (f i) := by
  classical
  have h1 : ((Finsupp.toMultiset e).map F).prod = e.prod fun k n => F k ^ n := by
    rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset, Finsupp.prod_mapDomain_index]
    · intro _; simp
    · intro _ _ _; rw [pow_add]
  rw [← h1, hm, Multiset.map_coe, Multiset.prod_coe, List.map_ofFn, List.prod_ofFn]
  rfl

theorem evalFn_monomial (ι : ℂ ≃+* ℂ_[q]) {κ : Type} (u : κ →₀ ℕ) {k : ℕ} (j : Fin k → κ)
    (hu : Finsupp.toMultiset u = (↑(List.ofFn j) : Multiset κ)) (a : κ → ℤ_[q]) :
    evalFn ι (MvPolynomial.monomial u 1) a = ∏ l, zc (a (j l)) := by
  rw [evalFn_apply, MvPolynomial.eval₂_monomial, map_one, one_mul]
  exact prod_pow_eq_list (fun i => zc (a i)) u j hu

def jetL {κ : Type} [Fintype κ] (v : κ → V) (G : V → ℂ) : MvPolynomial κ ℂ →ₗ[ℂ] ℂ :=
  (MvPolynomial.basisMonomials κ ℂ).constr ℂ (monoJet v G)

theorem jetL_monomial {κ : Type} [Fintype κ] (v : κ → V) (G : V → ℂ) (u : κ →₀ ℕ) :
    jetL v G (MvPolynomial.monomial u 1) = monoJet v G u := by
  have := (MvPolynomial.basisMonomials κ ℂ).constr_basis ℂ (monoJet v G) u
  rwa [MvPolynomial.coe_basisMonomials] at this

theorem jetL_apply {κ : Type} [Fintype κ] (v : κ → V) (G : V → ℂ) (P : MvPolynomial κ ℂ) :
    jetL v G P = ∑ m ∈ P.support, P.coeff m * monoJet v G m := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : MvPolynomial.monomial m (P.coeff m) = P.coeff m • MvPolynomial.monomial m (1 : ℂ) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, jetL_monomial, smul_eq_mul]

def Bm {κ : Type} [Fintype κ] (n : κ → ℕ) : MvPolynomial κ ℂ :=
  ∏ i, MvPolynomial.C (((n i).factorial : ℂ)⁻¹) *
    Polynomial.aeval (MvPolynomial.X i : MvPolynomial κ ℂ) (descPochhammer ℂ (n i))

def Bp {κ : Type} [Fintype κ] (n : κ → ℕ) : MvPolynomial κ ℂ :=
  ∏ i, Polynomial.aeval (MvPolynomial.X i : MvPolynomial κ ℂ) (descPochhammer ℂ (n i))

theorem mahler_eq_jetL {κ : Type} [Fintype κ] (v : κ → V) (G : V → ℂ) (n : κ → ℕ) :
    mahler v G n = jetL v G (Bm n) := by
  rw [jetL_apply]; rfl

theorem Bp_eq {κ : Type} [Fintype κ] (n : κ → ℕ) : Bp n = (∏ i, ((n i).factorial : ℂ)) • Bm n := by
  rw [Bm, Bp, Finset.prod_mul_distrib, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_prod, ← map_mul,
    ← Finset.prod_mul_distrib]
  have : ∀ i, ((n i).factorial : ℂ) * ((n i).factorial : ℂ)⁻¹ = 1 := fun i =>
    mul_inv_cancel₀ (by exact_mod_cast (n i).factorial_ne_zero)
  simp [this]

theorem eval_descPochhammer (ι : ℂ ≃+* ℂ_[q]) {κ : Type} (a : κ → ℤ_[q]) (i : κ) (k : ℕ) :
    MvPolynomial.eval₂Hom (ι : ℂ →+* ℂ_[q]) (fun i => zc (a i))
      (Polynomial.aeval (MvPolynomial.X i : MvPolynomial κ ℂ) (descPochhammer ℂ k)) =
      (k.factorial : ℂ_[q]) * zc (Ring.choose (a i) k) := by
  have h1 : MvPolynomial.eval₂Hom (ι : ℂ →+* ℂ_[q]) (fun i => zc (a i))
      (Polynomial.aeval (MvPolynomial.X i : MvPolynomial κ ℂ) (descPochhammer ℂ k)) =
      ∏ r ∈ Finset.range k, (zc (a i) - r) := by
    induction k with
    | zero => simp
    | succ k ih => rw [descPochhammer_succ_right, map_mul, map_mul, ih, Finset.prod_range_succ]; simp
  have h2 : ∀ k : ℕ, (descPochhammer ℤ k).smeval (a i) = ∏ r ∈ Finset.range k, (a i - r) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih, Finset.prod_range_succ]
      simp [Polynomial.smeval_sub, Polynomial.smeval_natCast]
  have h3 := Ring.descPochhammer_eq_factorial_smul_choose (a i) k
  rw [h2] at h3
  have h4 := congrArg ((algebraMap ℚ_[q] ℂ_[q]).comp PadicInt.Coe.ringHom) h3
  rw [h1]
  simp only [map_prod, map_sub, map_natCast, map_nsmul] at h4
  rw [nsmul_eq_mul] at h4
  exact h4

theorem evalFn_Bm (ι : ℂ ≃+* ℂ_[q]) {κ : Type} [Fintype κ] (n : κ → ℕ) (a : κ → ℤ_[q]) :
    evalFn ι (Bm n) a = ∏ i, GlobalTheory.MultiMahler.binomC (n i) (a i) := by
  rw [evalFn_apply, ← MvPolynomial.coe_eval₂Hom, Bm, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, eval_descPochhammer, MvPolynomial.eval₂Hom_C]
  have : ((n i).factorial : ℂ_[q]) ≠ 0 := by exact_mod_cast (n i).factorial_ne_zero
  have e : (ι : ℂ →+* ℂ_[q]) (((n i).factorial : ℂ)⁻¹) = ((n i).factorial : ℂ_[q])⁻¹ := by simp
  rw [e, ← mul_assoc, inv_mul_cancel₀ this, one_mul]
  rfl

theorem isMom_eval (ι : ℂ ≃+* ℂ_[q]) {κ : Type} [Fintype κ] {v : κ → V} {G : V → ℂ}
    {μ : C(κ → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]} (h : IsMom ι v G μ) (P : MvPolynomial κ ℂ) :
    ι (jetL v G P) = μ (evalFn ι P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    have e : MvPolynomial.monomial u c = c • MvPolynomial.monomial u (1 : ℂ) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, jetL_monomial, smul_eq_mul, map_mul, evalFn_smul, ContinuousLinearMap.map_smul, smul_eq_mul]
    congr 1
    exact h _ (fun l => u.toMultiset.toList.get l) _
      (evalFn_monomial ι u _ (by rw [List.ofFn_get, Multiset.coe_toList]))
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ, evalFn_add, map_add]

theorem X_pow_mem_span (k : ℕ) :
    (Polynomial.X : Polynomial ℂ) ^ k ∈ Submodule.span ℂ (Set.range fun j => descPochhammer ℂ j) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hd : descPochhammer ℂ k - Polynomial.X ^ k ∈ Polynomial.degreeLT ℂ k := by
      rw [Polynomial.mem_degreeLT]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · have h1 := monic_descPochhammer ℂ k
        have h2 : (descPochhammer ℂ k).degree = k := by
          rw [Polynomial.degree_eq_natDegree h1.ne_zero, descPochhammer_natDegree]
        calc _ < (descPochhammer ℂ k).degree :=
              Polynomial.degree_sub_lt (by rw [h2, Polynomial.degree_X_pow]) h1.ne_zero
                (by rw [h1.leadingCoeff, Polynomial.leadingCoeff_X_pow])
          _ = k := h2
    rw [Polynomial.degreeLT_eq_span_X_pow] at hd
    have hle : Submodule.span ℂ ↑(Finset.image (fun n => (Polynomial.X : Polynomial ℂ) ^ n) (Finset.range k)) ≤
        Submodule.span ℂ (Set.range fun j => descPochhammer ℂ j) := by
      rw [Submodule.span_le]
      intro p hp
      simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hp
      obtain ⟨j, hj, rfl⟩ := hp
      exact ih j hj
    have := Submodule.sub_mem _ (Submodule.subset_span (Set.mem_range_self (f := fun j => descPochhammer ℂ j) k)) (hle hd)
    simpa using this

theorem monomial_mem_span {κ : Type} [Fintype κ] (m : κ →₀ ℕ) :
    MvPolynomial.monomial m (1 : ℂ) ∈ Submodule.span ℂ (Set.range (Bp (κ := κ))) := by
  classical
  have hX : ∀ k, ∃ c : ℕ →₀ ℂ, (c.sum fun j a => a • descPochhammer ℂ j) = Polynomial.X ^ k :=
    fun k => (Finsupp.mem_span_range_iff_exists_finsupp).1 (X_pow_mem_span k)
  choose c hc using hX
  have e1 : MvPolynomial.monomial m (1 : ℂ) = ∏ i, ∑ j ∈ (c (m i)).support,
      c (m i) j • Polynomial.aeval (MvPolynomial.X i : MvPolynomial κ ℂ) (descPochhammer ℂ j) := by
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    refine Finset.prod_congr rfl fun i _ => ?_
    have := congrArg (Polynomial.aeval (MvPolynomial.X i : MvPolynomial κ ℂ)) (hc (m i))
    rw [Polynomial.aeval_X_pow, Finsupp.sum, map_sum] at this
    rw [← this]
    simp only [map_smul]
  rw [e1, Finset.prod_univ_sum]
  refine Submodule.sum_mem _ fun p _ => ?_
  have e2 : ∏ i, c (m i) (p i) • Polynomial.aeval (MvPolynomial.X i : MvPolynomial κ ℂ) (descPochhammer ℂ (p i)) =
      (∏ i, c (m i) (p i)) • Bp p := by
    simp_rw [MvPolynomial.smul_eq_C_mul]
    rw [Finset.prod_mul_distrib, ← map_prod, Bp]
  rw [e2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self p))

theorem eq_of_mem_span (ι : ℂ ≃+* ℂ_[q]) {κ : Type} [Fintype κ] {v : κ → V} {G : V → ℂ}
    (μ : C(κ → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]) (h : ∀ n, μ (evalFn ι (Bp n)) = ι (jetL v G (Bp n)))
    (P : MvPolynomial κ ℂ) (hP : P ∈ Submodule.span ℂ (Set.range (Bp (κ := κ)))) :
    μ (evalFn ι P) = ι (jetL v G P) := by
  induction hP using Submodule.span_induction with
  | mem x hx => obtain ⟨n, rfl⟩ := hx; exact h n
  | zero => simp [evalFn_zero]
  | add x y _ _ hx hy => rw [evalFn_add, map_add, hx, hy, map_add, map_add]
  | smul c x _ hx => rw [evalFn_smul, map_smul, hx, map_smul, smul_eq_mul, smul_eq_mul, map_mul]

theorem jet_eq_monoJet {κ : Type} [Fintype κ] {v : κ → V} {G : V → ℂ} (hG : ContDiff ℂ ⊤ G) {k : ℕ}
    (j : Fin k → κ) (m : κ →₀ ℕ) (hm : Finsupp.toMultiset m = ↑(List.ofFn j)) :
    iteratedFDeriv ℂ k G 0 (fun l => v (j l)) = monoJet v G m := by
  have p : ((List.ofFn j).map v).Perm ((Finsupp.toMultiset m).toList.map v) := by
    refine List.Perm.map _ ?_
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, hm]
  have h1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.lD_perm (hG.contDiffAt (x := 0)) p
  rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.lD_eq G 0 _ (n := k) (by simp),
    ReciprocityTheory.ChartRestriction.G.PullbackSections.lD_eq G 0 _ (n := (Finsupp.toMultiset m).toList.length) (by simp)] at h1
  unfold monoJet
  refine Eq.trans (congrArg _ (funext fun i => ?_)) (h1.trans (congrArg _ (funext fun i => ?_)))
  · simp [List.get_eq_getElem]
  · simp [List.get_eq_getElem]

end GlobalTheory.MomCrit

namespace GlobalTheory.MomCrit

theorem momInt_iff_norm_mahler_le : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℂ V] (κ : Type) [Fintype κ] (v : κ → V) (G : V → ℂ), ContDiff ℂ ⊤ G →
      (MomInt ι v G ↔ ∀ n, ‖ι (mahler v G n)‖ ≤ 1) := by
  intro q _ ι V _ _ κ _ v G hG
  classical
  constructor
  · rintro ⟨μ, hμ, h⟩ n
    rw [mahler_eq_jetL, isMom_eval ι h]
    refine (μ.le_opNorm _).trans (mul_le_one₀ hμ (norm_nonneg _) ?_)
    refine (ContinuousMap.norm_le _ zero_le_one).2 fun a => ?_
    rw [evalFn_Bm, norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => GlobalTheory.MultiMahler.norm_binomC_le _ _
  · intro h
    let e := Fintype.equivFin κ
    let c : (Fin (Fintype.card κ) → ℕ) → ℂ_[q] := fun n' => ι (mahler v G (n' ∘ e))
    obtain ⟨μ', hnorm, hsum⟩ :=
      GlobalTheory.MultiMahler.exists_measure_of_bounded_moments q (Fintype.card κ) c ⟨1, fun n' => h _⟩
    have hμ' : ‖μ'‖ ≤ 1 := (hnorm 1 zero_le_one).2 fun n' => h _
    let r : C(Fin (Fintype.card κ) → ℤ_[q], κ → ℤ_[q]) := ⟨fun a i => a (e i), by fun_prop⟩
    let T : C(κ → ℤ_[q], ℂ_[q]) →ₗ[ℂ_[q]] ℂ_[q] :=
      { toFun := fun F => μ' (F.comp r)
        map_add' := fun F F' => by rw [ContinuousMap.add_comp, map_add]
        map_smul' := fun s F => by rw [ContinuousMap.smul_comp, map_smul]; rfl }
    have hT : ∀ F, ‖T F‖ ≤ 1 * ‖F‖ := fun F => by
      refine (μ'.le_opNorm _).trans (mul_le_mul hμ' ?_ (norm_nonneg _) zero_le_one)
      exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun a => F.norm_coe_le_norm _
    refine ⟨T.mkContinuous 1 hT, LinearMap.mkContinuous_norm_le _ zero_le_one _, ?_⟩
    have hB : ∀ n, T.mkContinuous 1 hT (evalFn ι (Bm n)) = ι (mahler v G n) := by
      intro n
      change μ' ((evalFn ι (Bm n)).comp r) = _
      have hF : ∀ a, ((evalFn ι (Bm n)).comp r) a = ∏ i', GlobalTheory.MultiMahler.binomC (n (e.symm i')) (a i') := by
        intro a
        rw [ContinuousMap.comp_apply, evalFn_Bm, ← Equiv.prod_comp e.symm]
        simp [r]
      refine (hsum _ _ hF).unique ?_
      convert hasSum_single (f := fun m : Fin (Fintype.card κ) → ℕ =>
        c m * ∏ i, (fwdDiff (1 : ℤ_[q]))^[m i] (GlobalTheory.MultiMahler.binomC (q := q) (n (e.symm i))) 0) (n ∘ e.symm) ?_ using 1
      · simp [GlobalTheory.MultiMahler.fwdDiff_binomC, c, Function.comp_assoc]
      · intro m hm
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hm
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [GlobalTheory.MultiMahler.fwdDiff_binomC, if_neg (by simpa using hi)]), mul_zero]
    have hP := eq_of_mem_span ι (v := v) (G := G) (T.mkContinuous 1 hT) (fun n => by
      rw [Bp_eq, evalFn_smul, map_smul, hB, mahler_eq_jetL, map_smul, smul_eq_mul, smul_eq_mul, map_mul])
    intro k j f hf
    have hmm : Finsupp.toMultiset (Multiset.toFinsupp (↑(List.ofFn j) : Multiset κ)) = ↑(List.ofFn j) :=
      Multiset.toFinsupp_toMultiset _
    have hfe : f = evalFn ι (MvPolynomial.monomial (Multiset.toFinsupp (↑(List.ofFn j) : Multiset κ)) 1) :=
      ContinuousMap.ext fun a => by rw [hf, evalFn_monomial ι _ j hmm]
    rw [hfe, hP _ (monomial_mem_span _), jetL_monomial, jet_eq_monoJet hG j _ hmm]

end GlobalTheory.MomCrit
