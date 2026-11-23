import Formalism.GaussJetBounds.GenLogInverse
import Formalism.GaussJetBounds.StatementS
import Formalism.GradedWeylDivisibility.FinalD

noncomputable section
open scoped BigOperators
open MvPolynomial

namespace Formalism.DworkPowerSeriesWeights

open Formalism.GradedWeylDivisibility

lemma sat_tri_integral {K ι : Type} [NormedField K] [IsUltrametricDist K] [Fintype ι] [PartialOrder ι]
    (T : ι → ι → K) (hT : ∀ i j, ‖T i j‖ ≤ 1) (hd : ∀ i, T i i = 1) (h0 : ∀ i j, ¬ i ≤ j → T i j = 0)
    (c : ι → K) (hc : ∀ i, ‖∑ j, c j * T i j‖ ≤ 1) : ∀ i, ‖c i‖ ≤ 1 := by
  classical
  intro i
  induction i using (wellFounded_gt (α := ι)).induction with
  | _ i ih =>
    have h1 : c i = (∑ j, c j * T i j) - ∑ j ∈ Finset.univ.erase i, c j * T i j := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hd]; ring
    rw [h1, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc i) ?_)
    rw [norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
    intro j hj
    by_cases hij : i ≤ j
    · have hlt : i < j := lt_of_le_of_ne hij (Finset.ne_of_mem_erase hj).symm
      rw [norm_mul]
      exact mul_le_one₀ (ih j hlt) (norm_nonneg _) (hT i j)
    · rw [h0 i j hij]; simp

lemma sat_glue_apply {S τ σ : Type} [Fintype S] [DecidableEq S] (e : S → τ → σ)
    (he : ∀ s t v w, e s v = e t w → s = t ∧ v = w) (m : S → τ →₀ ℕ) (s : S) (v : τ) :
    (∑ t, (m t).mapDomain (e t)) (e s v) = m s v := by
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single s]
  · exact Finsupp.mapDomain_apply (fun x y h => (he s s x y h).2) _ _
  · intro t _ hts
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨w, hw⟩
    exact hts (he t s w v hw).1
  · intro h; exact absurd (Finset.mem_univ s) h

lemma sat_prod_monomial {R α σ : Type} [CommSemiring R] (s : Finset α) (a : α → σ →₀ ℕ) (c : α → R) :
    ∏ i ∈ s, monomial (a i) (c i) = monomial (∑ i ∈ s, a i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, Finset.prod_insert hx, ih, monomial_mul]

lemma sat_coeff_prod_rename {R S τ σ : Type} [CommSemiring R] [Fintype S] [DecidableEq S] (e : S → τ → σ)
    (he : ∀ s t v w, e s v = e t w → s = t ∧ v = w) (f : S → MvPolynomial τ R) (m : S → τ →₀ ℕ) :
    coeff (∑ s, (m s).mapDomain (e s)) (∏ s, rename (e s) (f s)) = ∏ s, coeff (m s) (f s) := by
  classical
  have h1 : ∀ s, rename (e s) (f s) =
      ∑ n ∈ (f s).support, monomial (n.mapDomain (e s)) (coeff n (f s)) := by
    intro s
    conv_lhs => rw [← support_sum_monomial_coeff (f s)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun n _ => rename_monomial _ _ _
  simp_rw [h1]
  rw [Finset.prod_univ_sum, coeff_sum]
  simp_rw [sat_prod_monomial, coeff_monomial]
  have hinj : ∀ N : S → τ →₀ ℕ, (∑ s, (N s).mapDomain (e s)) = (∑ s, (m s).mapDomain (e s)) ↔ N = m := by
    intro N
    constructor
    · intro h
      funext s
      ext v
      have := congrArg (fun x => x (e s v)) h
      simpa only [sat_glue_apply e he] using this
    · rintro rfl; rfl
  simp_rw [hinj]
  rw [Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [Fintype.mem_piFinset] at hm
    push Not at hm
    obtain ⟨s, hs⟩ := hm
    rw [eq_comm]
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simpa using hs)

lemma sat_card_gt {n k C : ℕ} (sz : Fin k → ℕ) (p : Fin C → ℕ) (hsz : ∀ i, sz i ≤ n) (hp : ∀ c, p c ≤ n)
    (h : (shapeDeg sz : Fin n → ℕ) = shapeDeg p) (j : ℕ) :
    (Finset.univ.filter fun i => j < sz i).card = (Finset.univ.filter fun c => j < p c).card := by
  by_cases hj : j < n
  · exact congrFun h ⟨j, hj⟩
  · rw [Finset.filter_false_of_mem (fun i _ => by have := hsz i; omega),
      Finset.filter_false_of_mem (fun c _ => by have := hp c; omega)]
    rfl

lemma sat_card_split {k : ℕ} (sz : Fin k → ℕ) (j : ℕ) :
    (Finset.univ.filter fun i => sz i = j + 1).card + (Finset.univ.filter fun i => j + 1 < sz i).card =
      (Finset.univ.filter fun i => j < sz i).card := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> omega

lemma sat_card_fiber {n k C : ℕ} (sz : Fin k → ℕ) (p : Fin C → ℕ) (hsz : ∀ i, sz i ≤ n) (hp : ∀ c, p c ≤ n)
    (h : (shapeDeg sz : Fin n → ℕ) = shapeDeg p) (j : ℕ) :
    Fintype.card {c // p c = j + 1} = Fintype.card {i // sz i = j + 1} := by
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have h1 := sat_card_split sz j
  have h2 := sat_card_split p j
  have h3 := sat_card_gt sz p hsz hp h j
  have h4 := sat_card_gt sz p hsz hp h (j + 1)
  omega

def satMinor (R : Type) [CommRing R] (r n : ℕ) (x : (j : ℕ) × (Fin j → Fin r)) :
    MvPolynomial (Fin r × Fin n) R :=
  if h : x.1 ≤ n then initMinor R x.2 h else 1

lemma satMinor_zero (R : Type) [CommRing R] (r n : ℕ) (x : (j : ℕ) × (Fin j → Fin r)) (hx : x.1 = 0) :
    satMinor R r n x = 1 := by
  obtain ⟨j, I⟩ := x
  simp only at hx
  subst hx
  simp [satMinor, initMinor]

lemma sat_bidet_eq (R : Type) [CommRing R] {r n k : ℕ} (sz : Fin k → ℕ) (hsz : ∀ i, sz i ≤ n)
    (I : ∀ i, Fin (sz i) → Fin r) : bideterminant R sz hsz I = ∏ i, satMinor R r n ⟨sz i, I i⟩ := by
  unfold bideterminant
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [satMinor, hsz i]

lemma sat_sigma_cast {r a b : ℕ} (h : a = b) (I : Fin b → Fin r) :
    (⟨a, fun i => I (Fin.cast h i)⟩ : (j : ℕ) × (Fin j → Fin r)) = ⟨b, I⟩ := by
  subst h; rfl

lemma sat_prod_fibers {A : Type} [CommMonoid A] {n k : ℕ} (sz : Fin k → ℕ) (hsz : ∀ i, sz i ≤ n) (G : Fin k → A)
    (hG : ∀ i, sz i = 0 → G i = 1) :
    ∏ i, G i = ∏ j ∈ Finset.range n, ∏ i : {i // sz i = j + 1}, G i.1 := by
  classical
  rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (n + 1)) (g := sz)
    (fun i _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hsz i))), Finset.prod_range_succ']
  rw [Finset.prod_eq_one (s := Finset.univ.filter fun i => sz i = 0)
    (fun i hi => hG i (Finset.mem_filter.mp hi).2), mul_one]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact Finset.prod_subtype _ (fun i => by simp) _

lemma sat_bidet_reindex (R : Type) [CommRing R] {r n k C : ℕ} (sz : Fin k → ℕ) (hsz : ∀ i, sz i ≤ n)
    (p : Fin C → ℕ) (hp : ∀ c, p c ≤ n) (h : (shapeDeg sz : Fin n → ℕ) = shapeDeg p)
    (I : ∀ i, Fin (sz i) → Fin r) : ∃ A : ∀ c, Fin (p c) → Fin r, bideterminant R sz hsz I = bideterminant R p hp A := by
  classical
  have e : ∀ j, {c // p c = j + 1} ≃ {i // sz i = j + 1} := fun j =>
    Fintype.equivOfCardEq (sat_card_fiber sz p hsz hp h j)
  have hk : ∀ c, p c ≠ 0 → p c = p c - 1 + 1 := fun c hc => by omega
  let A : ∀ c, Fin (p c) → Fin r := fun c =>
    if h0 : p c = 0 then fun i => (Fin.cast h0 i).elim0
    else fun i => I (e (p c - 1) ⟨c, hk c h0⟩).1
      (Fin.cast ((hk c h0).trans (e (p c - 1) ⟨c, hk c h0⟩).2.symm) i)
  have hA : ∀ j (c : {c // p c = j + 1}),
      (⟨p c.1, A c.1⟩ : (j : ℕ) × (Fin j → Fin r)) = ⟨sz (e j c).1, I (e j c).1⟩ := by
    rintro j ⟨c, hc⟩
    have h0 : p c ≠ 0 := by omega
    have hj : p c - 1 = j := by omega
    subst hj
    simp only [A, dif_neg h0]
    exact sat_sigma_cast _ _
  refine ⟨A, ?_⟩
  rw [sat_bidet_eq, sat_bidet_eq,
    sat_prod_fibers sz hsz _ (fun i hi => satMinor_zero R r n _ hi),
    sat_prod_fibers p hp _ (fun c hc => satMinor_zero R r n _ hc)]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Fintype.prod_equiv (e j) (fun c => satMinor R r n ⟨p c.1, A c.1⟩)
    (fun i => satMinor R r n ⟨sz i.1, I i.1⟩)]
  intro c
  rw [hA j c]

def satEmb (d N0 : ℕ) (s : ZMod d) (v : Fin N0 × Fin N0) : ZMod d × Fin N0 × Fin N0 := (s, v.2, v.1)

lemma satEmb_inj (d N0 : ℕ) (s t : ZMod d) (v w : Fin N0 × Fin N0) (h : satEmb d N0 s v = satEmb d N0 t w) :
    s = t ∧ v = w := by
  simp only [satEmb, Prod.mk.injEq] at h
  exact ⟨h.1, Prod.ext h.2.2 h.2.1⟩

lemma sat_minorProd_eq (K : Type) [CommRing K] (d N0 C : ℕ) (s : ZMod d) (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
    (A : ∀ c, Fin (p c) → Fin N0) :
    minorProd (fun (i a : Fin N0) => (X (s, i, a) : MvPolynomial (ZMod d × Fin N0 × Fin N0) K)) p hp A =
      rename (satEmb d N0 s) (bideterminant K p hp A) := by
  unfold minorProd bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [satEmb, Matrix.transpose_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]
  rfl

lemma sat_map_bidet {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n k : ℕ} (sz : Fin k → ℕ)
    (hsz : ∀ i, sz i ≤ n) (I : ∀ i, Fin (sz i) → Fin r) :
    map φ (bideterminant R sz hsz I) = bideterminant S sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply]

theorem slope_bound_saturation : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (d N0 : ℕ) [NeZero d]
    (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ) (hp : ∀ s c, p s c ≤ N0), SBSat K colN p hp := by
  intro K _ _ d N0 _ colN p hp P hP hint
  classical
  have hb := fun s : ZMod d => sSBasis (unitBall K) N0 N0 (shapeDeg (p s))
  choose b hb1 hb2 using hb
  have : ∀ s : ZMod d, Fintype (ssIdx N0 N0 (shapeDeg (p s) : Fin N0 → ℕ)) :=
    fun s => (sSIdxFinite N0 N0 (shapeDeg (p s))).fintype
  let φ : unitBall K →+* K := (unitBall K).subtype
  let B : (∀ s : ZMod d, ssIdx N0 N0 (shapeDeg (p s) : Fin N0 → ℕ)) →
      MvPolynomial (ZMod d × Fin N0 × Fin N0) K :=
    fun M => ∏ s, rename (satEmb d N0 s) (map φ (b s (M s)))

  have hBx : ∀ M, B M ∈ xMinors (K := K) colN p hp := by
    intro M
    have h1 : ∀ s, ∃ A : ∀ c, Fin (p s c) → Fin N0, b s (M s) = bideterminant (unitBall K) (p s) (hp s) A := by
      intro s
      obtain ⟨-, -, k, sz, hsz, I, hsh, -, hbI⟩ := hb2 s (M s)
      obtain ⟨A, hA⟩ := sat_bidet_reindex (unitBall K) sz hsz (p s) (hp s) hsh I
      exact ⟨A, hbI.trans hA⟩
    choose A hA using h1
    refine ⟨A, Finset.prod_congr rfl fun s _ => ?_⟩
    rw [sat_minorProd_eq, hA s, sat_map_bidet]

  have hspan : ∀ Q ∈ xMinors (K := K) colN p hp, Q ∈ Submodule.span K (Set.range B) := by
    rintro Q ⟨A, rfl⟩
    have h1 : ∀ s, ∃ a : ssIdx N0 N0 (shapeDeg (p s) : Fin N0 → ℕ) → unitBall K,
        ∑ m, a m • b s m = bideterminant (unitBall K) (p s) (hp s) (A s) := by
      intro s
      have h2 := bidetMem (unitBall K) N0 N0 (colN s) (p s) (hp s) (A s)
      rw [← (hb1 s).2.1] at h2
      exact (Submodule.mem_span_range_iff_exists_fun _).mp h2
    choose a ha using h1
    have h3 : ∀ s, minorProd (fun (i a : Fin N0) =>
        (X (s, i, a) : MvPolynomial (ZMod d × Fin N0 × Fin N0) K)) (p s) (hp s) (A s) =
        ∑ m, φ (a s m) • rename (satEmb d N0 s) (map φ (b s m)) := by
      intro s
      rw [sat_minorProd_eq, ← sat_map_bidet φ, ← ha s, map_sum, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_eq_C_mul, map_mul, map_C, map_mul, rename_C, ← smul_eq_C_mul]
    simp_rw [h3]
    rw [Finset.prod_univ_sum]
    refine Submodule.sum_mem _ fun M _ => ?_
    rw [Finset.prod_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨M, rfl⟩)
  have hP' : P ∈ Submodule.span K (Set.range B) := Submodule.span_le.mpr hspan hP
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hP'

  let f : (∀ s : ZMod d, ssIdx N0 N0 (shapeDeg (p s) : Fin N0 → ℕ)) → (ZMod d → (colLex N0 N0).syn) :=
    fun M s => (colLex N0 N0).toSyn (M s).1
  have hf : Function.Injective f := by
    intro M M' h
    funext s
    exact Subtype.ext ((colLex N0 N0).toSyn.injective (congrFun h s))
  let _ : PartialOrder (∀ s : ZMod d, ssIdx N0 N0 (shapeDeg (p s) : Fin N0 → ℕ)) := PartialOrder.lift f hf
  let E : (∀ s : ZMod d, ssIdx N0 N0 (shapeDeg (p s) : Fin N0 → ℕ)) → (ZMod d × Fin N0 × Fin N0 →₀ ℕ) :=
    fun M => ∑ s, ((M s).1).mapDomain (satEmb d N0 s)
  have hT : ∀ M' M, coeff (E M') (B M) = ∏ s, φ (coeff (M' s).1 (b s (M s))) := by
    intro M' M
    simp only [E, B]
    rw [sat_coeff_prod_rename (satEmb d N0) (satEmb_inj d N0)]
    simp only [coeff_map]
  have hcint : ∀ M, ‖c M‖ ≤ 1 := by
    refine sat_tri_integral (fun M' M => coeff (E M') (B M)) ?_ ?_ ?_ c ?_
    · intro M' M
      rw [hT, norm_prod]
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun s _ => (coeff (M' s).1 (b s (M s))).2
    · intro M
      rw [hT]
      refine Finset.prod_eq_one fun s _ => ?_
      have h1 := (hb2 s (M s)).2.1
      rw [MonomialOrder.leadingCoeff, (hb2 s (M s)).1] at h1
      rw [h1, map_one]
    · intro M' M hle
      rw [hT]
      have h1 : ∃ s, ¬ f M' s ≤ f M s := by
        by_contra hcon
        push Not at hcon
        exact hle hcon
      obtain ⟨s, hs⟩ := h1
      refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
      rw [MonomialOrder.coeff_eq_zero_of_lt, map_zero]
      rw [(hb2 s (M s)).1]
      exact not_le.mp hs
    · intro M'
      have h1 : ∑ M, c M * coeff (E M') (B M) = coeff (E M') P := by
        rw [← hc, coeff_sum]
        exact Finset.sum_congr rfl fun M _ => by rw [coeff_smul, smul_eq_mul]
      rw [h1]
      exact hint _
  rw [← hc]
  refine Submodule.sum_mem _ fun M _ => ?_
  exact Submodule.smul_mem _ (⟨c M, hcint M⟩ : unitBall K) (Submodule.subset_span (hBx M))

end Formalism.DworkPowerSeriesWeights
