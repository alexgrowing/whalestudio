import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.TopLimitModules.FmodConst

set_option autoImplicit false

noncomputable section

open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF

namespace ReciprocityTheory.ChartRestriction.G.Pdiv.TL

section Jets

variable {T : Type} [CommRing T]

theorem limJ_mk_eq_iff {σ : Type} (k : ℕ) (P Q : MvPolynomial σ T) :
    (Ideal.Quotient.mk _ P : JetR T σ k) = Ideal.Quotient.mk _ Q ↔
      ∀ x : σ →₀ ℕ, x.degree < k + 1 → P.coeff x = Q.coeff x := by
  rw [Ideal.Quotient.eq]
  have hI : (Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ T))) =
      MvPolynomial.idealOfVars σ T := rfl
  rw [hI, MvPolynomial.mem_pow_idealOfVars_iff]
  constructor
  · intro h x hx
    by_contra hne
    have hmem : x ∈ (P - Q).support := by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub]
      exact sub_ne_zero.mpr hne
    have := h x hmem
    omega
  · intro h x hx
    by_contra hlt
    push_neg at hlt
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sub, h x hlt, sub_self] at hx
    exact hx rfl

theorem limJ_tt_eq_iff {σ : Type} [Finite σ] (k : ℕ) (f g : MvPowerSeries σ T) :
    truncTotalAlgHom σ T (k + 1) f = truncTotalAlgHom σ T (k + 1) g ↔
      ∀ x : σ →₀ ℕ, x.degree < k + 1 → coeff x f = coeff x g := by
  rw [MvPowerSeries.truncTotalAlgHom_apply, MvPowerSeries.truncTotalAlgHom_apply]
  refine (limJ_mk_eq_iff k (truncTotal (k + 1) f) (truncTotal (k + 1) g)).trans ?_
  refine forall_congr' fun x => imp_congr_right fun hx => ?_
  rw [MvPowerSeries.coeff_truncTotal _ hx, MvPowerSeries.coeff_truncTotal _ hx]

theorem limJ_lt_box {σ : Type} [Finite σ] (i0 : σ) (k : ℕ) (x : σ →₀ ℕ) (hx : x.degree < k + 1) :
    x < Finsupp.equivFunOnFinite.symm (fun _ : σ => k + 1) := by
  classical
  have hle : ∀ i, x i ≤ x.degree := fun i => by
    by_cases hi : i ∈ x.support
    · exact Finset.single_le_sum (f := fun j => x j) (fun _ _ => Nat.zero_le _) hi
    · have h0 : x i = 0 := by
        by_contra h'
        exact hi (Finsupp.mem_support_iff.mpr h')
      rw [h0]
      exact Nat.zero_le _
  refine lt_of_le_of_ne (fun i => ?_) (fun h => ?_)
  · show x i ≤ k + 1
    have := hle i
    omega
  · have h2 : x i0 = k + 1 := by
      rw [h]
      rfl
    have := hle i0
    omega

theorem limJ_psJet_eq {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (k : ℕ) (f : PS T n d) :
    psJet k f = truncTotalAlgHom (Fin n × Fin d) T (k + 1) f := by
  rw [MvPowerSeries.truncTotalAlgHom_apply]
  refine (limJ_mk_eq_iff k _ _).mpr fun x hx => ?_
  classical
  rw [MvPowerSeries.coeff_truncTotal _ hx, MvPowerSeries.coeff_trunc,
    if_pos (limJ_lt_box (⟨0, hn⟩, ⟨0, hd⟩) k x hx)]

private theorem vzero_lemma {ρ : Type*} {e : ρ →₀ ℕ} (h : e.degree = 0) : e = 0 := by
  first
  | exact (Finsupp.degree_eq_zero_iff _).mp h
  | exact Finsupp.degree_eq_zero_iff.mp h

private theorem vmul_lemma_2 {ρ K : Type*} [CommRing K] {P Q : MvPowerSeries ρ K} {m n : ℕ}
    (hP : ∀ e : ρ →₀ ℕ, e.degree < m → coeff e P = 0)
    (hQ : ∀ e : ρ →₀ ℕ, e.degree < n → coeff e Q = 0) :
    ∀ e : ρ →₀ ℕ, e.degree < m + n → coeff e (P * Q) = 0 := by
  classical
  intro e he
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx' : x.1 + x.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have hdeg : (x.1 + x.2).degree = x.1.degree + x.2.degree := by
    first
    | exact Finsupp.degree_add _ _
    | exact map_add _ _ _
  rw [hx'] at hdeg
  by_cases h1 : x.1.degree < m
  · rw [hP _ h1, zero_mul]
  · rw [hQ _ (by omega), mul_zero]

private theorem vpow_lemma_3 {ρ K : Type*} [CommRing K] {A : MvPowerSeries ρ K}
    (hA : constantCoeff A = 0) (k : ℕ) :
    ∀ e : ρ →₀ ℕ, e.degree < k → coeff e (A ^ k) = 0 := by
  induction k with
  | zero => intro e he; omega
  | succ k ih =>
    rw [pow_succ]
    refine vmul_lemma_2 ih ?_
    intro e he
    have h0 : e = 0 := vzero_lemma (by omega)
    rw [h0, coeff_zero_eq_constantCoeff_apply, hA]

private theorem vprod_lemma_4 {ι ρ K : Type*} [CommRing K] {A : ι → MvPowerSeries ρ K}
    (hA : ∀ s, constantCoeff (A s) = 0) (d : ι →₀ ℕ) (S : Finset ι) :
    ∀ e : ρ →₀ ℕ, e.degree < ∑ s ∈ S, d s → coeff e (∏ s ∈ S, A s ^ d s) = 0 := by
  classical
  refine Finset.induction_on S (fun e he => by simp at he) (fun a S ha ih => ?_)
  rw [Finset.prod_insert ha, Finset.sum_insert ha]
  exact vmul_lemma_2 (vpow_lemma_3 (hA a) (d a)) ih

private theorem hs_lemma_5 {ρ τ K : Type*} [CommRing K] [Finite ρ] {a : ρ → MvPowerSeries τ K}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact HasSubst.of_constantCoeff_zero ha
  | exact hasSubst_of_constantCoeff_zero ha

private theorem osub_lemma_6 {ρ τ K : Type*} [CommRing K] [Finite ρ] {a : ρ → MvPowerSeries τ K}
    (ha0 : ∀ s, constantCoeff (a s) = 0) {N : MvPowerSeries ρ K} {m : ℕ}
    (hN : ∀ d : ρ →₀ ℕ, d.degree < m → coeff d N = 0) :
    ∀ e : τ →₀ ℕ, e.degree < m → coeff e (MvPowerSeries.subst a N) = 0 := by
  intro e he
  rw [MvPowerSeries.coeff_subst (hs_lemma_5 ha0) N e]
  refine (finsum_congr fun d => ?_).trans finsum_zero
  by_cases hd : d.degree < m
  · rw [hN d hd, zero_smul]
  · have hz : coeff e (d.prod fun s n => a s ^ n) = 0 :=
      vprod_lemma_4 ha0 d d.support e (by show e.degree < d.degree; omega)
    rw [hz, smul_zero]

theorem limJ_tt_subst {σ τ : Type} [Finite σ] [Finite τ] (k : ℕ) (a : σ → MvPowerSeries τ T)
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ T) :
    truncTotalAlgHom τ T (k + 1) (MvPowerSeries.subst (R := T) (S := T) a f) =
      MvPolynomial.aeval (fun i => truncTotalAlgHom τ T (k + 1) (a i)) (truncTotal (k + 1) f) := by
  have has : HasSubst a := hs_lemma_5 ha
  have hpoly : ∀ P : MvPolynomial σ T,
      truncTotalAlgHom τ T (k + 1) (MvPowerSeries.subst (R := T) (S := T) a (P : MvPowerSeries σ T)) =
        MvPolynomial.aeval (fun i => truncTotalAlgHom τ T (k + 1) (a i)) P := by
    intro P
    induction P using MvPolynomial.induction_on
    next c =>
      rw [MvPolynomial.coe_C, ← MvPowerSeries.coe_substAlgHom has, MvPowerSeries.c_eq_algebraMap,
        AlgHom.commutes, MvPolynomial.aeval_C, MvPowerSeries.truncTotalAlgHom_apply,
        ← MvPowerSeries.c_eq_algebraMap, ← Ideal.Quotient.mk_algebraMap,
        MvPolynomial.algebraMap_eq]
      refine (limJ_mk_eq_iff k _ _).mpr fun x hx => ?_
      classical
      rw [MvPowerSeries.coeff_truncTotal _ hx, MvPolynomial.coeff_C, MvPowerSeries.coeff_C]
      split_ifs with h1 h2 h2 <;>
        first | rfl | (exfalso; exact h2 h1.symm) | (exfalso; exact h1 h2.symm)
    next p q hp hq =>
      rw [MvPolynomial.coe_add, ← MvPowerSeries.coe_substAlgHom has]
      simp only [map_add]
      rw [MvPowerSeries.coe_substAlgHom has, hp, hq]
    next p n hp =>
      rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, ← MvPowerSeries.coe_substAlgHom has]
      simp only [map_mul, MvPowerSeries.substAlgHom_X, MvPolynomial.aeval_X]
      rw [MvPowerSeries.coe_substAlgHom has, hp]
  rw [← hpoly, limJ_tt_eq_iff]
  intro x hx
  rw [← sub_eq_zero, ← map_sub, ← MvPowerSeries.coe_substAlgHom has, ← map_sub,
    MvPowerSeries.coe_substAlgHom has]
  refine osub_lemma_6 ha (fun d hd => ?_) x hx
  rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal _ hd, sub_self]

theorem limJ_substJ_mk {n d : ℕ} (m : ℕ) (φ : Fin d → PS T n d) (hφ : ∀ j, constantCoeff (φ j) = 0)
    (P : MvPolynomial (Fin 1 × Fin d) T) :
    substJ m φ hφ (Ideal.Quotient.mk _ P) = MvPolynomial.aeval (fun q => psJet m (φ q.2)) P :=
  rfl

theorem limJ_psJet_subst {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (k : ℕ) (b : Fin 1 × Fin d → PS T n d)
    (hb : ∀ q, constantCoeff (b q) = 0) (φ : Fin d → PS T n d) (hφ : ∀ j, constantCoeff (φ j) = 0)
    (hbφ : ∀ q, b q = φ q.2) (f : PS T 1 d) :
    psJet k (MvPowerSeries.subst b f) = substJ k φ hφ (psJet k f) := by
  rw [limJ_psJet_eq hn hd, limJ_tt_subst k b hb f]
  have e1 : psJet k f = Ideal.Quotient.mk _ (truncTotal (k + 1) f) := by
    rw [limJ_psJet_eq (n := 1) Nat.one_pos hd, MvPowerSeries.truncTotalAlgHom_apply]
  rw [e1, limJ_substJ_mk]
  have hfun : (fun i => truncTotalAlgHom (Fin n × Fin d) T (k + 1) (b i)) =
      fun q => psJet k (φ q.2) := by
    funext q
    rw [hbφ q, limJ_psJet_eq hn hd]
  rw [hfun]

theorem limJ_psJet_mul {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (k : ℕ) (f g : PS T n d) :
    psJet k (f * g) = psJet k f * psJet k g := by
  rw [limJ_psJet_eq hn hd, limJ_psJet_eq hn hd, limJ_psJet_eq hn hd, map_mul]

theorem limJ_ev_pts {d : ℕ} (g : PS T 2 d) : ev (n := 2) ![pt T d 0, pt T d 1] g = g := by
  have h2 : MvPowerSeries.subst (fun p : Fin 2 × Fin d => (X p : PS T 2 d)) g = g := by
    first
    | exact congrFun MvPowerSeries.subst_self g
    | simp [MvPowerSeries.subst_self]
  refine Eq.trans ?_ h2
  unfold ev
  congr 1
  funext p
  obtain ⟨i, j⟩ := p
  fin_cases i <;> first | rfl | simp [pt]

end Jets

section Limits

variable {O : Type} [CommRing O] (p : ℕ) [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem limJ_mem_smul_top (m : ℕ) (a b : O)
    (h : Ideal.Quotient.mk (Ideal.span {(p : O) ^ (m + 1)}) a = Ideal.Quotient.mk _ b) :
    a ≡ b [SMOD (Ideal.span {(p : O)} ^ m • ⊤ : Submodule O O)] := by
  rw [SModEq.sub_mem]
  have h1 : a - b ∈ Ideal.span {(p : O) ^ (m + 1)} := Ideal.Quotient.eq.mp h
  rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ m)) h1

theorem limJ_unique (a b : O)
    (h : ∀ n, Ideal.Quotient.mk (Ideal.span {(p : O) ^ (n + 1)}) a = Ideal.Quotient.mk _ b) : a = b := by
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : O)})]
  intro n
  exact limJ_mem_smul_top p n a b (h n)

theorem limJ_back (x : ∀ n, O ⧸ Ideal.span {(p : O) ^ (n + 1)})
    (hx : ∀ n, redQ p n (x (n + 1)) = x n) (m : ℕ) :
    ∀ j (a : O), Ideal.Quotient.mk (Ideal.span {(p : O) ^ (m + j + 1)}) a = x (m + j) →
      Ideal.Quotient.mk (Ideal.span {(p : O) ^ (m + 1)}) a = x m := by
  intro j
  induction j with
  | zero =>
    intro a ha
    simpa using ha
  | succ j ih =>
    intro a ha
    apply ih
    have ha' : Ideal.Quotient.mk (Ideal.span {(p : O) ^ (m + j + 1 + 1)}) a = x (m + j + 1) := ha
    rw [← hx (m + j), ← ha']
    first
    | rfl
    | simp [redQ]

theorem limJ_exists (x : ∀ n, O ⧸ Ideal.span {(p : O) ^ (n + 1)})
    (hx : ∀ n, redQ p n (x (n + 1)) = x n) :
    ∃ a : O, ∀ n, Ideal.Quotient.mk (Ideal.span {(p : O) ^ (n + 1)}) a = x n := by
  choose f hf using fun n => Ideal.Quotient.mk_surjective (x n)
  have hdown : ∀ m j, Ideal.Quotient.mk (Ideal.span {(p : O) ^ (m + 1)}) (f (m + j)) = x m :=
    fun m j => limJ_back p x hx m j (f (m + j)) (hf (m + j))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)}) f (fun {m n} hmn => by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmn
    apply limJ_mem_smul_top p m
    rw [hf m, hdown m j])
  refine ⟨L, fun n => ?_⟩
  have h1 := hL (n + 1)
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h1
  rw [← hdown n 1]
  exact (Ideal.Quotient.eq.mpr h1).symm

end Limits

theorem lim_holds : LimSt := by
  intro O _ p _ d F U hd hN hK hZ hM

  set π : ∀ n : ℕ, O →+* O ⧸ Ideal.span {(p : O) ^ (n + 1)} :=
    fun n => Ideal.Quotient.mk (Ideal.span {(p : O) ^ (n + 1)}) with hπ

  choose P hP using fun n k => Ideal.Quotient.mk_surjective (U n k)
  let c : ∀ n : ℕ, (Fin 1 × Fin d →₀ ℕ) → O ⧸ Ideal.span {(p : O) ^ (n + 1)} :=
    fun n μ => (P n μ.degree).coeff μ
  have hck : ∀ n μ k, μ.degree ≤ k → (P n k).coeff μ = c n μ := by
    intro n μ k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      rw [← ih]
      have h1 : (Ideal.Quotient.mk _ (P n k) : JetR _ (Fin 1 × Fin d) k) =
          Ideal.Quotient.mk _ (P n (k + 1)) := by
        rw [hP, ← hK n k, ← hP]
        rfl
      exact ((limJ_mk_eq_iff k _ _).1 h1 μ (by omega)).symm
  have hcn : ∀ n μ, redQ p n (c (n + 1) μ) = c n μ := by
    intro n μ
    have h1 : (Ideal.Quotient.mk _ (MvPolynomial.map (redQ p n) (P (n + 1) μ.degree)) :
        JetR _ (Fin 1 × Fin d) μ.degree) = Ideal.Quotient.mk _ (P n μ.degree) := by
      rw [hP n, ← hN n, ← hP]
      rfl
    have h2 := (limJ_mk_eq_iff _ _ _).1 h1 μ (by omega)
    rw [MvPolynomial.coeff_map] at h2
    exact h2
  choose a ha using fun μ => limJ_exists p (fun n => c n μ) (fun n => hcn n μ)
  let u : PS O 1 d := fun μ => a μ
  have hu : ∀ μ, coeff μ u = a μ := fun μ => rfl
  have hJ : ∀ n k, psJet k (MvPowerSeries.map (π n) u) = U n k := by
    intro n k
    rw [limJ_psJet_eq Nat.one_pos hd, ← hP n k, truncTotalAlgHom_apply, limJ_mk_eq_iff]
    intro μ hμ
    rw [coeff_truncTotal _ hμ, coeff_map, hu, ha μ n, hck n μ k (by omega)]
  refine ⟨u, ⟨?_, ?_⟩, hJ⟩
  ·
    rw [← coeff_zero_eq_constantCoeff_apply, hu]
    apply limJ_unique p
    intro n
    rw [ha 0 n, map_one]
    have h1 : (Ideal.Quotient.mk _ (P n 0) : JetR _ (Fin 1 × Fin d) 0) = Ideal.Quotient.mk _ 1 := by
      rw [map_one, ← hZ n 0, ← hP n 0]
      rfl
    have h2 := (limJ_mk_eq_iff 0 _ _).1 h1 0 (by simp)
    rw [MvPolynomial.coeff_zero_one] at h2
    exact h2
  ·
    have hadd : addOf F.F (pt O (n := 2) d 0) (pt O d 1) = F.F :=
      funext fun i => limJ_ev_pts (F.F i)
    have hbL : ∀ q : Fin 1 × Fin d,
        (![addOf F.F (pt O (n := 2) d 0) (pt O d 1)] : Fin 1 → Pt O 2 d) q.1 q.2 = F.F q.2 := by
      intro q
      rw [Fin.fin_one_eq_zero q.1, hadd]
      rfl
    have hbLc : ∀ q : Fin 1 × Fin d,
        constantCoeff ((![addOf F.F (pt O (n := 2) d 0) (pt O d 1)] : Fin 1 → Pt O 2 d) q.1 q.2) = 0 := by
      intro q; rw [hbL]; exact F.const _
    have hbP : ∀ (i : Fin 2) (q : Fin 1 × Fin d),
        (![pt O (n := 2) d i] : Fin 1 → Pt O 2 d) q.1 q.2 = X (i, q.2) := by
      intro i q
      rw [Fin.fin_one_eq_zero q.1]
      rfl
    have hbPc : ∀ (i : Fin 2) (q : Fin 1 × Fin d),
        constantCoeff ((![pt O (n := 2) d i] : Fin 1 → Pt O 2 d) q.1 q.2) = 0 := by
      intro i q; rw [hbP]; simp
    ext ν
    apply limJ_unique p
    intro n
    rw [← coeff_map, ← coeff_map]
    refine (limJ_tt_eq_iff ν.degree _ _).1 ?_ ν (by omega)
    rw [← limJ_psJet_eq (by omega) hd, ← limJ_psJet_eq (by omega) hd]
    unfold ev
    rw [map_mul, map_subst (hasSubst_of_constantCoeff_zero hbLc), map_subst (hasSubst_of_constantCoeff_zero (hbPc 0)),
      map_subst (hasSubst_of_constantCoeff_zero (hbPc 1)), limJ_psJet_mul (by omega) hd]
    rw [limJ_psJet_subst (by omega) hd _ _ (fun q => by rw [hbL]; exact Fmod_const p F n q.2) (Fmod p F n) (Fmod_const p F n)
        (fun q => by rw [hbL]; rfl),
      limJ_psJet_subst (by omega) hd _ _ (fun q => by rw [hbP, map_X]; simp) (fun j => (MvPowerSeries.X ((0 : Fin 2), j) : PS _ 2 d))
        (fun j => by simp) (fun q => by rw [hbP, map_X]),
      limJ_psJet_subst (by omega) hd _ _ (fun q => by rw [hbP, map_X]; simp) (fun j => (MvPowerSeries.X ((1 : Fin 2), j) : PS _ 2 d))
        (fun j => by simp) (fun q => by rw [hbP, map_X]), hJ]
    exact hM n ν.degree

end ReciprocityTheory.ChartRestriction.G.Pdiv.TL
