import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OneAddXPowSubOneMem
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PowSubOneMem
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem pow_sub_one_mem {S : Type} [CommRing S] (J : Ideal S) (p : ℕ) (hp : p.Prime) (hpJ : (p : S) ∈ J)
    (x : S) (hx : x - 1 ∈ J) (j : ℕ) : x ^ (p ^ j) - 1 ∈ J ^ (j + 1) :=
  _root_.UpperTheory.Reformulated.B.Qf4.pow_sub_one_mem J p hp hpJ x hx j

private theorem pow_sub_pow_mem {S : Type} [CommRing S] (J : Ideal S) (x y : S) (h : x - y ∈ J) (n : ℕ) :
    x ^ n - y ^ n ∈ J := by
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow x y n
  rw [hc]; exact Ideal.mul_mem_right _ _ h

private theorem prod_limit {S : Type} [CommRing S] (J : Ideal S) [IsAdicComplete J S] (y : ℕ → S) (c : ℕ)
    (hy1 : ∀ k, y k - 1 ∈ J) (hy : ∀ k, y k - 1 ∈ J ^ (k - c)) :
    ∃ W : S, W - 1 ∈ J ∧ ∀ n K, n + c ≤ K → W - ∏ k ∈ Finset.range K, y k ∈ J ^ n := by
  have h1 : ∀ K, ∏ k ∈ Finset.range K, y k - 1 ∈ J := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.prod_range_succ]
      have e : (∏ k ∈ Finset.range K, y k) * y K - 1 = (∏ k ∈ Finset.range K, y k) * (y K - 1) + (∏ k ∈ Finset.range K, y k - 1) := by ring
      rw [e]; exact add_mem (Ideal.mul_mem_left _ _ (hy1 K)) ih
  have h2 : ∀ n K, n + c ≤ K → ∏ k ∈ Finset.range K, y k - ∏ k ∈ Finset.range (n + c), y k ∈ J ^ n := by
    intro n K hK
    induction K, hK using Nat.le_induction with
    | base => simp
    | succ K hK ih =>
      rw [Finset.prod_range_succ]
      have e : (∏ k ∈ Finset.range K, y k) * y K - ∏ k ∈ Finset.range (n + c), y k
          = (∏ k ∈ Finset.range K, y k) * (y K - 1) + (∏ k ∈ Finset.range K, y k - ∏ k ∈ Finset.range (n + c), y k) := by ring
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by omega) (hy K))) ih
  obtain ⟨W, hW⟩ := IsPrecomplete.prec' (I := J) (fun n => ∏ k ∈ Finset.range (n + c), y k) (fun {a b} hab => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub]
    exact neg_mem (h2 a (b + c) (by omega)))
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hW
  refine ⟨W, ?_, fun n K hK => ?_⟩
  · have := sub_mem (h1 (1 + c)) (show _ ∈ J by simpa using hW 1)
    convert this using 1; ring
  · have := neg_mem (add_mem (h2 n K hK) (hW n))
    convert this using 1; ring

private theorem conv {S : Type} [CommRing S] (J : Ideal S) [IsAdicComplete J S] (p : ℕ) (hp : p.Prime) (hpJ : (p : S) ∈ J)
    (N : S →* S) (E : ℕ → Ideal S) (Q : ℕ → ℕ → Ideal S)
    (hNJ : ∀ x, x - 1 ∈ J → N x - 1 ∈ J)
    (hNE : ∀ r, 1 ≤ r → ∀ a b, a - b ∈ E (r + 1) → N a - N b ∈ E r)
    (hNQ : ∀ r, 1 ≤ r → ∀ n a b, a - b ∈ Q (r + 1) n → N a - N b ∈ Q r n)
    (hEQ : ∀ r n, E r ≤ Q r n) (hJQ : ∀ r n, ∃ K, J ^ K ≤ Q r n)
    (hsep : ∀ r x, (∀ n, x ∈ Q r n) → x ∈ E r)
    (g w : ℕ → S) (c : ℕ) (hw : ∀ r, w r - 1 ∈ J)
    (hg : ∀ r, 1 ≤ r → N (g (r + 1)) - g r * w r ^ p ^ (r - c) ∈ E r) :
    ∃ W : ℕ → S, (∀ r, W r - 1 ∈ J) ∧
      ∀ r, 1 ≤ r → N (g (r + 1) * W (r + 1) ^ p ^ (r + 1 - c)) - g r * W r ^ p ^ (r - c) ∈ E r := by
  have hit : ∀ K r, 1 ≤ r → ∀ a b, a - b ∈ E (r + K) → N^[K] a - N^[K] b ∈ E r := by
    intro K
    induction K with
    | zero => intro r _ a b h; exact h
    | succ K ih =>
      intro r hr a b h
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih r hr _ _ (hNE (r + K) (by omega) a b h)
  have hitJ : ∀ K x, x - 1 ∈ J → N^[K] x - 1 ∈ J := by
    intro K
    induction K with
    | zero => intro x h; exact h
    | succ K ih => intro x h; rw [Function.iterate_succ_apply]; exact ih _ (hNJ x h)
  set y : ℕ → ℕ → S := fun r k => (N^[k] (w (r + k))) ^ p ^ ((r + k - c) - (r - c)) with hy
  have hex : ∀ r, ∃ W : S, W - 1 ∈ J ∧ ∀ n K, n + c ≤ K → W - ∏ k ∈ Finset.range K, y r k ∈ J ^ n := by
    intro r
    have h0 := fun k => pow_sub_one_mem J p hp hpJ _ (hitJ k _ (hw (r + k))) ((r + k - c) - (r - c))
    exact prod_limit J (y r) c (fun k => Ideal.pow_le_self (by omega) (h0 k))
      (fun k => Ideal.pow_le_pow_right (by omega) (h0 k))
  choose W hW1 hW2 using hex
  have key : ∀ r, 1 ≤ r → ∀ K, N^[K] (g (r + K)) - g r * (∏ k ∈ Finset.range K, y r k) ^ p ^ (r - c) ∈ E r := by
    intro r hr K
    induction K with
    | zero => simp
    | succ K ih =>
      have h1 := hit K r hr _ _ (hg (r + K) (by omega))
      rw [iterate_map_mul, iterate_map_pow, ← Function.iterate_succ_apply] at h1
      have e : (N^[K] (w (r + K))) ^ p ^ (r + K - c) = (y r K) ^ p ^ (r - c) := by
        rw [hy]; dsimp only
        rw [← pow_mul, ← pow_add]; congr 2; omega
      rw [e] at h1
      rw [Finset.prod_range_succ, mul_pow]
      have := add_mem h1 (Ideal.mul_mem_right ((y r K) ^ p ^ (r - c)) _ ih)
      convert this using 1
      simp only [Nat.succ_eq_add_one, add_assoc]; ring
  have app : ∀ r, 1 ≤ r → ∀ n, ∃ K0, ∀ K, K0 ≤ K → N^[K] (g (r + K)) - g r * W r ^ p ^ (r - c) ∈ Q r n := by
    intro r hr n
    obtain ⟨L, hL⟩ := hJQ r n
    refine ⟨L + c, fun K hK => ?_⟩
    have h1 := hEQ r n (key r hr K)
    have h2 := Ideal.mul_mem_left _ (g r) (pow_sub_pow_mem _ _ _ (hL (hW2 r L K hK)) (p ^ (r - c)))
    convert sub_mem h1 h2 using 1; ring
  refine ⟨W, hW1, fun r hr => hsep r _ fun n => ?_⟩
  obtain ⟨K1, h1⟩ := app r hr n
  obtain ⟨K2, h2⟩ := app (r + 1) (by omega) n
  have h3 := hNQ r hr n _ _ (h2 (K1 + K2) (by omega))
  have h4 := h1 (K1 + K2 + 1) (by omega)
  rw [Function.iterate_succ_apply', show r + (K1 + K2 + 1) = r + 1 + (K1 + K2) by omega] at h4
  convert sub_mem h4 h3 using 1; ring

private theorem norm_congr {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (a : A) (x z : B) :
    Algebra.norm A (x + algebraMap A B a * z) - Algebra.norm A x ∈ Ideal.span {a} := by
  classical
  by_cases h : ∃ s : Finset B, Nonempty (Module.Basis s A B)
  · obtain ⟨s, ⟨b⟩⟩ := h
    rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b, ← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    rw [← Algebra.smul_def, map_add, map_smul]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul]
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self a), zero_mul, add_zero]
  · rw [Algebra.norm_eq_one_of_not_exists_basis A h, Algebra.norm_eq_one_of_not_exists_basis A h, sub_self]
    exact zero_mem _

private theorem sub_one_mem_of_pow {S : Type} [CommRing S] (J : Ideal S) (hJ : J.IsPrime) (p : ℕ) (hp : p.Prime)
    (hpJ : (p : S) ∈ J) (x : S) (k : ℕ) (hx : x ^ p ^ k - 1 ∈ J) : x - 1 ∈ J := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (x - 1) 1 k
  rw [sub_add_cancel, one_pow] at hr
  refine hJ.mem_of_pow_mem (p ^ k) ?_
  have := sub_mem hx (Ideal.mul_mem_right ((x - 1) * r) _ hpJ)
  convert this using 1
  rw [hr]; ring

private theorem root_mod {R : Type} [CommRing R] (p : ℕ) (hperf : ∀ x : R, ∃ y : R, y ^ p - x ∈ Ideal.span {(p : R)})
    (m : ℕ) (x : R) : ∃ y : R, y ^ p ^ m - x ∈ Ideal.span {(p : R)} := by
  induction m generalizing x with
  | zero => exact ⟨x, by simp⟩
  | succ m ih =>
    obtain ⟨y, hy⟩ := hperf x
    obtain ⟨z, hz⟩ := ih y
    refine ⟨z, ?_⟩
    have := add_mem (pow_sub_pow_mem _ _ _ hz p) hy
    rw [pow_succ, pow_mul]
    convert this using 1; ring

private noncomputable def colNm (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] : PowerSeries R →* PowerSeries R :=
  letI := (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
  Algebra.norm (PowerSeries R)

private theorem colNm_apply {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] (h : PowerSeries R) :
    colNm R p h = normOp p h := rfl

private theorem nrm_congr {R : Type} [CommRing R] (p m n : ℕ) [Fact p.Prime] (hm : 1 ≤ m) (x y : lev R p (m + 1))
    (h : x - y ∈ Ideal.span {(p : lev R p (m + 1)) ^ n}) :
    nrm p m hm x - nrm p m hm y ∈ Ideal.span {(p : lev R p m) ^ n} := by
  letI := (up (R := R) p m hm).toAlgebra
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  have := norm_congr ((p : lev R p m) ^ n) y z
  rw [map_pow, map_natCast, mul_comm, hz, add_sub_cancel] at this
  exact this

private theorem cyc_mem (R : Type) [CommRing R] (p n : ℕ) [Fact p.Prime] :
    PowerSeries.constantCoeff (GlobalTheory.Col.cyc R p (n + 1)) ∈ Ideal.span {(p : R)} := by
  unfold GlobalTheory.Col.cyc
  rw [Polynomial.hom_eval₂]
  have h1 : (PowerSeries.constantCoeff (R := R)).comp (PowerSeries.C (R := R)) = RingHom.id R := by ext a; simp
  rw [h1, map_add, map_one, PowerSeries.constantCoeff_X, add_zero, Polynomial.eval₂_id,
    Polynomial.eval_one_cyclotomic_prime_pow]
  exact Ideal.subset_span rfl

private theorem all_levels (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R) (hF : FrobLift R p σ)
    (g : ℕ → PowerSeries R) (c : ℕ) (hgu : ∀ m, IsUnit (g m))
    (hg : ∀ m, 1 ≤ m → ∃ w : PowerSeries R, IsUnit w ∧
      ev R p m (normOp p (g (m + 1))) = ev R p m (g m * w ^ p ^ (m - c))) :
    ∃ f : PowerSeries R, IsUnit f ∧ ∀ m, 1 ≤ m → ∃ w : PowerSeries R, IsUnit w ∧
      ev R p m (PowerSeries.map (((σ.symm : R ≃+* R) : R →+* R) ^ m) f) = ev R p m (g m * w ^ p ^ (m - c)) := by
  have hR := hF.complete
  haveI : IsAdicComplete (Ideal.span {(p : R)}) R := hF.complete
  haveI : IsAdicComplete ((Ideal.span {(p : R)}).comap (PowerSeries.constantCoeff (R := R))) (PowerSeries R) :=
    GlobalTheory.ChartRing.isAdicComplete_comap_constantCoeff _
  set J : Ideal (PowerSeries R) := (Ideal.span {(p : R)}).comap (PowerSeries.constantCoeff (R := R)) with hJ
  have hJp : J.IsPrime := by
    haveI : (Ideal.span {(p : R)}).IsPrime := (Ideal.span_singleton_prime hF.prime.ne_zero).2 hF.prime
    exact Ideal.comap_isPrime _ _
  have hpJ : (p : PowerSeries R) ∈ J := by
    rw [hJ, Ideal.mem_comap, map_natCast]; exact Ideal.subset_span rfl
  have hun : ∀ x : PowerSeries R, x - 1 ∈ J → IsUnit x := fun x hx => by
    simpa using Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot J hx) 1
  have hNJ : ∀ x, x - 1 ∈ J → colNm R p x - 1 ∈ J := by
    intro x hx
    obtain ⟨r, hr⟩ := GlobalTheory.T.normOp_eq_smap_add_mul R p σ hF x
    have h1 : smap σ (x - 1) ∈ J := by
      rw [hJ, Ideal.mem_comap, Ideal.mem_span_singleton'] at hx ⊢
      obtain ⟨d, hd⟩ := hx
      refine ⟨σ d, ?_⟩
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, ← hd, map_mul, map_natCast]
      rfl
    rw [colNm_apply, hr]
    rw [map_sub, map_one] at h1
    convert add_mem h1 (Ideal.mul_mem_right r _ hpJ) using 1; ring

  have hnorm : ∀ m, ∃ a : (PowerSeries R)ˣ, g m * (a : PowerSeries R) ^ p ^ m - 1 ∈ J := by
    intro m
    obtain ⟨v, hv⟩ := (hgu m).exists_right_inv
    obtain ⟨y, hy⟩ := root_mod p hF.perfect m (PowerSeries.constantCoeff v)
    have h1 : g m * (PowerSeries.C y) ^ p ^ m - 1 ∈ J := by
      rw [← hv, ← mul_sub]
      refine Ideal.mul_mem_left _ _ ?_
      rw [hJ, Ideal.mem_comap, map_sub, map_pow, PowerSeries.constantCoeff_C]
      exact hy
    have h2 : IsUnit (PowerSeries.C y : PowerSeries R) :=
      (isUnit_pow_iff (pow_pos hp.out.pos m).ne').1 (isUnit_of_mul_isUnit_right (hun _ h1))
    exact ⟨h2.unit, h1⟩
  choose a ha using hnorm
  set G : ℕ → PowerSeries R := fun m => g m * (a m : PowerSeries R) ^ p ^ m with hG
  have hw : ∀ m, ∃ w : PowerSeries R, w - 1 ∈ J ∧
      (1 ≤ m → colNm R p (G (m + 1)) - G m * w ^ p ^ (m - c) ∈ Ideal.span {GlobalTheory.Col.cyc R p m}) := by
    intro m
    rcases m with _ | m
    · exact ⟨1, by simp, fun h => absurd h (by omega)⟩
    obtain ⟨w, -, hw⟩ := hg (m + 1) (by omega)
    rw [Ideal.Quotient.eq, ← colNm_apply] at hw
    obtain ⟨d, hd⟩ : ∃ d, m + 1 = (m + 1 - c) + d := ⟨m + 1 - (m + 1 - c), by omega⟩
    set k := m + 1 - c
    set w' : PowerSeries R := w * (colNm R p (a (m + 1 + 1))) ^ p ^ (d + 1) * ((a (m + 1))⁻¹ : (PowerSeries R)ˣ) ^ p ^ d
    have h1 : colNm R p (G (m + 1 + 1)) - G (m + 1) * w' ^ p ^ k ∈ Ideal.span {GlobalTheory.Col.cyc R p (m + 1)} := by
      have e1 : G (m + 1) * w' ^ p ^ k = g (m + 1) * w ^ p ^ k * (colNm R p (a (m + 1 + 1))) ^ p ^ (m + 1 + 1) := by
        have e2 : ((a (m + 1) : PowerSeries R)) ^ p ^ (m + 1) * ((a (m + 1))⁻¹ : (PowerSeries R)ˣ) ^ p ^ (m + 1) = 1 := by
          rw [← mul_pow, Units.mul_inv, one_pow]
        simp only [hG, w', mul_pow, ← pow_mul, ← pow_add]
        rw [show d + 1 + k = m + 1 + 1 by omega, show d + k = m + 1 by omega]
        linear_combination (g (m + 1) * w ^ p ^ k * (colNm R p (a (m + 1 + 1))) ^ p ^ (m + 1 + 1)) * e2
      rw [e1]
      simp only [hG, map_mul, map_pow]
      rw [← sub_mul]
      exact Ideal.mul_mem_right _ _ hw
    refine ⟨w', sub_one_mem_of_pow J hJp p hp.out hpJ w' k ?_, fun _ => h1⟩
    have h2 : colNm R p (G (m + 1 + 1)) - G (m + 1) * w' ^ p ^ k ∈ J :=
      ((Ideal.span_singleton_le_iff_mem J).2 (Ideal.mem_comap.2 (cyc_mem R p m))) h1
    have h3 := hNJ _ (ha (m + 1 + 1))
    have h4 := Ideal.mul_mem_right (w' ^ p ^ k) _ (ha (m + 1))
    convert sub_mem (sub_mem h3 h2) h4 using 1
    simp only [hG]; ring
  choose w hw1 hw2 using hw
  obtain ⟨W, hW1, hW2⟩ := conv J p hp.out hpJ (colNm R p) (fun r => Ideal.span {GlobalTheory.Col.cyc R p r})
    (fun r n => (Ideal.span {(p : lev R p r) ^ n}).comap (ev R p r)) hNJ
    (fun r hr x y h => by
      rw [← Ideal.Quotient.eq] at h ⊢
      rw [colNm_apply, colNm_apply, GlobalTheory.T.ev_normOp_eq_nrm_ev_succ R p r hr hR, GlobalTheory.T.ev_normOp_eq_nrm_ev_succ R p r hr hR, h])
    (fun r hr n x y h => by
      rw [Ideal.mem_comap, map_sub] at h ⊢
      rw [colNm_apply, colNm_apply, GlobalTheory.T.ev_normOp_eq_nrm_ev_succ R p r hr hR, GlobalTheory.T.ev_normOp_eq_nrm_ev_succ R p r hr hR]
      exact nrm_congr p r n hr _ _ h)
    (fun r n x hx => by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]; exact zero_mem _)
    (fun r n => ⟨p ^ r * n, fun x hx => by
      obtain ⟨y, hy⟩ := GlobalTheory.ColEx.ev_of_mem_pow R p r n x hx
      rw [Ideal.mem_comap, hy, map_mul, map_pow, map_natCast]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)⟩)
    (fun r x hx => by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      refine GlobalTheory.ColEx.lev_sep R p r hR _ fun n => ?_
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 (hx n))
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨y, by rw [← hz, map_mul, map_pow, map_natCast, mul_comm]⟩)
    G w c hw1 hw2
  have hU : ∀ r, IsUnit (ev R p r (G r * W r ^ p ^ (r - c))) := fun r =>
    ((hun _ (ha r)).mul ((hun _ (hW1 r)).pow _)).map _
  obtain ⟨f, hf⟩ := GlobalTheory.Col.exists_coleman_series R p σ hF (fun m => (hU (m + 1)).unit) (fun m => by
    rw [IsUnit.unit_spec, IsUnit.unit_spec, ← GlobalTheory.T.ev_normOp_eq_nrm_ev_succ R p (m + 1) _ hR, Ideal.Quotient.eq]
    exact hW2 (m + 1) (by omega))
  refine ⟨f, f.isUnit, fun m hm => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine ⟨(a (m + 1) : PowerSeries R) ^ p ^ (m + 1 - (m + 1 - c)) * W (m + 1),
    ((a (m + 1)).isUnit.pow _).mul (hun _ (hW1 _)), ?_⟩
  rw [hf m, IsUnit.unit_spec, mul_pow, ← pow_mul, ← pow_add, show m + 1 - (m + 1 - c) + (m + 1 - c) = m + 1 by omega,
    ← mul_assoc]

theorem UpperTheory.Kd.C7.pExact :
    UpperTheory.Kd.C7.SExact := by
  intro R _ p hp σ hF _ g c m₀ hgu hg
  obtain ⟨f, hfu, hf⟩ := all_levels R p σ hF (fun m => (colNm R p)^[m₀ - m] (g (max m m₀))) c
    (fun m => by
      generalize m₀ - m = k
      induction k with
      | zero => exact hgu _ (le_max_right _ _)
      | succ k ih => rw [Function.iterate_succ_apply']; exact ih.map _)
    (fun m hm => by
      rcases le_or_gt m₀ m with h | h
      · obtain ⟨w, hwu, hw⟩ := hg m hm h
        refine ⟨w, hwu, ?_⟩
        rw [show m₀ - (m + 1) = 0 by omega, show m₀ - m = 0 by omega, max_eq_left h, max_eq_left (by omega : m₀ ≤ m + 1),
          Function.iterate_zero_apply, Function.iterate_zero_apply, GlobalTheory.T.ev_normOp_eq_nrm_ev_succ R p m hm hF.complete, hw]
      · refine ⟨1, isUnit_one, ?_⟩
        rw [one_pow, mul_one, show m₀ - m = (m₀ - (m + 1)) + 1 by omega, Function.iterate_succ_apply',
          max_eq_right h.le, max_eq_right (by omega : m + 1 ≤ m₀), colNm_apply])
  refine ⟨f, hfu, fun m hm h N => ?_⟩
  obtain ⟨w, hwu, hw⟩ := hf m hm
  refine ⟨w, hwu, ?_⟩
  rw [show m₀ - m = 0 by omega, max_eq_left h, Function.iterate_zero_apply] at hw
  unfold LC
  rw [hw, sub_self]
  exact zero_mem _
