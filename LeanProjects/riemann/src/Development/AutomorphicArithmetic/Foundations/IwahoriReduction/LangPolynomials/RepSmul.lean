import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.WdVal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem rs_dl_mul {R : Type} [CommRing R] {f g : PowerSeries R} (hf : IsUnit f) (hg : IsUnit g) :
    dl (f * g) = dl f + dl g := by
  obtain ⟨u, rfl⟩ := hf
  obtain ⟨v, rfl⟩ := hg
  have hu : (u : PowerSeries R) * ↑u⁻¹ = 1 := u.mul_inv
  have hv : (v : PowerSeries R) * ↑v⁻¹ = 1 := v.mul_inv
  have hinv : Ring.inverse ((u : PowerSeries R) * v) = ↑v⁻¹ * ↑u⁻¹ := by
    rw [← Units.val_mul, Ring.inverse_unit, mul_inv_rev, Units.val_mul]
  simp only [dl, dd, Ring.inverse_unit, Derivation.leibniz, smul_eq_mul, hinv]
  linear_combination ((1 + PowerSeries.X) * PowerSeries.derivative R v * ↑v⁻¹) * hu +
    ((1 + PowerSeries.X) * PowerSeries.derivative R u * ↑u⁻¹) * hv

private theorem rs_dl_one {R : Type} [CommRing R] : dl (1 : PowerSeries R) = 0 := by
  simp [dl, dd]

private theorem rs_dl_pow {R : Type} [CommRing R] {f : PowerSeries R} (hf : IsUnit f) (a : ℕ) :
    dl (f ^ a) = (a : PowerSeries R) * dl f := by
  induction a with
  | zero => simp [rs_dl_one]
  | succ a ih => rw [pow_succ, rs_dl_mul (hf.pow a) hf, ih]; push_cast; ring

private theorem rs_dl_prod {R : Type} [CommRing R] {ι : Type} (s : Finset ι) (F : ι → PowerSeries R)
    (hF : ∀ k, IsUnit (F k)) (a : ι → ℕ) :
    IsUnit (∏ k ∈ s, F k ^ a k) ∧ dl (∏ k ∈ s, F k ^ a k) = ∑ k ∈ s, (a k : PowerSeries R) * dl (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rs_dl_one]
  | insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk]
    have hk' : IsUnit (F k ^ a k) := (hF k).pow _
    refine ⟨hk'.mul ih.1, ?_⟩
    rw [rs_dl_mul hk' ih.1, ih.2, rs_dl_pow (hF k)]

private theorem rs_alg_le {l : ℕ} [Fact l.Prime] (z : ℤ_[l]) : ‖algebraMap ℤ_[l] (PadicAlgCl l) z‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends l]
  exact PadicInt.norm_le_one z

private theorem rs_sum_le {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] (e : ι → PadicAlgCl l) (he : ∀ i, ‖e i‖ ≤ 1)
    (z : ι → ℤ_[l]) : ‖∑ i, e i * algebraMap ℤ_[l] (PadicAlgCl l) (z i)‖ ≤ 1 := by
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (he i) (norm_nonneg _) (rs_alg_le _)

private theorem rs_mat {l : ℕ} [Fact l.Prime] {c : Coef l} (β : Bas c) (b : c.O) (k : Fin β.d) :
    (b : PadicAlgCl l) * β.val k = ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.mat b i k) := by
  simp only [Bas.val, Bas.mat, Algebra.leftMulMatrix_eq_repr_mul]
  conv_lhs => rw [← MulMemClass.coe_mul, ← β.e.sum_repr (b * β.e k)]
  simp [Algebra.smul_def, mul_comm]

private theorem rs_b_le {l : ℕ} [Fact l.Prime] {c : Coef l} (β : Bas c) (he : ∀ i, ‖β.val i‖ ≤ 1) (b : c.O) :
    ‖(b : PadicAlgCl l)‖ ≤ 1 := by
  have h : (b : PadicAlgCl l) = ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr b i) := by
    conv_lhs => rw [← β.e.sum_repr b]
    simp [Bas.val, Algebra.smul_def, mul_comm]
  rw [h]
  exact rs_sum_le _ he _

private theorem rs_cg {l : ℕ} [Fact l.Prime] {c : Coef l} (β : Bas c) (he : ∀ i, ‖β.val i‖ ≤ 1) (b : c.O) (n : ℕ)
    (z : Qbar l) (x y : Fin β.d → ℕ) (hz : Cg n z (∑ i, β.val i * (x i : Qbar l)))
    (hy : ∀ i, ∃ w : ℤ_[l], ∑ k, β.mat b i k * (x k : ℤ_[l]) = y i + (l : ℤ_[l]) ^ n * w) :
    Cg n ((b : PadicAlgCl l) * z) (∑ i, β.val i * (y i : Qbar l)) := by
  choose w hw using hy
  unfold Cg at hz ⊢
  have hb := rs_b_le β he b
  have hsum : (b : PadicAlgCl l) * ∑ k, β.val k * (x k : Qbar l)
      = ∑ i, β.val i * (y i : Qbar l) + (l : PadicAlgCl l) ^ n * ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (w i) := by
    calc (b : PadicAlgCl l) * ∑ k, β.val k * (x k : Qbar l)
        = ∑ k, ((b : PadicAlgCl l) * β.val k) * (x k : Qbar l) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = ∑ k, ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.mat b i k) * (x k : Qbar l) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [rs_mat β b k, Finset.sum_mul]
      _ = ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (∑ k, β.mat b i k * (x k : ℤ_[l])) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul, map_natCast]
          ring
      _ = _ := by
          simp only [hw, map_add, map_mul, map_pow, map_natCast, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
  have key : (b : PadicAlgCl l) * z - ∑ i, β.val i * (y i : Qbar l)
      = (b : PadicAlgCl l) * (z - ∑ i, β.val i * (x i : Qbar l))
        + (l : PadicAlgCl l) ^ n * ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (w i) := by
    rw [mul_sub, hsum]
    ring
  rw [key]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    calc ‖(b : PadicAlgCl l)‖ * ‖z - ∑ i, β.val i * (x i : Qbar l)‖ ≤ 1 * ‖(l : PadicAlgCl l) ^ n‖ :=
          mul_le_mul hb hz (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · rw [norm_mul]
    calc _ ≤ ‖(l : PadicAlgCl l) ^ n‖ * 1 := mul_le_mul_of_nonneg_left (rs_sum_le _ he _) (norm_nonneg _)
      _ = _ := mul_one _

private theorem rs_unit {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {ι : Type} [Fintype ι] (u : ι → Ω)
    (hu : ∀ i, u i ∈ A ∧ u i ≠ 0 ∧ (u i)⁻¹ ∈ A) (a : ι → ℕ) :
    ∏ k, u k ^ a k ∈ A ∧ ∏ k, u k ^ a k ≠ 0 ∧ (∏ k, u k ^ a k)⁻¹ ∈ A := by
  classical
  suffices h : ∀ s : Finset ι, ∏ k ∈ s, u k ^ a k ∈ A ∧ ∏ k ∈ s, u k ^ a k ≠ 0 ∧ (∏ k ∈ s, u k ^ a k)⁻¹ ∈ A from h _
  intro s
  induction s using Finset.induction_on with
  | empty => simp [A.one_mem]
  | insert k s hk ih =>
    rw [Finset.prod_insert hk]
    obtain ⟨h1, h2, h3⟩ := hu k
    refine ⟨mul_mem (pow_mem h1 _) ih.1, mul_ne_zero (pow_ne_zero _ h2) ih.2.1, ?_⟩
    rw [mul_inv, ← inv_pow]
    exact mul_mem (pow_mem h3 _) ih.2.2

private theorem rs_kum {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {z : Ω} (hz : z ^ l ^ n = 1)
    (s : G ℚ Ω) {ι : Type} [Fintype ι] (u : ι → Ω) (x : ι → ZMod (l ^ n)) (hx : ∀ k, KumVal n z (u k) s (x k)) (a : ι → ℕ) :
    KumVal (l := l) n z (∏ k, u k ^ a k) s ((∑ k, a k * (x k).val : ℕ) : ZMod (l ^ n)) := by
  classical
  choose v hv using hx
  refine ⟨∏ k, v k ^ a k, ?_, ?_⟩
  · rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_mul, mul_comm (a k), pow_mul, (hv k).1]
  · rw [map_prod]
    have hmod : z ^ (((∑ k, a k * (x k).val : ℕ) : ZMod (l ^ n))).val = z ^ (∑ k, a k * (x k).val) := by
      rw [ZMod.val_natCast]
      conv_rhs => rw [← Nat.mod_add_div (∑ k, a k * (x k).val) (l ^ n), pow_add, pow_mul, hz, one_pow, mul_one]
    rw [hmod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_pow, (hv k).2, mul_pow, ← pow_mul, mul_comm (a k)]

theorem UpperTheory.Kd.C7.pRepSmul :
    UpperTheory.Kd.C7.SRepSmul := by
  intro l hl hl2 Ω _ _ _ A hA jj Φ c β ζ hζ Z D b hRep
  classical
  haveI : IsAdicComplete (Ideal.span {(l : Φ.R)}) Φ.R := Φ.fl.complete
  unfold Rep at hRep ⊢
  obtain ⟨c₁, m₁, hR⟩ := hRep
  refine ⟨c₁, max m₁ 1, fun m hm => ?_⟩
  have hm1 : m₁ ≤ m := le_trans (le_max_left _ _) hm
  have hm0 : 1 ≤ m := le_trans (le_max_right _ _) hm
  obtain ⟨P, hB, hLC⟩ := hR m hm1
  set n := m - c₁ with hn
  let a : Fin β.d → Fin β.d → ℕ := fun i k => PadicInt.appr (β.mat b i k) n
  have ha : ∀ i k, ∃ t : ℤ_[l], β.mat b i k = (a i k : ℤ_[l]) + (l : ℤ_[l]) ^ n * t := by
    intro i k
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec n (β.mat b i k))
    exact ⟨t, by linear_combination (-1 : ℤ_[l]) * ht⟩
  choose t ht using ha
  let P' : Fin β.d → Polynomial (R0 A) := fun i => ∏ k, P k ^ a i k
  unfold BPres KumPres at hB ⊢
  obtain ⟨hprim, hnm, hunits, hval, hK⟩ := hB
  have hpv : ∀ i, pv (P' i) (ζ m) = ∏ k, pv (P k) (ζ m) ^ a i k := by
    intro i
    simp only [P', pv, Polynomial.eval₂_finset_prod, Polynomial.eval₂_pow]
  refine ⟨P', ⟨hprim, hnm, fun i => ?_, hval, fun s hs hcyc hfix => ?_⟩, fun i => ?_⟩
  · beta_reduce
    rw [hpv i]
    exact rs_unit A _ hunits (a i)
  · obtain ⟨k, hk, hcg⟩ := hK s hs hcyc hfix
    refine ⟨fun i => ((∑ k', a i k' * (k k').val : ℕ) : ZMod (l ^ n)), fun i => ?_, ?_⟩
    · beta_reduce
      rw [hpv i]
      exact rs_kum hprim.pow_eq_one s _ k hk (a i)
    · refine rs_cg β hval b n _ (fun k' => (k k').val)
        (fun i => (((∑ k', a i k' * (k k').val : ℕ) : ZMod (l ^ n))).val) hcg fun i => ?_
      beta_reduce
      refine ⟨((∑ k', a i k' * (k k').val) / l ^ n : ℕ) + ∑ k', t i k' * ((k k').val : ℤ_[l]), ?_⟩
      have hcast : ((∑ k', a i k' * (k k').val : ℕ) : ℤ_[l])
          = ((∑ k', a i k' * (k k').val) % l ^ n : ℕ) + (l : ℤ_[l]) ^ n * ((∑ k', a i k' * (k k').val) / l ^ n : ℕ) := by
        conv_lhs => rw [← Nat.mod_add_div (∑ k', a i k' * (k k').val) (l ^ n)]
        push_cast
        ring
      have e1 : ∑ k', β.mat b i k' * ((k k').val : ℤ_[l])
          = ((∑ k', a i k' * (k k').val : ℕ) : ℤ_[l]) + (l : ℤ_[l]) ^ n * ∑ k', t i k' * ((k k').val : ℤ_[l]) := by
        push_cast
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k' _ => ?_
        rw [ht i k']
        ring
      rw [e1, ZMod.val_natCast]
      linear_combination hcast
  · let ψ : Polynomial (R0 A) →+* PowerSeries Φ.R :=
      (Polynomial.eval₂RingHom PowerSeries.C (1 + PowerSeries.X)).comp (Polynomial.mapRingHom Φ.i0)
    have hψ : ∀ F, Φ.ser F = ψ F := fun F => rfl
    have hunit : ∀ k, IsUnit (Φ.ser (P k)) := fun k =>
      (pWD l hl2 Ω A hA jj Φ ζ hζ m hm0 (P k)).2 (hunits k)
    have hser : Φ.ser (P' i) = ∏ k, Φ.ser (P k) ^ a i k := by
      simp only [hψ, P', map_prod, map_pow]
    have hfixR : ∀ (f : Φ.R →+* Φ.R) (z : ℤ_[l]), f (algebraMap ℤ_[l] Φ.R z) = algebraMap ℤ_[l] Φ.R z :=
      fun f z => RingHom.congr_fun (padicHom_ext l (f.comp (algebraMap ℤ_[l] Φ.R)) (algebraMap ℤ_[l] Φ.R)) z
    have htw : Φ.tw m (Φ.act (β.mat b) D i)
        = ∑ k, PowerSeries.C (algebraMap ℤ_[l] Φ.R (β.mat b i k)) * Φ.tw m (D k) := by
      simp only [Fr.tw, Fr.act, map_sum, map_mul, PowerSeries.map_C, hfixR]
    unfold LC at hLC ⊢
    rw [htw, hser, (rs_dl_prod Finset.univ (fun k => Φ.ser (P k)) hunit (a i)).2, map_sum, map_sum,
      ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun k _ => ?_
    have hdiff : ev Φ.R l m (PowerSeries.C (algebraMap ℤ_[l] Φ.R (β.mat b i k)))
        - ev Φ.R l m ((a i k : ℕ) : PowerSeries Φ.R) ∈ Ideal.span {(l : lev Φ.R l m) ^ n} := by
      have e : PowerSeries.C (algebraMap ℤ_[l] Φ.R (β.mat b i k)) - ((a i k : ℕ) : PowerSeries Φ.R)
          = (l : PowerSeries Φ.R) ^ n * PowerSeries.C (algebraMap ℤ_[l] Φ.R (t i k)) := by
        rw [ht i k]
        simp only [map_add, map_mul, map_pow, map_natCast]
        ring
      rw [← map_sub, e, map_mul, map_pow, map_natCast]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [map_mul, map_mul]
    have e2 : ev Φ.R l m (PowerSeries.C (algebraMap ℤ_[l] Φ.R (β.mat b i k))) * ev Φ.R l m (Φ.tw m (D k))
        - ev Φ.R l m ((a i k : ℕ) : PowerSeries Φ.R) * ev Φ.R l m (dl (Φ.ser (P k)))
        = ev Φ.R l m (PowerSeries.C (algebraMap ℤ_[l] Φ.R (β.mat b i k)))
            * (ev Φ.R l m (Φ.tw m (D k)) - ev Φ.R l m (dl (Φ.ser (P k))))
          + (ev Φ.R l m (PowerSeries.C (algebraMap ℤ_[l] Φ.R (β.mat b i k)))
            - ev Φ.R l m ((a i k : ℕ) : PowerSeries Φ.R)) * ev Φ.R l m (dl (Φ.ser (P k))) := by
      ring
    rw [e2]
    exact add_mem (Ideal.mul_mem_left _ _ (hLC k)) (Ideal.mul_mem_right _ _ hdiff)
