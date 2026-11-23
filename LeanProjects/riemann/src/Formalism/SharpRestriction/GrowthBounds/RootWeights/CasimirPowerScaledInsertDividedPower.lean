import Formalism.SharpRestriction.GrowthBounds.RootWeights.DegreeZeroWeightsBounded

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section Alg

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def singleConjugation (E : GLOps n K V) (c i : Fin n) : Module.End K (Module.End K V) :=
  (LinearMap.mulLeft K (E c i)).comp (LinearMap.mulRight K (E i c))

theorem singleConjugation_apply (E : GLOps n K V) (c i : Fin n) (X : Module.End K V) :
    singleConjugation E c i X = E c i * (X * E i c) := rfl

theorem singleConjugation_pow_apply (E : GLOps n K V) (c i : Fin n) (k : ℕ) (X : Module.End K V) :
    ((singleConjugation E c i) ^ k) X = (E c i) ^ k * (X * (E i c) ^ k) := by
  induction k generalizing X with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, singleConjugation_apply, pow_succ, pow_succ']
    simp only [mul_assoc]

theorem casimirConjugation_eq_sum_single (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) :
    casimirConjugation E c s = ∑ i ∈ s, singleConjugation E c i := rfl

theorem singleConjugation_commute {E : GLOps n K V} (hE : IsGLRep E) (c i j : Fin n) (hi : i ≠ c) (hj : j ≠ c) :
    Commute (singleConjugation E c i) (singleConjugation E c j) := by
  have h1 : E c i * E c j = E c j * E c i := by
    have := hE.1 c i c j
    rw [if_neg hi, if_neg hj, sub_zero, sub_eq_zero] at this
    exact this
  have h2 : E j c * E i c = E i c * E j c := by
    have := hE.1 j c i c
    rw [if_neg (Ne.symm hi), if_neg (Ne.symm hj), sub_zero, sub_eq_zero] at this
    exact this
  unfold Commute SemiconjBy
  ext X : 1
  simp only [Module.End.mul_apply, singleConjugation_apply, ← mul_assoc, h1]
  simp only [mul_assoc, h2]

theorem casimirPowerW_insert_binomial {E : GLOps n K V} (hE : IsGLRep E) (c i : Fin n) (s : Finset (Fin n)) (his : i ∉ s)
    (hi : i ≠ c) (hs : ∀ j ∈ s, j ≠ c) (q : ℕ) :
    casimirPower E c (insert i s) q =
      ∑ k ∈ range (q + 1), (q.choose k) • ((E c i) ^ k * (casimirPower E c s (q - k) * (E i c) ^ k)) := by
  have hc : Commute (singleConjugation E c i) (casimirConjugation E c s) := by
    rw [casimirConjugation_eq_sum_single]
    exact Commute.sum_right _ _ _ fun j hj => singleConjugation_commute hE c i j hi (hs j hj)
  unfold casimirPower
  rw [casimirConjugation_eq_sum_single E c (insert i s), Finset.sum_insert his, ← casimirConjugation_eq_sum_single, hc.add_pow, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, map_nsmul,
    singleConjugation_pow_apply]

theorem casimirPowerW_empty (E : GLOps n K V) (c : Fin n) (q : ℕ) :
    casimirPower E c ∅ q = if q = 0 then 1 else 0 := by
  unfold casimirPower casimirConjugation
  rw [Finset.sum_empty]
  rcases q with _ | q <;> simp

end Alg

section Alg2

variable {n : ℕ} {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

theorem factorial_ratio_choose_identity (b q k : ℕ) (hk : k ≤ q) :
    ((b.factorial : K) / (((q + b).factorial : K) * (q.factorial : K))) * ((q.choose k : ℕ) : K) =
      (1 / (((q + b).choose k : ℕ) : K)) * ((k.factorial : K)⁻¹ *
        (((b.factorial : K) / (((q - k + b).factorial : K) * ((q - k).factorial : K))) * (k.factorial : K)⁻¹)) := by
  have hk' : k ≤ q + b := le_trans hk (Nat.le_add_right q b)
  rw [Nat.cast_choose K hk, Nat.cast_choose K hk', Nat.sub_add_comm hk]
  have h1 : ((q + b).factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h2 : (q.factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h3 : (k.factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h4 : ((q - k).factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h5 : ((q - k + b).factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h6 : (b.factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp

theorem casimirPowerScaled_insert_dividedPower {E : GLOps n K V} (hE : IsGLRep E) (c i : Fin n) (s : Finset (Fin n)) (his : i ∉ s)
    (hi : i ≠ c) (hs : ∀ j ∈ s, j ≠ c) (b q : ℕ) (y : V) :
    casimirPowerScaled E c (insert i s) b q y =
      ∑ k ∈ range (q + 1), (1 / (((q + b).choose k : ℕ) : K)) •
        divPowE E c i k (casimirPowerScaled E c s b (q - k) (divPowE E i c k y)) := by
  unfold casimirPowerScaled divPowE
  rw [casimirPowerW_insert_binomial hE c i s his hi hs q]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum, Module.End.mul_apply, map_smul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkq : k ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [← Nat.cast_smul_eq_nsmul K, smul_smul]
  congr 1
  rw [factorial_ratio_choose_identity b q k hkq]

end Alg2

section Lattice

variable {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

private theorem isUnit_natCast_of_not_dvd_root_weights (S : UniformizedDVR p O) (hp : p.Prime) (u : ℕ) (hu : ¬ p ∣ u) :
    IsUnit (u : O) := by
  by_contra hnu
  have hum : (u : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have hcop : IsCoprime (u : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu))
  obtain ⟨x, z, hxz⟩ := hcop
  have h1 : ((x * u + z * p : ℤ) : O) = 1 := by rw [hxz]; simp
  push_cast at h1
  have h2 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [← h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hum) (Ideal.mul_mem_left _ _ S.p_mem)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h2)

private theorem charZero_KK_of_uniformizedDVR (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  refine charZero_of_inj_zero fun N hN => ?_
  by_contra hN0
  have hN' : (N : O) = 0 := by
    apply IsFractionRing.injective O (KK O)
    rw [map_natCast, map_zero, hN]
  have hCu : p ^ N.factorization p * (N / p ^ N.factorization p) = N := by
    first
      | exact Nat.ordProj_mul_ordCompl_eq_self N p
      | exact Nat.ord_proj_mul_ord_compl_eq_self N p
  have hu : ¬ p ∣ (N / p ^ N.factorization p) := by
    first
      | exact Nat.not_dvd_ordCompl hp hN0
      | exact Nat.not_dvd_ord_compl hp hN0
  rw [← hCu, Nat.cast_mul, Nat.cast_pow] at hN'
  rcases mul_eq_zero.mp hN' with h | h
  · exact S.p_ne (pow_eq_zero_iff'.mp h).1
  · exact (isUnit_natCast_of_not_dvd_root_weights S hp _ hu).ne_zero h

private theorem exists_integral_p_pow_div_choose_of_log_le (S : UniformizedDVR p O) (hp : p.Prime) (N k d : ℕ)
    (hN : Nat.log p N ≤ d) (hk : k ≤ N) :
    ∃ o : O, algebraMap O (KK O) o = ((p : KK O) ^ d) * (1 / ((N.choose k : ℕ) : KK O)) := by
  have hC0 : N.choose k ≠ 0 := (Nat.choose_pos hk).ne'
  have hCu : p ^ (N.choose k).factorization p * (N.choose k / p ^ (N.choose k).factorization p) =
      N.choose k := by
    first
      | exact Nat.ordProj_mul_ordCompl_eq_self (N.choose k) p
      | exact Nat.ord_proj_mul_ord_compl_eq_self (N.choose k) p
  have hu : ¬ p ∣ (N.choose k / p ^ (N.choose k).factorization p) := by
    first
      | exact Nat.not_dvd_ordCompl hp hC0
      | exact Nat.not_dvd_ord_compl hp hC0
  have ha : (N.choose k).factorization p ≤ d := Nat.factorization_choose_le_log.trans hN
  generalize (N.choose k).factorization p = a at hCu hu ha
  generalize N.choose k / p ^ a = u at hCu hu
  have huO : IsUnit (u : O) := isUnit_natCast_of_not_dvd_root_weights S hp u hu
  have hp0 : (p : KK O) ≠ 0 := by
    rw [← map_natCast (algebraMap O (KK O))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).mpr S.p_ne
  have hu0 : ((u : ℕ) : KK O) ≠ 0 := by
    rw [← map_natCast (algebraMap O (KK O))]
    exact (huO.map _).ne_zero
  have hinv : algebraMap O (KK O) ((huO.unit⁻¹ : Oˣ) : O) = ((u : ℕ) : KK O)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_natCast (algebraMap O (KK O)), ← map_mul, huO.val_inv_mul, map_one]
  refine ⟨(p : O) ^ (d - a) * ((huO.unit⁻¹ : Oˣ) : O), ?_⟩
  rw [map_mul, map_pow, map_natCast, hinv, ← hCu]
  push_cast
  conv_rhs => rw [← Nat.sub_add_cancel ha, pow_add]
  field_simp
  try ring

theorem scaled_casimirPower_integral_bound (S : UniformizedDVR p O) (hp : p.Prime) {E : GLOps n (KK O) V} (hE : IsGLRep E)
    {M : Submodule O V} (hM : UZStable (O := O) E M) (c : Fin n) (L : ℕ) (s : Finset (Fin n)) :
    (∀ j ∈ s, j ≠ c) → ∀ q b : ℕ, q + b ≤ L + n - 1 → ∀ y ∈ M,
      ((p : O) ^ (s.card * deF p n L)) • casimirPowerScaled E c s b q y ∈ M := by
  haveI := charZero_KK_of_uniformizedDVR S hp
  induction s using Finset.induction_on with
  | empty =>
    intro _ q b _ y hy
    simp only [Finset.card_empty, zero_mul, pow_zero, one_smul]
    unfold casimirPowerScaled
    rw [casimirPowerW_empty]
    split_ifs with hq
    · subst hq
      have hb0 : (b.factorial : KK O) ≠ 0 := by exact_mod_cast (Nat.factorial_pos b).ne'
      simpa [hb0] using hy
    · simp
  | @insert i s his ih =>
    intro hs q b hqb y hy
    have hic : i ≠ c := hs i (Finset.mem_insert_self i s)
    have hs' : ∀ j ∈ s, j ≠ c := fun j hj => hs j (Finset.mem_insert_of_mem hj)
    rw [casimirPowerScaled_insert_dividedPower hE c i s his hic hs' b q y, Finset.smul_sum]
    refine Submodule.sum_mem _ fun k hk => ?_
    have hkq : k ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hy' : divPowE E i c k y ∈ M := hM _ (Or.inl ⟨i, c, k, hic, rfl⟩) y hy
    have hz : ((p : O) ^ (s.card * deF p n L)) • casimirPowerScaled E c s b (q - k) (divPowE E i c k y) ∈ M :=
      ih hs' (q - k) b (by omega) _ hy'
    have hz' := hM _ (Or.inl ⟨c, i, k, Ne.symm hic, rfl⟩) _ hz
    obtain ⟨o, ho⟩ := exists_integral_p_pow_div_choose_of_log_le S hp (q + b) k (deF p n L)
      (by unfold deF; exact Nat.log_mono_right hqb) (by omega)
    have heq : ((p : O) ^ ((insert i s).card * deF p n L)) • ((1 / (((q + b).choose k : ℕ) : KK O)) •
        divPowE E c i k (casimirPowerScaled E c s b (q - k) (divPowE E i c k y))) =
        o • divPowE E c i k (((p : O) ^ (s.card * deF p n L)) •
          casimirPowerScaled E c s b (q - k) (divPowE E i c k y)) := by
      first
        | rw [Finset.card_insert_of_notMem his]
        | rw [Finset.card_insert_of_not_mem his]
      simp only [← algebraMap_smul (R := O) (KK O), map_smul, smul_smul]
      congr 1
      rw [ho]
      simp only [map_pow, map_natCast]
      ring
    rw [heq]
    exact M.smul_mem o hz'

theorem extremalProjector_denominator_bound (S : UniformizedDVR p O) (hp : p.Prime) {E : GLOps n (KK O) V} (hE : IsGLRep E)
    {M : Submodule O V} (hM : UZStable (O := O) E M) (c : Fin n) (L : ℕ) (y : V) (hy : y ∈ M) :
    ((p : O) ^ (c.val * deF p n L)) • extremalProjector E c L y ∈ M := by
  unfold extremalProjector
  rw [LinearMap.sum_apply, Finset.smul_sum]
  refine Submodule.sum_mem _ fun q hq => ?_
  have hqL : q ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
  have h := scaled_casimirPower_integral_bound S hp hE hM c L (Finset.Iio c) (fun j hj => ne_of_lt (Finset.mem_Iio.mp hj))
    q c.val (by have := c.isLt; omega) y hy
  rw [Fin.card_Iio] at h
  have heq : ((p : O) ^ (c.val * deF p n L)) • (((-1 : KK O) ^ q) • casimirPowerScaled E c (Finset.Iio c) c.val q) y =
      ((-1 : O) ^ q) • (((p : O) ^ (c.val * deF p n L)) • casimirPowerScaled E c (Finset.Iio c) c.val q y) := by
    simp only [LinearMap.smul_apply, ← algebraMap_smul (R := O) (KK O), smul_smul, map_pow, map_neg,
      map_one, map_natCast]
    congr 1
    ring
  rw [heq]
  exact M.smul_mem _ h

end Lattice

end Formalism.MainNotions.G.GLWeightTheory
