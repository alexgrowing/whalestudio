import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementE
import Formalism.GaussJetBounds.GaussJetProofs.ConstantCoeffAevalLinP

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

namespace ETerm

open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact jetPair_eq_sum jetPair_C_mul_right jetPair_sum_right)

section Mono

variable {Tp Lw : Type}

def jn (e : Tp →₀ ℕ) (n : Lw →₀ ℕ) : Tp ⊕ Lw →₀ ℕ := e.mapDomain Sum.inl + n.mapDomain Sum.inr

lemma mapDomain_inl_inl (e : Tp →₀ ℕ) (τ : Tp) :
    (e.mapDomain (Sum.inl : Tp → Tp ⊕ Lw)) (Sum.inl τ) = e τ :=
  Finsupp.mapDomain_apply Sum.inl_injective _ _

lemma mapDomain_inl_inr (e : Tp →₀ ℕ) (x : Lw) :
    (e.mapDomain (Sum.inl : Tp → Tp ⊕ Lw)) (Sum.inr x) = 0 :=
  Finsupp.mapDomain_of_notMem_range _ _ (by simp)

lemma mapDomain_inr_inr (n : Lw →₀ ℕ) (x : Lw) :
    (n.mapDomain (Sum.inr : Lw → Tp ⊕ Lw)) (Sum.inr x) = n x :=
  Finsupp.mapDomain_apply Sum.inr_injective _ _

lemma mapDomain_inr_inl (n : Lw →₀ ℕ) (τ : Tp) :
    (n.mapDomain (Sum.inr : Lw → Tp ⊕ Lw)) (Sum.inl τ) = 0 :=
  Finsupp.mapDomain_of_notMem_range _ _ (by simp)

lemma jn_inl (e : Tp →₀ ℕ) (n : Lw →₀ ℕ) (τ : Tp) : jn e n (Sum.inl τ) = e τ := by
  simp [jn, mapDomain_inl_inl, mapDomain_inr_inl]

lemma jn_inr (e : Tp →₀ ℕ) (n : Lw →₀ ℕ) (x : Lw) : jn e n (Sum.inr x) = n x := by
  simp [jn, mapDomain_inl_inr, mapDomain_inr_inr]

lemma jn_injective (e : Tp →₀ ℕ) : Function.Injective (jn (Lw := Lw) e) := by
  intro n n' h
  ext x
  rw [← jn_inr e n x, h, jn_inr]

lemma degree_jn [Fintype Tp] [Fintype Lw] (e : Tp →₀ ℕ) (n : Lw →₀ ℕ) :
    (jn e n).degree = e.degree + n.degree := by
  simp only [Finsupp.degree_eq_sum, Fintype.sum_sum_type, jn_inl, jn_inr]

lemma mfact_eq_prod {ι : Type} [Fintype ι] (n : ι →₀ ℕ) : mfact n = ∏ i, (n i).factorial := by
  unfold mfact
  exact Finsupp.prod_fintype _ _ (fun _ => rfl)

lemma mfact_jn [Fintype Tp] [Fintype Lw] (e : Tp →₀ ℕ) (n : Lw →₀ ℕ) :
    mfact (jn e n) = mfact e * mfact n := by
  simp only [mfact_eq_prod, Fintype.prod_sum_type, jn_inl, jn_inr]

lemma lowDeg_jn [Fintype Lw] (e : Tp →₀ ℕ) (n : Lw →₀ ℕ) : lowDeg (jn e n) = n.degree := by
  simp only [lowDeg, Finsupp.degree_eq_sum, jn_inr]

lemma lowDeg_add [Fintype Lw] (a c : Tp ⊕ Lw →₀ ℕ) : lowDeg (a + c) = lowDeg a + lowDeg c := by
  simp [lowDeg, Finset.sum_add_distrib]

lemma lowDeg_sub_le [Fintype Lw] (a c : Tp ⊕ Lw →₀ ℕ) : lowDeg (a - c) ≤ lowDeg a := by
  unfold lowDeg
  refine Finset.sum_le_sum fun x _ => ?_
  simp

end Mono

section Op

variable {K Tp Lw : Type} [Field K]

lemma coeff_jn (e : Tp →₀ ℕ) (n : Lw →₀ ℕ) (R : MvPolynomial Lw K) :
    MvPolynomial.coeff (jn e n) (topMonoP e * lowPoly R) = MvPolynomial.coeff n R := by
  unfold jn topMonoP lowPoly
  rw [MvPolynomial.coeff_monomial_mul, one_mul,
    MvPolynomial.coeff_rename_mapDomain _ Sum.inr_injective]

lemma support_topLow [DecidableEq Tp] [DecidableEq Lw] (e : Tp →₀ ℕ) (R : MvPolynomial Lw K) :
    (topMonoP e * lowPoly R).support ⊆ R.support.image (jn e) := by
  intro m hm
  rw [MvPolynomial.mem_support_iff] at hm
  unfold topMonoP lowPoly at hm
  rw [MvPolynomial.coeff_monomial_mul'] at hm
  split_ifs at hm with hle
  · rw [one_mul] at hm
    by_contra hcon
    apply hm
    refine MvPolynomial.coeff_rename_eq_zero _ _ _ fun u hu => ?_
    by_contra hu0
    apply hcon
    rw [Finset.mem_image]
    refine ⟨u, MvPolynomial.mem_support_iff.2 hu0, ?_⟩
    unfold jn
    rw [hu]
    exact add_tsub_cancel_of_le hle
  · exact absurd rfl hm

lemma jetPair_topLow [Fintype Tp] [Fintype Lw] (e : Tp →₀ ℕ)
    (R : MvPolynomial Lw K) (G : MvPowerSeries (Tp ⊕ Lw) K) :
    jetPair (topMonoP e * lowPoly R) G =
      ∑ n ∈ R.support, MvPolynomial.coeff n R * ((mfact e * mfact n : ℕ) : K) *
        MvPowerSeries.coeff (jn e n) G := by
  classical
  rw [jetPair_eq_sum _ _ _ (support_topLow e R), Finset.sum_image (fun a _ c _ h => jn_injective e h)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [coeff_jn, mfact_jn]

lemma jetPair_congr {ι : Type} (P : MvPolynomial ι K) (G G' : MvPowerSeries ι K)
    (h : ∀ m ∈ P.support, MvPowerSeries.coeff m G = MvPowerSeries.coeff m G') :
    jetPair P G = jetPair P G' := by
  unfold jetPair
  exact Finset.sum_congr rfl fun m hm => by rw [h m hm]

variable {κ : Type} [Fintype κ]

def ext0 (b : κ → Lw → K) (k : κ) : Tp ⊕ Lw → K := Sum.elim 0 (b k)

lemma lin_s_extend_zero [Fintype Tp] [Fintype Lw] (b : κ → Lw → K) (k : κ) :
    linS (ext0 (Tp := Tp) b k) = lowLin (b k) := by
  unfold linS lowLin ext0
  rw [Fintype.sum_sum_type]
  simp

lemma shiftPoly_topMonoP (b : κ → Lw → K) (e : Tp →₀ ℕ) :
    shiftPoly (ext0 (Tp := Tp) b) (topMonoP e) = MvPolynomial.C (topMonoP e) := by
  unfold shiftPoly topMonoP
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_mapDomain_index_inj Sum.inl_injective,
    MvPolynomial.monomial_eq, Finsupp.prod_mapDomain_index_inj Sum.inl_injective]
  simp [ext0, Finsupp.prod, map_prod]

lemma shiftPoly_lowPoly (b : κ → Lw → K) (Q : MvPolynomial Lw K) :
    shiftPoly (ext0 (Tp := Tp) b) (lowPoly Q) =
      MvPolynomial.map (MvPolynomial.rename (Sum.inr : Lw → Tp ⊕ Lw) :
        MvPolynomial Lw K →ₐ[K] MvPolynomial (Tp ⊕ Lw) K).toRingHom (shiftPoly b Q) := by
  unfold shiftPoly lowPoly
  induction Q using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f x hf =>
    simp only [map_mul, hf]
    simp [ext0, map_sum]

lemma hasseDir_topLow (b : κ → Lw → K) (β : κ →₀ ℕ) (e : Tp →₀ ℕ) (Q : MvPolynomial Lw K) :
    hasseDir (ext0 (Tp := Tp) b) β (topMonoP e * lowPoly Q) =
      topMonoP e * lowPoly (hasseDir b β Q) := by
  have hm : shiftPoly (ext0 (Tp := Tp) b) (topMonoP e * lowPoly Q) =
      shiftPoly (ext0 (Tp := Tp) b) (topMonoP e) * shiftPoly (ext0 (Tp := Tp) b) (lowPoly Q) := by
    unfold shiftPoly
    exact map_mul _ _ _
  unfold hasseDir
  rw [hm, shiftPoly_topMonoP, shiftPoly_lowPoly, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]
  rfl

end Op

section Ser

variable {K σ : Type} [Field K]

def Agree (D : ℕ) (f f' : MvPowerSeries σ K) : Prop :=
  ∀ n : σ →₀ ℕ, n.degree ≤ D → MvPowerSeries.coeff n f = MvPowerSeries.coeff n f'

lemma agree_refl (D : ℕ) (f : MvPowerSeries σ K) : Agree D f f := fun _ _ => rfl

lemma agree_mul {D : ℕ} {f f' g g' : MvPowerSeries σ K} (hf : Agree D f f') (hg : Agree D g g') :
    Agree D (f * g) (f' * g') := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  have hd : x.1.degree + x.2.degree = n.degree := by rw [← hx', map_add]
  rw [hf _ (by omega), hg _ (by omega)]

lemma agree_pow {D : ℕ} {f f' : MvPowerSeries σ K} (hf : Agree D f f') (i : ℕ) :
    Agree D (f ^ i) (f' ^ i) := by
  induction i with
  | zero => simpa using agree_refl D (1 : MvPowerSeries σ K)
  | succ i ih =>
    rw [pow_succ, pow_succ]
    exact agree_mul ih hf

lemma prod_monomial {α : Type} (s : Finset α) (d : α → σ →₀ ℕ) (a : α → K) :
    ∏ i ∈ s, MvPowerSeries.monomial (d i) (a i) =
      MvPowerSeries.monomial (∑ i ∈ s, d i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [MvPowerSeries.monomial_zero_one]
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx, Finset.prod_insert hx, ih,
      MvPowerSeries.monomial_mul_monomial]

lemma C_mul_monomial_one (a : K) (d : σ →₀ ℕ) :
    MvPowerSeries.C a * MvPowerSeries.monomial d (1 : K) = MvPowerSeries.monomial d a := by
  rw [← MvPowerSeries.monomial_zero_eq_C_apply, MvPowerSeries.monomial_mul_monomial, zero_add,
    mul_one]

end Ser

section Low

variable {K Tp Lw : Type} [Field K] [Fintype Lw]

def LowGe (m : ℕ) (V : MvPowerSeries (Tp ⊕ Lw) K) : Prop :=
  ∀ n, MvPowerSeries.coeff n V ≠ 0 → m ≤ lowDeg n

lemma lowGe_zero (V : MvPowerSeries (Tp ⊕ Lw) K) : LowGe 0 V := fun _ _ => Nat.zero_le _

lemma lowGe_mul {m m' : ℕ} {V V' : MvPowerSeries (Tp ⊕ Lw) K} (h : LowGe m V) (h' : LowGe m' V') :
    LowGe (m + m') (V * V') := by
  classical
  intro n hn
  rw [MvPowerSeries.coeff_mul] at hn
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  rw [← hx', lowDeg_add]
  exact add_le_add (h _ (left_ne_zero_of_mul hx0)) (h' _ (right_ne_zero_of_mul hx0))

lemma lowGe_pow {m : ℕ} {V : MvPowerSeries (Tp ⊕ Lw) K} (h : LowGe m V) (i : ℕ) :
    LowGe (m * i) (V ^ i) := by
  induction i with
  | zero => exact lowGe_zero _
  | succ i ih =>
    rw [pow_succ, Nat.mul_succ]
    exact lowGe_mul ih h

end Low

section Norm

variable {K : Type} [NormedField K] [IsUltrametricDist K]

lemma integral_mul {σ : Type} {f g : MvPowerSeries σ K} (hf : Integral f) (hg : Integral g) :
    Integral (f * g) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

lemma integral_pow {σ : Type} {f : MvPowerSeries σ K} (hf : Integral f) (i : ℕ) :
    Integral (f ^ i) := by
  classical
  induction i with
  | zero =>
    intro n
    rw [pow_zero, MvPowerSeries.coeff_one]
    split_ifs <;> simp
  | succ i ih =>
    rw [pow_succ]
    exact integral_mul ih hf

lemma norm_prod_pow_le_one {α : Type} (s : Finset α) (a : α → K) (m : α → ℕ)
    (ha : ∀ i, ‖a i‖ ≤ 1) : ‖∏ i ∈ s, a i ^ m i‖ ≤ 1 := by
  rw [norm_prod]
  refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => ?_
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (ha i)

lemma closure_sum {Wt J : Type} (valid : Wt → Prop) (B : Wt → ℝ) (s : Finset J) (f : J → K)
    (h : ∀ j ∈ s, f j = 0 ∨ ∃ w, valid w ∧ ‖f j‖ ≤ B w) :
    ∑ j ∈ s, f j = 0 ∨ ∃ w, valid w ∧ ‖∑ j ∈ s, f j‖ ≤ B w := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · left; simp
  · obtain ⟨j, hj, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs f
    rcases h j hj with h0 | ⟨w, hw, hb⟩
    · left
      rw [h0, norm_zero] at hle
      exact norm_le_zero_iff.1 hle
    · exact Or.inr ⟨w, hw, hle.trans hb⟩

lemma norm_natCast_le_of_dvd {a c : ℕ} (h : a ∣ c) : ‖(c : K)‖ ≤ ‖(a : K)‖ := by
  obtain ⟨q, rfl⟩ := h
  rw [Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K q)

end Norm

lemma fact_dvd {Φ κ : Type} [Fintype Φ] [Fintype κ] (k : Φ ⊕ κ ⊕ Fin 2 → ℕ) :
    (∑ x : κ, k (Sum.inr (Sum.inl x))).factorial ∣
      Nat.multinomial univ k * ∏ x : κ, (k (Sum.inr (Sum.inl x))).factorial := by
  have hs := Nat.multinomial_spec (univ : Finset (Φ ⊕ κ ⊕ Fin 2)) k
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at hs
  set A := ∏ φ : Φ, (k (Sum.inl φ)).factorial with hA
  set Bf := ∏ x : κ, (k (Sum.inr (Sum.inl x))).factorial with hBf
  set C2 := ∏ t : Fin 2, (k (Sum.inr (Sum.inr t))).factorial with hC2
  set sA := ∑ φ : Φ, k (Sum.inl φ) with hsA
  set sB := ∑ x : κ, k (Sum.inr (Sum.inl x)) with hsB
  set sC := ∑ t : Fin 2, k (Sum.inr (Sum.inr t)) with hsC
  have h1 : A ∣ sA.factorial := Nat.prod_factorial_dvd_factorial_sum _ _
  have h2 : C2 ∣ sC.factorial := Nat.prod_factorial_dvd_factorial_sum _ _
  have h3 : sB.factorial * sC.factorial ∣ (sB + sC).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add _ _
  have h4 : sA.factorial * (sB + sC).factorial ∣ (sA + (sB + sC)).factorial :=
    Nat.factorial_mul_factorial_dvd_factorial_add _ _
  have h5 : A * (sB.factorial * C2) ∣ (sA + (sB + sC)).factorial :=
    (mul_dvd_mul h1 ((mul_dvd_mul (dvd_refl _) h2).trans h3)).trans h4
  rw [← hs] at h5
  have hpos : 0 < A * C2 :=
    Nat.mul_pos (Finset.prod_pos fun _ _ => Nat.factorial_pos _)
      (Finset.prod_pos fun _ _ => Nat.factorial_pos _)
  refine Nat.dvd_of_mul_dvd_mul_left hpos ?_
  have e1 : A * C2 * sB.factorial = A * (sB.factorial * C2) := by ring
  have e2 : A * C2 * (Nat.multinomial univ k * Bf) = A * (Bf * C2) * Nat.multinomial univ k := by
    ring
  rw [e1, e2]
  exact h5

section Main

variable {K Tp Lw Φ κ : Type} [NormedField K] [IsUltrametricDist K] [Fintype Tp] [Fintype Lw]
  [Fintype Φ] [Fintype κ]

def piece (p : ℕ) (Z Y : MvPowerSeries (Tp ⊕ Lw) K) (aA : Φ → K) (dA : Φ → Tp →₀ ℕ) (aB : κ → K)
    (dB : κ → Tp →₀ ℕ) (b : κ → Lw → K) : Φ ⊕ κ ⊕ Fin 2 → MvPowerSeries (Tp ⊕ Lw) K :=
  Sum.elim (fun φ => MvPowerSeries.C (aA φ) * topMonoS (dA φ))
    (Sum.elim (fun k => MvPowerSeries.C (aB k) * topMonoS (dB k) * lowLin (b k))
      (fun t => if t = 0 then Z else MvPowerSeries.C (p : K) * Y))

lemma sum_piece (p : ℕ) (Z Y : MvPowerSeries (Tp ⊕ Lw) K) (aA : Φ → K) (dA : Φ → Tp →₀ ℕ)
    (aB : κ → K) (dB : κ → Tp →₀ ℕ) (b : κ → Lw → K) :
    ∑ j, piece p Z Y aA dA aB dB b j =
      ∑ φ, MvPowerSeries.C (aA φ) * topMonoS (Lw := Lw) (dA φ) +
        ∑ k, MvPowerSeries.C (aB k) * topMonoS (dB k) * lowLin (b k) + Z +
        MvPowerSeries.C (p : K) * Y := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_two]
  simp only [piece, Sum.elim_inl, Sum.elim_inr, if_true, one_ne_zero, if_false]
  ring

def dTot (dA : Φ → Tp →₀ ℕ) (dB : κ → Tp →₀ ℕ) (k : Φ ⊕ κ ⊕ Fin 2 → ℕ) : Tp ⊕ Lw →₀ ℕ :=
  ∑ φ, k (Sum.inl φ) • (dA φ).mapDomain Sum.inl +
    ∑ x, k (Sum.inr (Sum.inl x)) • (dB x).mapDomain Sum.inl

def cTot (p : ℕ) (aA : Φ → K) (aB : κ → K) (k : Φ ⊕ κ ⊕ Fin 2 → ℕ) : K :=
  (∏ φ, aA φ ^ k (Sum.inl φ)) * (∏ x, aB x ^ k (Sum.inr (Sum.inl x))) *
    (p : K) ^ k (Sum.inr (Sum.inr 1))

lemma dTot_inl (dA : Φ → Tp →₀ ℕ) (dB : κ → Tp →₀ ℕ) (k : Φ ⊕ κ ⊕ Fin 2 → ℕ) (τ : Tp) :
    dTot (Lw := Lw) dA dB k (Sum.inl τ) =
      ∑ φ, k (Sum.inl φ) * dA φ τ + ∑ x, k (Sum.inr (Sum.inl x)) * dB x τ := by
  simp [dTot, mapDomain_inl_inl]

lemma prod_piece (p : ℕ) (Z Y : MvPowerSeries (Tp ⊕ Lw) K) (aA : Φ → K) (dA : Φ → Tp →₀ ℕ)
    (aB : κ → K) (dB : κ → Tp →₀ ℕ) (b : κ → Lw → K) (k : Φ ⊕ κ ⊕ Fin 2 → ℕ)
    (U : MvPowerSeries (Tp ⊕ Lw) K) :
    (∏ j, piece p Z Y aA dA aB dB b j ^ k j) * U =
      (∏ x, lowLin (b x) ^ k (Sum.inr (Sum.inl x))) *
        (MvPowerSeries.monomial (dTot dA dB k) (cTot p aA aB k) *
          (Z ^ k (Sum.inr (Sum.inr 0)) * (Y ^ k (Sum.inr (Sum.inr 1)) * U))) := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fin.prod_univ_two]
  simp only [piece, Sum.elim_inl, Sum.elim_inr, if_true, one_ne_zero, if_false]
  have hA : ∏ φ, (MvPowerSeries.C (aA φ) * topMonoS (Lw := Lw) (dA φ)) ^ k (Sum.inl φ) =
      MvPowerSeries.monomial (∑ φ, k (Sum.inl φ) • (dA φ).mapDomain Sum.inl)
        (∏ φ, aA φ ^ k (Sum.inl φ)) := by
    rw [← prod_monomial]
    refine Finset.prod_congr rfl fun φ _ => ?_
    unfold topMonoS
    rw [C_mul_monomial_one, MvPowerSeries.monomial_pow]
  have hB : ∏ x, (MvPowerSeries.C (aB x) * topMonoS (Lw := Lw) (dB x) * lowLin (b x)) ^
        k (Sum.inr (Sum.inl x)) =
      MvPowerSeries.monomial (∑ x, k (Sum.inr (Sum.inl x)) • (dB x).mapDomain Sum.inl)
        (∏ x, aB x ^ k (Sum.inr (Sum.inl x))) * ∏ x, lowLin (b x) ^ k (Sum.inr (Sum.inl x)) := by
    rw [← prod_monomial, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    unfold topMonoS
    rw [C_mul_monomial_one, mul_pow, MvPowerSeries.monomial_pow]
  have hC : MvPowerSeries.monomial (dTot (Lw := Lw) dA dB k) (cTot p aA aB k) =
      MvPowerSeries.monomial (∑ φ, k (Sum.inl φ) • (dA φ).mapDomain Sum.inl)
        (∏ φ, aA φ ^ k (Sum.inl φ)) *
      MvPowerSeries.monomial (∑ x, k (Sum.inr (Sum.inl x)) • (dB x).mapDomain Sum.inl)
        (∏ x, aB x ^ k (Sum.inr (Sum.inl x))) *
      MvPowerSeries.C ((p : K)) ^ k (Sum.inr (Sum.inr 1)) := by
    rw [← map_pow, ← MvPowerSeries.monomial_zero_eq_C_apply, MvPowerSeries.monomial_mul_monomial,
      MvPowerSeries.monomial_mul_monomial, add_zero]
    rfl
  rw [hA, hB, hC, mul_pow]
  ring

def valid (p : ℕ) (aA : Φ → K) (dA : Φ → Tp →₀ ℕ) (aB : κ → K) (dB : κ → Tp →₀ ℕ) (b : κ → Lw → K)
    (e : Tp →₀ ℕ) (Q : MvPolynomial Lw K) (w : (Φ → ℕ) × (κ →₀ ℕ) × ℕ × (Lw →₀ ℕ)) : Prop :=
  w.2.2.2 ∈ (hasseDir b w.2.1 Q).support ∧ (∀ φ, w.1 φ ≠ 0 → aA φ ≠ 0) ∧
    (∀ k, w.2.1 k ≠ 0 → aB k ≠ 0) ∧
    (∀ τ, ∑ φ, w.1 φ * dA φ τ + ∑ k, w.2.1 k * dB k τ ≤ e τ) ∧ p * w.2.2.1 ≤ w.2.2.2.degree

def bnd (K : Type) [NormedField K] (p : ℕ) (e : Tp →₀ ℕ)
    (w : (Φ → ℕ) × (κ →₀ ℕ) × ℕ × (Lw →₀ ℕ)) : ℝ :=
  (p : ℝ) ^ (∑ φ, w.1 φ + ∑ k, w.2.1 k + w.2.2.1) * ‖((mfact e : ℕ) : K)‖ *
    ‖(((∑ k, w.2.1 k).factorial : ℕ) : K)‖ * ‖((mfact w.2.2.2 : ℕ) : K)‖

lemma term_bound (h1 : JetPairingHasseIdentity) (h2 : HasseDerivIntegralHomogeneous) (p : ℕ) (Z Y : MvPowerSeries (Tp ⊕ Lw) K)
    (aA : Φ → K) (dA : Φ → Tp →₀ ℕ) (aB : κ → K) (dB : κ → Tp →₀ ℕ) (b : κ → Lw → K)
    (e : Tp →₀ ℕ) (Q : MvPolynomial Lw K) (hp : p.Prime) (hpn : ‖(p : K)‖ = (p : ℝ)⁻¹)
    (haA : ∀ φ, ‖aA φ‖ ≤ 1) (haB : ∀ k, ‖aB k‖ ≤ 1) (hb : ∀ k x, ‖b k x‖ ≤ 1) (hZ : Integral Z)
    (hY : Integral Y) (hZlow : LowGe p Z) (hQ : ∀ n, ‖MvPolynomial.coeff n Q‖ ≤ 1)
    (i : ℕ) (k : Φ ⊕ κ ⊕ Fin 2 → ℕ) (hk : ∑ j, k j = i) (U : MvPowerSeries (Tp ⊕ Lw) K)
    (hU : Integral U) :
    ((p : K) ^ i)⁻¹ * (((Nat.multinomial univ k : ℕ) : K) *
        jetPair (topMonoP e * lowPoly Q) ((∏ j, piece p Z Y aA dA aB dB b j ^ k j) * U)) = 0 ∨
      ∃ w, valid p aA dA aB dB b e Q w ∧
        ‖((p : K) ^ i)⁻¹ * (((Nat.multinomial univ k : ℕ) : K) *
          jetPair (topMonoP e * lowPoly Q) ((∏ j, piece p Z Y aA dA aB dB b j ^ k j) * U))‖ ≤
          bnd K p e w := by
  classical
  set β : κ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun x => k (Sum.inr (Sum.inl x))) with hβ
  have hβx : ∀ x, β x = k (Sum.inr (Sum.inl x)) := fun x => rfl
  have hlin : ∏ x, lowLin (Tp := Tp) (b x) ^ k (Sum.inr (Sum.inl x)) =
      ∏ x, linS (ext0 (Tp := Tp) b x) ^ β x :=
    Finset.prod_congr rfl fun x _ => by rw [lin_s_extend_zero, hβx]
  rw [prod_piece, hlin, h1 K (Tp ⊕ Lw) κ (ext0 b) β, hasseDir_topLow, jetPair_topLow,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine closure_sum _ _ _ _ fun n hn => ?_
  rw [MvPowerSeries.coeff_monomial_mul]
  split_ifs with hle
  swap
  · left; simp
  set v := MvPowerSeries.coeff (jn e n - dTot dA dB k)
    (Z ^ k (Sum.inr (Sum.inr 0)) * (Y ^ k (Sum.inr (Sum.inr 1)) * U)) with hv
  by_cases hc : cTot p aA aB k * v = 0
  · left; simp [hc]
  right
  have hc1 : cTot p aA aB k ≠ 0 := left_ne_zero_of_mul hc
  have hv1 : v ≠ 0 := right_ne_zero_of_mul hc
  have hsum : ∑ φ, k (Sum.inl φ) + ∑ x, β x + k (Sum.inr (Sum.inr 0)) + k (Sum.inr (Sum.inr 1)) = i := by
    rw [← hk, Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_two]
    simp only [hβx]
    ring
  refine ⟨(fun φ => k (Sum.inl φ), β, k (Sum.inr (Sum.inr 0)), n), ⟨hn, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro φ hφ h0
    apply hc1
    have : ∏ φ, aA φ ^ k (Sum.inl φ) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ φ) (by rw [h0]; exact zero_pow hφ)
    simp [cTot, this]
  · intro x hx h0
    apply hc1
    have : ∏ x, aB x ^ k (Sum.inr (Sum.inl x)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ x) (by rw [h0]; exact zero_pow hx)
    simp [cTot, this]
  · intro τ
    have := hle (Sum.inl τ)
    rw [jn_inl, dTot_inl] at this
    exact this
  · have h3 := lowGe_mul (lowGe_pow hZlow (k (Sum.inr (Sum.inr 0))))
      (lowGe_zero (Y ^ k (Sum.inr (Sum.inr 1)) * U)) _ hv1
    have h4 := lowDeg_sub_le (jn e n) (dTot dA dB k)
    rw [lowDeg_jn] at h4
    show p * k (Sum.inr (Sum.inr 0)) ≤ n.degree
    omega
  · have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    set s := ∑ φ, k (Sum.inl φ) + ∑ x, β x + k (Sum.inr (Sum.inr 0)) with hs
    set cR := MvPolynomial.coeff n (hasseDir b β Q) with hcR
    have hx : ((p : K) ^ i)⁻¹ * (((Nat.multinomial univ k : ℕ) : K) *
        (((∏ x, (β x).factorial : ℕ) : K) * (cR * ((mfact e * mfact n : ℕ) : K) *
          (cTot p aA aB k * v)))) =
        (((p : K) ^ i)⁻¹ * (p : K) ^ k (Sum.inr (Sum.inr 1))) *
          ((Nat.multinomial univ k * ∏ x, (β x).factorial : ℕ) : K) * ((mfact e : ℕ) : K) *
          ((mfact n : ℕ) : K) * (cR * ((∏ φ, aA φ ^ k (Sum.inl φ)) *
            ((∏ x, aB x ^ k (Sum.inr (Sum.inl x))) * v))) := by
      unfold cTot
      push_cast
      ring
    rw [hx]
    have hpp : ‖((p : K) ^ i)⁻¹ * (p : K) ^ k (Sum.inr (Sum.inr 1))‖ = (p : ℝ) ^ s := by
      rw [norm_mul, norm_inv, norm_pow, norm_pow, hpn, ← hsum, pow_add, inv_pow, inv_pow, mul_inv,
        inv_inv, inv_inv, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp0.ne'), mul_one]
    have hm : ‖((Nat.multinomial univ k * ∏ x, (β x).factorial : ℕ) : K)‖ ≤
        ‖(((∑ x, β x).factorial : ℕ) : K)‖ := norm_natCast_le_of_dvd (fact_dvd k)
    have ht : ‖cR * ((∏ φ, aA φ ^ k (Sum.inl φ)) *
        ((∏ x, aB x ^ k (Sum.inr (Sum.inl x))) * v))‖ ≤ 1 := by
      rw [norm_mul, norm_mul, norm_mul]
      refine mul_le_one₀ ((h2 K Lw κ b β Q).1 hQ hb n) (by positivity) ?_
      refine mul_le_one₀ (norm_prod_pow_le_one _ _ _ haA) (by positivity) ?_
      refine mul_le_one₀ (norm_prod_pow_le_one _ _ _ haB) (norm_nonneg _) ?_
      exact integral_mul (integral_pow hZ _) (integral_mul (integral_pow hY _) hU) _
    rw [norm_mul, norm_mul, norm_mul, norm_mul, hpp]
    unfold bnd
    show _ ≤ (p : ℝ) ^ s * ‖((mfact e : ℕ) : K)‖ * ‖(((∑ x, β x).factorial : ℕ) : K)‖ *
      ‖((mfact n : ℕ) : K)‖
    calc _ ≤ (p : ℝ) ^ s * ‖(((∑ x, β x).factorial : ℕ) : K)‖ * ‖((mfact e : ℕ) : K)‖ *
          ‖((mfact n : ℕ) : K)‖ * 1 := by gcongr
      _ = _ := by ring

end Main

end ETerm

open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)

theorem TermBound_of (h1 : JetPairingHasseIdentity) (h2 : HasseDerivIntegralHomogeneous) : TermBound := by
  intro K Tp Lw Φ κ _ _ _ _ _ _ _ _ p D dQ h g Z Y aA dA aB dB b e Q hp hpn _ hg haA haB hb hZ hY
    hZlow hdec hQ hQh hD
  classical
  obtain ⟨U, hU, hgU⟩ := hg
  have hag : ETerm.Agree D h (∑ j, ETerm.piece p Z Y aA dA aB dB b j) := by
    rw [ETerm.sum_piece]
    exact hdec
  have hsupp : ∀ m ∈ (topMonoP e * lowPoly Q).support, m.degree = D := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 (ETerm.support_topLow e Q hm)
    have hnd : n.degree = dQ := by
      have := hQh (MvPolynomial.mem_support_iff.1 hn)
      rw [← this, Finsupp.degree_eq_weight_one]
      rfl
    rw [ETerm.degree_jn, hnd, hD]
  have key : jetPair (topMonoP e * lowPoly Q) g =
      ∑ i ∈ range (D + 1), ∑ k ∈ Finset.piAntidiag (univ : Finset (Φ ⊕ κ ⊕ Fin 2)) i,
        ((p : K) ^ i)⁻¹ * (((Nat.multinomial univ k : ℕ) : K) *
          jetPair (topMonoP e * lowPoly Q)
            ((∏ j, ETerm.piece p Z Y aA dA aB dB b j ^ k j) * U i)) := by
    have h0 : jetPair (topMonoP e * lowPoly Q) g = jetPair (topMonoP e * lowPoly Q)
        (∑ i ∈ range (D + 1), MvPowerSeries.C (((p : K) ^ i)⁻¹) *
          ((∑ j, ETerm.piece p Z Y aA dA aB dB b j) ^ i * U i)) := by
      refine ETerm.jetPair_congr _ _ _ fun m hm => ?_
      rw [hgU m, hsupp m hm, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MvPowerSeries.coeff_C_mul,
        ETerm.agree_mul (ETerm.agree_pow hag i) (ETerm.agree_refl D (U i)) m (hsupp m hm).le]
    rw [h0, Formalism.DworkPowerSeriesWeights.jetPair_sum_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Formalism.DworkPowerSeriesWeights.jetPair_C_mul_right, Finset.sum_pow_eq_sum_piAntidiag, Finset.sum_mul,
      Formalism.DworkPowerSeriesWeights.jetPair_sum_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc : ((Nat.multinomial univ k : ℕ) : MvPowerSeries (Tp ⊕ Lw) K) =
        MvPowerSeries.C ((Nat.multinomial univ k : ℕ) : K) := (map_natCast _ _).symm
    rw [mul_assoc, hc, Formalism.DworkPowerSeriesWeights.jetPair_C_mul_right]
  rw [key]
  have hmain := ETerm.closure_sum (ETerm.valid p aA dA aB dB b e Q) (ETerm.bnd K p e)
    (range (D + 1)) (fun i => ∑ k ∈ Finset.piAntidiag (univ : Finset (Φ ⊕ κ ⊕ Fin 2)) i,
        ((p : K) ^ i)⁻¹ * (((Nat.multinomial univ k : ℕ) : K) *
          jetPair (topMonoP e * lowPoly Q)
            ((∏ j, ETerm.piece p Z Y aA dA aB dB b j ^ k j) * U i)))
    (fun i _ => ETerm.closure_sum _ _ _ _ fun k hk =>
      ETerm.term_bound h1 h2 p Z Y aA dA aB dB b e Q hp hpn haA haB hb hZ hY hZlow hQ i k
        (Finset.mem_piAntidiag.1 hk).1 (U i) (hU i))
  rcases hmain with h0 | ⟨⟨α, β, i2, n⟩, hv, hbd⟩
  · exact Or.inl h0
  · exact Or.inr ⟨α, β, i2, n, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2, hbd⟩

end Formalism.InvariantFactorPaths.G7
