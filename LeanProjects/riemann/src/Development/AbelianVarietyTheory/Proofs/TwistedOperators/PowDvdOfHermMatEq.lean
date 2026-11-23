import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SatakeTrivialRangeBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelativeLatticeVolumeOfDetValuation
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLeCard
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsBorelSphRevInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLeOfCompleteHomogeneousLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermiteReductionUnipotent

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel

namespace GlobalTheory.SatakeBound

section Hermite

variable {R : Type} [CommRing R] {n : ℕ}

abbrev HermIdx (p : R) (a : Fin n → ℕ) : Type :=
  ∀ i : Fin n, {j : Fin n // i < j} → R ⧸ Ideal.span {p ^ a i}

def hermMat (p : R) (a : Fin n → ℕ) (c : HermIdx p a) : Matrix (Fin n) (Fin n) R := fun i j =>
  if h : i < j then (c i ⟨j, h⟩).out else if i = j then p ^ a i else 0

variable {p : R} {a a' : Fin n → ℕ}

theorem hermMat_lt (c : HermIdx p a) {i j : Fin n} (h : i < j) : hermMat p a c i j = (c i ⟨j, h⟩).out := by
  simp [hermMat, h]

theorem hermMat_diag (c : HermIdx p a) (i : Fin n) : hermMat p a c i i = p ^ a i := by simp [hermMat]

theorem hermMat_gt (c : HermIdx p a) {i j : Fin n} (h : j < i) : hermMat p a c i j = 0 := by
  simp [hermMat, h.not_gt, h.ne']

theorem det_hermMat (c : HermIdx p a) : (hermMat p a c).det = p ^ ∑ i, a i := by
  rw [Matrix.det_of_isUpperTriangular (M := hermMat p a c) (fun _ _ h => hermMat_gt c h), ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun i _ => hermMat_diag c i

theorem eq_zero_of_upper {b : Matrix (Fin n) (Fin n) R} (hb : ∀ i j, j < i → b i j = 0) (x : Fin n → R)
    (P : Fin n → Prop) (hP : ∀ l l', l < l' → P l → P l')
    (h : ∀ l, P l → b l l * x l = ∑ s, b l s * x s → x l = 0) (l : Fin n) : P l → x l = 0 := by
  induction l using WellFoundedGT.induction with
  | ind l ih =>
    intro hl
    refine h l hl (Finset.sum_eq_single (f := fun s => b l s * x s) l (fun s _ hs => ?_) (by simp)).symm
    rcases lt_or_gt_of_ne hs with h1 | h1
    · rw [hb _ _ h1, zero_mul]
    · rw [ih s h1 (hP _ _ h1 hl), mul_zero]

variable [IsDomain R]

theorem pow_dvd_of_hermMat_eq (hp : p ≠ 0) {c : HermIdx p a} {c' : HermIdx p a'} {W : Matrix (Fin n) (Fin n) R}
    (h : hermMat p a c = hermMat p a' c' * W) (i : Fin n) : p ^ a' i ∣ p ^ a i := by
  have hW : ∀ l, i < l → W l i = 0 :=
    eq_zero_of_upper (fun _ _ => hermMat_gt c') (fun l => W l i) _ (fun _ _ h1 h2 => h2.trans h1) fun l hl e => by
      rw [← Matrix.mul_apply, ← h, hermMat_gt c hl, hermMat_diag] at e
      exact (mul_eq_zero.1 e).resolve_left (pow_ne_zero _ hp)
  refine ⟨W i i, ?_⟩
  rw [← hermMat_diag c, h, Matrix.mul_apply, Finset.sum_eq_single i (fun s _ hs => ?_) (by simp), hermMat_diag]
  rcases lt_or_gt_of_ne hs with h1 | h1
  · rw [hermMat_gt c' h1, zero_mul]
  · rw [hW s h1, mul_zero]

theorem eq_of_hermMat_eq (hp : p ≠ 0) {c c' : HermIdx p a} {W : Matrix (Fin n) (Fin n) R}
    (h : hermMat p a c = hermMat p a c' * W) : c = c' := by
  have key : ∀ l j (hl : l < j), p ^ a l ∣ hermMat p a c l j - hermMat p a c' l j →
      c l ⟨j, hl⟩ = c' l ⟨j, hl⟩ := fun l j hl e => by
    rw [hermMat_lt c hl, hermMat_lt c' hl, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq] at e
    simpa using e
  have hW : W - 1 = 0 := by
    ext l j
    refine eq_zero_of_upper (fun _ _ => hermMat_gt c') (fun l => (W - 1) l j) (fun _ => True) (fun _ _ _ _ => trivial)
      (fun l _ e => ?_) l trivial
    rw [← Matrix.mul_apply, mul_sub, mul_one, ← h, hermMat_diag, Matrix.sub_apply (hermMat p a c)] at e
    have : hermMat p a c l j = hermMat p a c' l j := by
      rcases lt_trichotomy l j with h1 | rfl | h1
      · rw [hermMat_lt c h1, hermMat_lt c' h1, key l j h1 ⟨_, e.symm⟩]
      · rw [hermMat_diag, hermMat_diag]
      · rw [hermMat_gt c h1, hermMat_gt c' h1]
    rw [this, sub_self] at e
    exact (mul_eq_zero.1 e).resolve_left (pow_ne_zero _ hp)
  rw [sub_eq_zero.1 hW, mul_one] at h
  funext l ⟨j, hl⟩
  exact key l j hl (by simp [h])

theorem exists_hermMat [IsDiscreteValuationRing R] (hp : Irreducible p) (b : Matrix (Fin n) (Fin n) R)
    (hb : ∀ i j, j < i → b i j = 0) (h0 : ∀ i, b i i ≠ 0) :
    ∃ (a : Fin n → ℕ) (c : HermIdx p a) (W : GL (Fin n) R), hermMat p a c = b * W := by
  choose a u hu using fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (h0 i) hp
  let b' := b * Matrix.diagonal fun i => (((u i)⁻¹ : Rˣ) : R)
  have h1 : ∀ i j, j < i → b' i j = 0 := fun i j h => by simp [b', hb i j h]
  have h2 : ∀ i, b' i i = p ^ a i := fun i => by
    simp only [b', Matrix.mul_diagonal]
    rw [hu i, mul_comm, Units.inv_mul_cancel_left]
  obtain ⟨U, hU, hU1, hr⟩ := GlobalTheory.hermite_reduction_unipotent R n b' (fun i y => (Ideal.Quotient.mk (Ideal.span {p ^ a i}) y).out) h1
    fun i y => by
      rw [h2, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
      simp
  have hunit : IsUnit ((Matrix.diagonal fun i => (((u i)⁻¹ : Rˣ) : R)) * U) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.det_of_isUpperTriangular (M := U) fun _ _ h => hU _ _ h,
      Matrix.det_diagonal]
    simp [hU1, IsUnit.prod_iff]
  refine ⟨a, fun i j => Ideal.Quotient.mk _ ((b' * U) i j), hunit.unit, ?_⟩
  rw [hunit.unit_spec, ← mul_assoc]
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · obtain ⟨y, hy⟩ := hr i j h
    rw [hermMat_lt _ h]
    show (Ideal.Quotient.mk _ ((b' * U) i j)).out = (b' * U) i j
    rw [hy]
    simp
  · rw [hermMat_diag, Matrix.mul_apply, Finset.sum_eq_single i (fun s _ hs => ?_) (by simp), hU1, mul_one, ← h2]
    rcases lt_or_gt_of_ne hs with h | h
    · exact mul_eq_zero_of_left (h1 _ _ h) _
    · rw [hU _ _ h, mul_zero]
  · rw [hermMat_gt _ h]
    exact (Matrix.BlockTriangular.mul (b := id) (fun _ _ h => h1 _ _ h) (fun _ _ h => hU _ _ h) h).symm

end Hermite

section Count

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {p : 𝒪[k]}

def hermGL (hp : Irreducible p) (a : Fin n → ℕ) (c : HermIdx p a) : GL (Fin n) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((algebraMap 𝒪[k] k).mapMatrix (hermMat p a c)) (by
    rw [← RingHom.map_det, det_hermMat]
    simpa using fun h => absurd h hp.ne_zero)

theorem val_hermGL (hp : Irreducible p) (a : Fin n → ℕ) (c : HermIdx p a) :
    (hermGL hp a c).val = (algebraMap 𝒪[k] k).mapMatrix (hermMat p a c) := rfl

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mapMatrix_inj : Function.Injective ((algebraMap 𝒪[k] k).mapMatrix (m := Fin n)) :=
  fun A B h => by ext i j; exact congrFun (congrFun h i) j

theorem hermMat_eq_of_coe_eq (hp : Irreducible p) {a a' : Fin n → ℕ} {c : HermIdx p a} {c' : HermIdx p a'}
    (h : (hermGL hp a' c' : GL (Fin n) k ⧸ KO k (Fin n)) = hermGL hp a c) :
    ∃ W, hermMat p a c = hermMat p a' c' * W := by
  obtain ⟨W, hW⟩ := QuotientGroup.eq.1 h
  refine ⟨W, mapMatrix_inj ?_⟩
  rw [eq_inv_mul_iff_mul_eq] at hW
  rw [map_mul]
  exact (congrArg Units.val hW).symm

theorem hermGL_injective (hp : Irreducible p) : Function.Injective
    fun x : Σ a : Fin n → ℕ, HermIdx p a => (hermGL hp x.1 x.2 : GL (Fin n) k ⧸ KO k (Fin n)) := by
  rintro ⟨a, c⟩ ⟨a', c'⟩ h
  obtain ⟨W, hW⟩ := hermMat_eq_of_coe_eq hp h
  obtain ⟨W', hW'⟩ := hermMat_eq_of_coe_eq hp h.symm
  obtain rfl : a = a' := funext fun i => le_antisymm
    ((pow_dvd_pow_iff hp.ne_zero hp.not_isUnit).1 (pow_dvd_of_hermMat_eq hp.ne_zero hW i))
    ((pow_dvd_pow_iff hp.ne_zero hp.not_isUnit).1 (pow_dvd_of_hermMat_eq hp.ne_zero hW' i))
  exact congrArg (Sigma.mk a) (eq_of_hermMat_eq hp.ne_zero hW')

theorem exists_smul_hermGL (hp : Irreducible p) {x : GL (Fin n) k} (hx : x ∈ KO k (Fin n)) (a : Fin n → ℕ)
    (c : HermIdx p a) : ∃ (a' : Fin n → ℕ) (c' : HermIdx p a'), ∑ i, a' i = ∑ i, a i ∧
      (hermGL hp a' c' : GL (Fin n) k ⧸ KO k (Fin n)) = x • (hermGL hp a c : GL (Fin n) k ⧸ KO k (Fin n)) := by
  obtain ⟨b, hb, w, hw, e⟩ := iwasawa_blockTriangular k (Fin n) Fin.val (x * hermGL hp a c)
  obtain ⟨X, rfl⟩ := hx
  obtain ⟨W, rfl⟩ := hw
  let B : Matrix (Fin n) (Fin n) 𝒪[k] := X.val * hermMat p a c * (W⁻¹).val
  have hB : b.val = (algebraMap 𝒪[k] k).mapMatrix B := by
    rw [eq_mul_inv_of_mul_eq e.symm, ← map_inv, map_mul, map_mul]
    rfl
  have h1 : ∀ i j, j < i → B i j = 0 := fun i j h => Subtype.ext ((congrFun (congrFun hB i) j).symm.trans (hb h))
  have hd : B.det ≠ 0 := by
    simp only [B, Matrix.det_mul, det_hermMat]
    exact mul_ne_zero (mul_ne_zero (Matrix.isUnits_det_units _).ne_zero (pow_ne_zero _ hp.ne_zero))
      (Matrix.isUnits_det_units _).ne_zero
  rw [Matrix.det_of_isUpperTriangular (M := B) fun _ _ h => h1 _ _ h, Finset.prod_ne_zero_iff] at hd
  obtain ⟨a', c', U, hU⟩ := exists_hermMat hp B h1 fun i => hd i (Finset.mem_univ i)
  refine ⟨a', c', ?_, ?_⟩
  · have h := congrArg Matrix.det hU
    simp only [B, Matrix.det_mul, det_hermMat] at h
    refine IsDiscreteValuationRing.unit_mul_pow_congr_pow hp hp 1 (Matrix.GeneralLinearGroup.det (X * W⁻¹ * U)) _ _ ?_
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Matrix.det_mul, Units.val_one, h]
    ring
  · have : hermGL hp a' c' = b * Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) U := by
      apply Units.ext
      rw [val_hermGL, hU, map_mul, ← hB]
      rfl
    rw [this, MulAction.Quotient.smul_mk, smul_eq_mul, e, QuotientGroup.mk_mul_of_mem (s := KO k (Fin n)) _ (MonoidHom.mem_range.2 ⟨U, rfl⟩),
      QuotientGroup.mk_mul_of_mem (s := KO k (Fin n)) _ (MonoidHom.mem_range.2 ⟨W, rfl⟩)]

theorem apply_hermGL (hp : Irreducible p) {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (h : IsBorelSph k γ φ)
    (a : Fin n → ℕ) (c : HermIdx p a) :
    φ (hermGL hp a c : GL (Fin n) k ⧸ KO k (Fin n)).out = ∏ i, γ i ^ a i := by
  obtain ⟨y, hy⟩ := QuotientGroup.mk_out_eq_mul (KO k (Fin n)) (hermGL hp a c)
  have h0 : (p : k) ≠ 0 := by simpa using hp.ne_zero
  have hq : (1 : ℝ) < resCard k := by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard k
  have ho : ∀ m : ℕ, ord k (Units.mk0 _ h0 ^ m) = m := fun m => by
    have h1 := GlobalTheory.LGrp.nabs_eq_zpow (Units.mk0 _ h0 ^ m)
    have h2 : nabs k (Units.mk0 _ h0 ^ m) = nabs k (Units.mk0 _ h0) ^ m := by simp [nabs]
    rw [h2, nabs_uniformiser hp (x := Units.mk0 _ h0) rfl, inv_pow, ← zpow_natCast, ← _root_.zpow_neg] at h1
    exact neg_injective (zpow_right_injective₀ (by positivity) hq.ne' h1).symm
  rw [hy, h.1 _ _ y.2, h.2 _ ((mem_borel k).2 fun i j hij => ?_) (fun i => Units.mk0 _ h0 ^ a i) fun i => ?_]
  · simp only [ho, zpow_natCast]
  · simp [val_hermGL, hermMat_gt c hij]
  · simp [val_hermGL, hermMat_diag]
    rfl

theorem card_quot (hp : Irreducible p) (m : ℕ) : Nat.card (𝒪[k] ⧸ Ideal.span {p ^ m}) = resCard k ^ m := by
  rw [GlobalTheory.HL.LatDet.card_quot_pow hp, ← hp.maximalIdeal_eq]
  rfl

theorem card_hermIdx (hp : Irreducible p) (a : Fin n → ℕ) :
    Nat.card (HermIdx p a) = ∏ i : Fin n, (resCard k ^ (n - 1 - (i : ℕ))) ^ a i := by
  rw [Nat.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.card_fun, card_quot hp, ← pow_mul, ← pow_mul, mul_comm, ← Fin.card_Ioi, Nat.card_eq_fintype_card,
    Fintype.card_subtype]
  congr 3
  ext; simp

theorem exists_cosets_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (m : ℕ), ∃ S : Finset (GL (Fin n) k ⧸ KO k (Fin n)), (∀ x ∈ KO k (Fin n), ∀ c ∈ S, x • c ∈ S) ∧ ∀ (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → ∑ c ∈ S, φ c.out = ∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ i : Fin n, ((resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i) ^ a i := by
  intro k _ _ _ _ n m
  classical
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have hq := GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard k
  have hfin : ∀ a : Fin n → ℕ, Finite (HermIdx p a) := fun a => Nat.finite_of_card_ne_zero (by
    rw [card_hermIdx hp]; positivity)
  let _ : ∀ a : Fin n → ℕ, Fintype (HermIdx p a) := fun a => Fintype.ofFinite _
  refine ⟨((Finset.piAntidiag Finset.univ m).sigma fun a => (Finset.univ : Finset (HermIdx p a))).map
    ⟨_, hermGL_injective hp⟩, fun x hx c hc => ?_, fun γ φ h => ?_⟩
  · obtain ⟨⟨a, c⟩, h, rfl⟩ := Finset.mem_map.1 hc
    obtain ⟨a', c', h1, h2⟩ := exists_smul_hermGL hp hx a c
    refine Finset.mem_map.2 ⟨⟨a', c'⟩, ?_, h2⟩
    simp only [Finset.mem_sigma, Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true] at h ⊢
    exact h1.trans h
  · rw [Finset.sum_map, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Function.Embedding.coeFn_mk, apply_hermGL hp h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, card_hermIdx hp, mul_pow, Finset.prod_mul_distrib]
    push_cast
    rfl

end Count

theorem norm_le_pow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (h : IsBorelSph k γ φ) (hb : HasBoundedSums k φ)
    (i : Fin n) : ‖γ i‖ ≤ (resCard k : ℝ) ^ (i : ℕ) := by
  have hq : (1 : ℝ) < resCard k := by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard k
  have key := GlobalTheory.CompleteHomogeneousBound.norm_le_of_completeHomogeneous_le n (fun i => (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i)
    (fun i => (resCard k : ℝ) ^ (n - 1 - (i : ℕ))) ((resCard k : ℝ) ^ (n - 1)) (fun _ => by positivity)
    (fun i => pow_le_pow_right₀ hq.le (Nat.sub_le _ _)) (fun m => by
      obtain ⟨S, hS, hs⟩ := exists_cosets_sum k n m
      have h1 := hs _ _ (isBorelSph_one k)
      rw [← hs γ φ h]
      refine (hb S hS).trans (le_of_eq ?_)
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h1
      exact_mod_cast h1) i
  have hi : n - 1 = (n - 1 - (i : ℕ)) + i := by have := i.2; omega
  rw [norm_mul, norm_pow, Complex.norm_natCast] at key
  conv_rhs at key => rw [hi, pow_add]
  exact le_of_mul_le_mul_left key (by positivity)

theorem satakeTrivialBound : GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.SatakeTrivialBound := by
  intro k _ _ _ _ n V _ _ π α _ _ hu _ hs i
  have hq : (0 : ℝ) < resCard k := by exact_mod_cast (GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard k).le
  obtain ⟨φ, h, hb⟩ := GlobalTheory.SatakeBound.Rep.exists_sph k n V π α hu hs
  obtain ⟨ψ, h', hb'⟩ := GlobalTheory.SatakeFlip.exists_isBorelSph_rev_inv k n _ φ h hb
  have h1 := norm_le_pow h hb i
  have h2 := norm_le_pow h' hb' i.rev
  have hr : ((i.rev : ℕ) : ℝ) = (n : ℝ) - 1 - (i : ℕ) := by
    have := i.2
    rw [Fin.val_rev, Nat.cast_sub (by omega)]; push_cast; ring
  have ha : 0 < ‖(α i : ℂ)‖ := norm_pos_iff.2 (α i).ne_zero
  simp only [Fin.rev_rev, norm_inv, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hq.le _),
    ← Real.rpow_natCast, hr] at h1 h2
  rw [← le_div_iff₀ (Real.rpow_pos_of_pos hq _), ← Real.rpow_sub hq] at h1
  rw [inv_le_comm₀ (by positivity) (by positivity), ← div_le_iff₀ (Real.rpow_pos_of_pos hq _),
    ← Real.rpow_neg hq.le, ← Real.rpow_sub hq] at h2
  constructor
  · exact le_of_eq_of_le (congrArg _ (by ring)) h2
  · exact h1.trans_eq (congrArg _ (by ring))

end GlobalTheory.SatakeBound
