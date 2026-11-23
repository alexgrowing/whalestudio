import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationOfHyp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOddPrimeGtTwoBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallEstimateImpliesFrameAutomorphyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameGal

section Poly

open Polynomial Formalism.L2.Col

variable {K : Type} [Field K]

theorem charpoly_smul [CharZero K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K} (hc : c ≠ 0) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

theorem scaleRoots_prod (M : Multiset K) (c : K) :
    (M.map fun m => X - C m).prod.scaleRoots c = (M.map fun m => X - C (m * c)).prod := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, mul_scaleRoots_of_noZeroDivisors, ih,
      sub_eq_add_neg, ← C_neg, X_add_C_scaleRoots, neg_mul, C_neg, ← sub_eq_add_neg]

theorem reverse_X_sub (m : K) : (X - C m : K[X]).reverse = 1 - C m * X := by
  rw [sub_eq_add_neg, ← C_neg, reverse_add_C, natDegree_X, ← one_mul (X : K[X]), reverse_mul_X, ← C_1, reverse_C]
  simp [sub_eq_add_neg]

theorem reverse_prod (M : Multiset K) : (M.map fun m => X - C m).prod.reverse = (M.map fun m => 1 - C m * X).prod := by
  induction M using Multiset.induction_on with
  | empty => simpa using reverse_C (1 : K)
  | cons a s ih => rw [Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, reverse_mul_of_domain, ih, reverse_X_sub]

theorem reverse_prod_eq_hecke {n q : ℕ} (M : Multiset K) (hM : M.card = n) (a : ℕ → K)
    (ha : ∀ k ≤ n, (q : K) ^ (k * (k - 1) / 2) * a k = M.esymm k) :
    (M.map fun m => X - C m).prod.reverse = heckePolyOf n q a := by
  ext i
  have hd : (M.map fun m => X - C m).prod.natDegree = n := by rw [natDegree_multiset_prod_X_sub_C_eq_card, hM]
  rw [coeff_reverse, hd, heckePolyOf, finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  by_cases hi : i ≤ n
  · rw [if_pos (Finset.mem_range.2 (by omega)), revAt_le hi, Multiset.prod_X_sub_C_coeff _ (by omega), hM,
      show n - (n - i) = i by omega, mul_assoc, ha i hi]
  · rw [if_neg (by rw [Finset.mem_range]; omega), revAt_eq_self_of_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

theorem le_of_dvd {M₀ M : Multiset K} (h₀ : ∀ m ∈ M₀, m ≠ 0) (h : ∀ m ∈ M, m ≠ 0)
    (hd : (M₀.map fun m => 1 - C m * X).prod ∣ (M.map fun m => 1 - C m * X).prod) : M₀ ≤ M := by
  have key : ∀ N : Multiset K, (∀ m ∈ N, m ≠ 0) →
      (N.map fun m => 1 - C m * X).prod = C (N.map fun m => -m).prod * ((N.map (·⁻¹)).map fun m => X - C m).prod := by
    intro N hN
    rw [map_multiset_prod, Multiset.map_map, Multiset.map_map, ← Multiset.prod_map_mul]
    refine congrArg _ (Multiset.map_congr rfl fun m hm => ?_)
    simp only [Function.comp_apply]
    rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ (hN m hm)]
    simp [sub_eq_add_neg, add_comm]
  rw [key _ h₀, key _ h] at hd
  have hu : (M.map fun m => -m).prod ≠ 0 := Multiset.prod_ne_zero fun h0 => by
    obtain ⟨m, hm, e⟩ := Multiset.mem_map.1 h0
    exact h m hm (neg_eq_zero.1 e)
  have h1 := (dvd_mul_left _ _).trans hd
  rw [(isUnit_C.2 hu.isUnit).dvd_mul_left,
    Multiset.prod_X_sub_C_dvd_iff_le_roots (monic_multiset_prod_of_monic _ _ fun _ _ => monic_X_sub_C _).ne_zero,
    roots_multiset_prod_X_sub_C] at h1
  exact (Multiset.map_le_map_iff inv_injective).1 h1

theorem esymm_map_mul (t : K) (M : Multiset K) (j : ℕ) : (M.map fun b => b * t).esymm j = t ^ j * M.esymm j := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, ← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun s hs => ?_)
  have hc := (Multiset.mem_powersetCard.1 hs).2
  simp only [Function.comp, Multiset.prod_map_mul, Multiset.map_id', Multiset.map_const', Multiset.prod_replicate, hc]
  ring

theorem esymm_map_hom {K' : Type} [Field K'] (f : K →+* K') (M : Multiset K) (j : ℕ) : (M.map f).esymm j = f (M.esymm j) := by
  unfold Multiset.esymm
  rw [Multiset.powersetCard_map, Multiset.map_map, map_multiset_sum, Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun s _ => ?_)
  simp only [Function.comp, map_multiset_prod]

theorem pow_key {q : ℕ} (hq : q ≠ 0) (n j : ℕ) :
    (q : ℂ) ^ (j * (j - 1) / 2) * (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) = ((q : ℂ) ^ (((n : ℂ) - 1) / 2)) ^ j := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have e : (((j * (j - 1) / 2 : ℕ)) : ℂ) = (j : ℂ) * ((j : ℂ) - 1) / 2 := by
    obtain ⟨k, hk⟩ := Nat.even_mul_pred_self j
    have e1 : j * (j - 1) / 2 = k := by omega
    have e2 : ((j * (j - 1) : ℕ) : ℂ) = (j : ℂ) * ((j : ℂ) - 1) := by
      rcases j with _ | m
      · simp
      · push_cast; simp
    rw [e1, ← e2, hk]; push_cast; ring
  rw [← Complex.cpow_natCast, e, ← Complex.cpow_add _ _ hq', ← Complex.cpow_nat_mul]
  congr 1; ring

theorem satEig_esymm (ι : K ≃+* ℂ) {q n : ℕ} (hq : q ≠ 0) (S : Multiset ℂˣ) (k : ℕ) {a : K} (ha : ι a = GlobalTheory.LFun.satEig q n S k) :
    (q : K) ^ (k * (k - 1) / 2) * a = (S.map fun z : ℂˣ => ι.symm ((z : ℂ) * (q : ℂ) ^ (((n : ℂ) - 1) / 2))).esymm k := by
  have e : (S.map fun z : ℂˣ => ι.symm ((z : ℂ) * (q : ℂ) ^ (((n : ℂ) - 1) / 2))) =
      ((S.map fun z : ℂˣ => (z : ℂ)).map fun b => b * (q : ℂ) ^ (((n : ℂ) - 1) / 2)).map ι.symm.toRingHom := by
    rw [Multiset.map_map, Multiset.map_map]; rfl
  rw [e, esymm_map_hom, esymm_map_mul, ← pow_key hq]
  apply ι.injective
  rw [map_mul, ha, GlobalTheory.LFun.satEig]
  simp [mul_assoc]

theorem reverse_scale_eq_hecke (ι : K ≃+* ℂ) {q n : ℕ} (hq : q ≠ 0) (S : Multiset ℂˣ) (hS : S.card = n) (a : ℕ → K)
    (ha : ∀ k ≤ n, ι (a k) = GlobalTheory.LFun.satEig q n S k) (c : K) :
    ((S.map fun z : ℂˣ => X - C (ι.symm ((z : ℂ) * (q : ℂ) ^ (((n : ℂ) - 1) / 2)))).prod.scaleRoots c).reverse =
      heckePolyOf n q fun k => a k * c ^ k := by
  have e := scaleRoots_prod (S.map fun z : ℂˣ => ι.symm ((z : ℂ) * (q : ℂ) ^ (((n : ℂ) - 1) / 2))) c
  rw [Multiset.map_map] at e
  have e' := reverse_prod_eq_hecke (q := q)
    ((S.map fun z : ℂˣ => ι.symm ((z : ℂ) * (q : ℂ) ^ (((n : ℂ) - 1) / 2))).map fun b => b * c) (by simpa using hS)
    (fun k => a k * c ^ k) fun k hk => by rw [esymm_map_mul, ← satEig_esymm ι hq S k (ha k hk)]; ring
  rw [Multiset.map_map] at e'
  exact (congrArg reverse e).trans e'

theorem string_of_dvd (ι : K ≃+* ℂ) {q n t : ℕ} (hq : q ≠ 0) (ht : t ≤ n) (S : Multiset ℂˣ) (hS : S.card = n) (a : ℕ → K)
    (ha : ∀ k ≤ n, ι (a k) = GlobalTheory.LFun.satEig q n S k) (ν : K) (hν : ‖ι ν‖ ^ 2 = (q : ℝ) ^ (n - t))
    (hd : blockPoly ν q t ∣ heckePolyOf n q a) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ (Multiset.range t).map (fun c : ℕ => u * (q : ℂ) ^ (((t : ℂ) - 1) / 2 - c)) ≤ S.map fun z : ℂˣ => (z : ℂ) := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hqr : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have hc : ∀ x : ℂ, (q : ℂ) ^ x ≠ 0 := fun x h => hq' ((Complex.cpow_eq_zero_iff _ _).1 h).1
  have hν0 : ι ν ≠ 0 := fun h => by
    rw [h, norm_zero, zero_pow two_ne_zero] at hν
    exact (pow_pos hqr _).ne hν
  have h1 := Polynomial.map_dvd ι.toRingHom hd
  rw [map_blockPoly, map_heckePolyOf, ← reverse_prod_eq_hecke
    (S.map fun z : ℂˣ => (RingEquiv.refl ℂ).symm ((z : ℂ) * (q : ℂ) ^ (((n : ℂ) - 1) / 2))) (by simpa using hS) (fun i => ι.toRingHom (a i))
    (fun k hk => satEig_esymm (RingEquiv.refl ℂ) hq S k (ha k hk)), reverse_prod, blockPoly, ← Finset.prod_range_reflect] at h1
  have h2 := le_of_dvd (M₀ := (Multiset.range t).map fun c : ℕ => ι ν * (q : ℂ) ^ (t - 1 - c))
    (M := S.map fun z : ℂˣ => (RingEquiv.refl ℂ).symm ((z : ℂ) * (q : ℂ) ^ (((n : ℂ) - 1) / 2))) (fun m hm => by
    obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 hm
    exact mul_ne_zero hν0 (pow_ne_zero _ hq')) (fun m hm => by
    obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 hm
    exact mul_ne_zero c.ne_zero (hc _)) (by rw [Multiset.map_map]; exact h1)
  have h3 := Multiset.map_le_map (f := fun x : ℂ => x * (q : ℂ) ^ (-(((n : ℂ) - 1) / 2))) h2
  rw [Multiset.map_map, Multiset.map_map] at h3
  refine ⟨ι ν * (q : ℂ) ^ (((t : ℂ) - n) / 2), ?_, ?_⟩
  · have e : (((t : ℂ) - n) / 2) = ((((t : ℝ) - n) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [← pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero, norm_mul, mul_pow, hν, e,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hq), Complex.ofReal_re, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hqr.le, ← Real.rpow_add hqr, Nat.cast_sub ht]
    norm_num
  · convert h3 using 1
    · refine Multiset.map_congr rfl fun c hc => ?_
      have hct : c < t := Multiset.mem_range.1 hc
      simp only [Function.comp_apply]
      rw [mul_assoc, mul_assoc, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq', ← Complex.cpow_add _ _ hq',
        Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      congr 2
      push_cast; ring
    · refine Multiset.map_congr rfl fun z _ => ?_
      simp only [Function.comp_apply, RingEquiv.symm_refl, RingEquiv.refl_apply]
      rw [mul_assoc, ← Complex.cpow_add _ _ hq', add_neg_cancel, Complex.cpow_zero, mul_one]

end Poly

section Runs

open Formalism.BasicNotions Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds GlobalTheory.GalDef

theorem drops {T : Type} {P : Par} {W : Wts T} (hP : P.Hyp) (hL : P.Large) (hW : W.Ok P) (τ : T) :
    (1 ≤ kc P + W.j τ → W.lam τ (kc P + W.j τ) < W.lam τ (kc P + W.j τ - 1)) ∧
    (kc P + W.j τ + P.t < P.Nr → W.lam τ (kc P + W.j τ + P.t) < W.lam τ (kc P + W.j τ)) := by
  have hrows := hW.what₂ τ
  have ht := hP.t_ge
  have hm := hP.m_pos
  have hk := hP.m_le
  have htr : (6 : ℝ) ≤ P.t := by exact_mod_cast (by omega : 6 ≤ P.t)
  have hkr : (1 : ℝ) ≤ P.k := by exact_mod_cast (by omega : 1 ≤ P.k)
  have hl : 0 ≤ 2 * P.b / P.lstar := by
    have := hL.L_ge
    have := hP.S_nonneg
    have hL0 : 0 ≤ P.L := by linarith
    unfold Par.lstar Par.N Par.b
    positivity
  have hb : W.bot P τ = (W.lam τ (kc P + W.j τ) : ℤ) + P.Nr - (kc P + W.j τ + P.t : ℕ) := by
    unfold Wts.bot Wts.U Formalism.CohomologicalDescent.UnitNormBounds.UN
    rw [hW.block τ _ (by omega) (by omega)]
    omega
  have hc := hW.centre τ
  have he : (P.t : ℝ) < W.e τ := by
    have hw : 2 * (P.t : ℝ) < P.w'' := by have := hL.w_gt; linarith
    have hb' := hP.b'_pos
    have hx := hP.x_ge
    have hn : (1 : ℝ) ≤ P.n := by exact_mod_cast hP.n_pos
    have hw' : P.w'' ≤ P.b' := div_le_self hb'.le (one_le_mul_of_one_le_of_one_le hx hn)
    by_cases h2 : τ ∈ W.T2
    · have h3 := (hW.thick τ h2).1.1
      have h4 := hL.b_gt
      have h5 : (1 : ℝ) ≤ (P.k : ℝ) ^ 2 := one_le_pow₀ hkr
      nlinarith [mul_le_mul_of_nonneg_right h5 (sq_nonneg (P.t : ℝ))]
    · rcases hW.other τ h2 with ⟨⟨bt, h3, -, h4, -⟩, -⟩ | ⟨⟨h3, -⟩, -⟩
      · have : 0 ≤ P.b' / P.x := by positivity
        linarith
      · linarith
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · refine lt_of_le_of_ne (hW.anti τ _ _ (by omega) (by omega)) fun e => ?_
    have hU : W.U P τ (kc P + W.j τ - 1) = W.bot P τ + P.t := by
      rw [hb]
      unfold Wts.U Formalism.CohomologicalDescent.UnitNormBounds.UN
      rw [← e]
      omega
    by_cases hj : W.j τ = 0
    · have h2 := (hW.cloud τ (kc P + W.j τ - 1) (by omega)).1
      have h3 := (hW.window τ).1
      rw [hU] at h2
      have h4 : (W.xm τ : ℝ) ≤ (W.bot P τ : ℝ) + P.t := by exact_mod_cast h2
      linarith
    · have h2 := (hW.low τ (kc P + W.j τ - 1) (by omega) (Or.inl (by omega))).1
      rw [hU, show ((W.bot P τ + P.t : ℤ) : ℝ) - W.c τ + W.e τ = ((P.t : ℝ) + 1) / 2 by push_cast; linarith,
        abs_of_nonneg (by linarith)] at h2
      linarith
  · refine lt_of_le_of_ne (hW.anti τ _ _ (by omega) h1) fun e => ?_
    have hU : W.U P τ (kc P + W.j τ + P.t) = W.bot P τ - 1 := by
      rw [hb]
      unfold Wts.U Formalism.CohomologicalDescent.UnitNormBounds.UN
      rw [e]
      omega
    have h2 := (hW.low τ (kc P + W.j τ + P.t) h1 (Or.inr le_rfl)).1
    rw [hU, show ((W.bot P τ - 1 : ℤ) : ℝ) - W.c τ + W.e τ = -(((P.t : ℝ) + 1) / 2) by push_cast; linarith,
      abs_neg, abs_of_nonneg (by linarith)] at h2
    linarith

theorem wAt_of_lt {n : ℕ} (lam : DomWeight n) {k : ℕ} (h : k < n) : wAt lam k = lam.w ⟨k, h⟩ := dif_pos h

theorem wAt_dual {n : ℕ} (lam : DomWeight n) {k : ℕ} (h : k < n) : wAt lam.dual k = -wAt lam (n - 1 - k) := by
  rw [wAt_of_lt _ h, wAt_of_lt _ (show n - 1 - k < n by omega)]
  show -lam.w _ = -lam.w _
  congr 2
  exact Fin.ext (by simp only [Fin.val_rev]; omega)

theorem isRunAt_dual {n p t : ℕ} {lam : DomWeight n} (ht : 1 ≤ t) (h : IsRunAt lam p t) :
    IsRunAt lam.dual (n - p - t) t ∧ wAt lam.dual (n - p - t) = -wAt lam p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e : wAt lam.dual (n - p - t) = -wAt lam p := by rw [wAt_dual _ (by omega), h2 _ (by omega) (by omega)]
  refine ⟨⟨by omega, fun k a b => ?_, fun a => ?_, fun a => ?_⟩, e⟩
  · rw [e, wAt_dual _ (by omega), h2 _ (by omega) (by omega)]
  · rw [e, wAt_dual _ (by omega), show n - 1 - (n - p - t - 1) = p + t by omega]
    have := h4 (by omega)
    omega
  · rw [e, wAt_dual _ (by omega), show n - 1 - (n - p - t + t) = p - 1 by omega]
    have := h3 (by omega)
    omega

theorem isRunAt_block {T : Type} {P : Par} {W : Wts T} (hP : P.Hyp) (hL : P.Large) (hW : W.Ok P) (τ : T) (lam : DomWeight P.Nr) (s : ℤ)
    (h : ∀ a, lam.w a = (W.lam τ a : ℤ) + s) :
    IsRunAt lam (kc P + W.j τ) P.t ∧ wAt lam (kc P + W.j τ) = W.bot P τ + s - P.Nr + (kc P + W.j τ + P.t : ℕ) := by
  have hrows := hW.what₂ τ
  have ht := hP.t_ge
  have hw : ∀ k, k < P.Nr → wAt lam k = (W.lam τ k : ℤ) + s := fun k hk => by rw [wAt_of_lt _ hk, h]
  obtain ⟨d1, d2⟩ := drops hP hL hW τ
  refine ⟨⟨by omega, fun k a b => ?_, fun a => ?_, fun a => ?_⟩, ?_⟩
  · rw [hw _ (by omega), hw _ (by omega), hW.block τ k a b]
  · rw [hw _ (by omega), hw _ (by omega)]
    have := d1 a
    omega
  · rw [hw _ (by omega), hw _ (by omega)]
    have := d2 a
    omega
  · rw [hw _ (by omega)]
    unfold Wts.bot Wts.U Formalism.CohomologicalDescent.UnitNormBounds.UN
    rw [hW.block τ (kc P + W.j τ + P.t - 1) (by omega) (by omega)]
    omega

end Runs

section Galois

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.ExpFrame GlobalTheory.TripleGal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]

theorem continuous_twist {n : ℕ} {r r' : G E Ω →* GL (Fin n) (Qbar l)} {μ : G E Ω →* (Qbar l)ˣ}
    (h : ∀ g, (r' g).val = ((μ g : (Qbar l)ˣ) : Qbar l) • (r g).val) (hr : Continuous r) (hμ : Continuous μ) : Continuous r' := by
  have hv : Continuous fun g => (r' g).val := by
    simp only [h]
    exact (Units.continuous_val.comp hμ).smul (Units.continuous_val.comp hr)
  refine Units.continuous_iff.2 ⟨hv, ?_⟩
  simp only [← map_inv]
  exact hv.comp continuous_inv

theorem crysWith_twist {n : ℕ} {r r' : G E Ω →* GL (Fin n) (Qbar l)} {μ : G E Ω →* (Qbar l)ˣ}
    (h : ∀ g, (r' g).val = ((μ g : (Qbar l)ˣ) : Qbar l) • (r g).val) {J : (E →+* Qbar l) → Multiset ℤ} {c : (E →+* Qbar l) → ℤ}
    (hr : CrysWith r J) (hc : Continuous μ) (hμ : CrysWith (rk1 μ) fun τ => {c τ}) : CrysWith r' fun τ => (J τ).map (· + c τ) := by
  refine ⟨continuous_twist h hr.1 hc, fun P AI hT w A hA O _ _ _ Bw hB => ?_⟩
  have h1 := hr.2 P AI hT w A hA O Bw hB
  have h2 := hμ.2 P AI hT w A hA O Bw hB
  have H := GlobalTheory.TwistAbove.twist_above l P AI hT E Ω _ O Bw n (r.comp (Dec (F := E) A).subtype) (r'.comp (Dec (F := E) A).subtype)
    (μ.comp (Dec (F := E) A).subtype) fun g => h g
  exact ⟨H.2.1 h1.1 h2.1, fun τ LL' τ' hτ => H.2.2.2 τ _ _ (h1.2 τ LL' τ' hτ) (h2.2 τ LL' τ' hτ)⟩

variable [IsCMField E]

theorem cj_cj (τ : E →+* Qbar l) : cj (cj τ) = τ := by
  ext x
  show τ (IsCMField.complexConj E (IsCMField.complexConj E x)) = τ x
  rw [IsCMField.complexConj_apply_apply]

theorem exists_of_half {T A : Type} {inc : T → (E →+* Qbar l)} (h : IsHalf inc) (f f' : T → A) :
    ∃ F : (E →+* Qbar l) → A, (∀ τ, F (inc τ) = f τ) ∧ ∀ τ, F (cj (inc τ)) = f' τ := by
  let e : T ⊕ T → (E →+* Qbar l) := Sum.elim inc fun τ => cj (inc τ)
  have hi : Function.Injective e := by
    rintro (a | a) (b | b) hab
    · exact congrArg _ (h.1 hab)
    · exact absurd hab.symm (h.2.1 b a)
    · exact absurd hab (h.2.1 a b)
    · exact congrArg _ (h.1 ((cj_cj _).symm.trans ((congrArg cj hab).trans (cj_cj _))))
  have hs : Function.Surjective e := fun i => by
    obtain ⟨τ, a | a⟩ := h.2.2 i
    exacts [⟨.inl τ, a.symm⟩, ⟨.inr τ, a.symm⟩]
  let e' := Equiv.ofBijective e ⟨hi, hs⟩
  exact ⟨fun i => Sum.elim f f' (e'.symm i), fun τ => congrArg (Sum.elim f f') (e'.symm_apply_apply (.inl τ)),
    fun τ => congrArg (Sum.elim f f') (e'.symm_apply_apply (.inr τ))⟩

variable (Ω) in

theorem exists_crys_char (h1 : GlobalTheory.Published.HeckeLAdicCharacter) (h2 : GlobalTheory.Published.HeckeLAdicCharacterAbove) (ι : Qbar l ≃+* ℂ)
    (c : (E →+* Qbar l) → ℤ) (w0 : ℤ) (hc : ∀ τ, c τ + c (cj τ) = w0) :
    ∃ μ : G E Ω →* (Qbar l)ˣ, Continuous μ ∧ CrysWith (rk1 μ) fun τ => {c τ} := by
  obtain ⟨χ, hχ, hu⟩ := GlobalTheory.AlgCharUnr.exists_algChar_unr E l Fact.out (fun φ => -c (ι.symm.toRingHom.comp φ)) (-w0) fun φ => by
    have e : ι.symm.toRingHom.comp (ComplexEmbedding.conjugate φ) = cj (ι.symm.toRingHom.comp φ) := by
      ext x
      show ι.symm (starRingEnd ℂ (φ x)) = ι.symm (φ (IsCMField.complexConj E x))
      rw [IsCMField.complexEmbedding_complexConj]
    rw [e, ← hc (ι.symm.toRingHom.comp φ)]
    ring
  obtain ⟨art, ha, H⟩ := h1 E Ω
  obtain ⟨μ, ⟨hμ, hL⟩, -⟩ := H l ι χ _ hχ
  refine ⟨μ, hμ, continuous_twist (r := 1) (μ := μ) (fun g => ?_) continuous_const hμ, fun P AI hT w A hA O _ _ _ Bw hB => ?_⟩
  · ext a b
    simp [rk1, Matrix.diagonal_apply, Matrix.one_apply]
  · have H2 := h2 E Ω l P AI hT ι art ha χ _ μ hχ hμ hL w A hA O Bw hB
    refine ⟨H2.2.2.1 (hu w (hB.mem_placesOver hA)), fun τ LL' τ' hτ => ?_⟩
    have e : ι.symm.toRingHom.comp (ι.toRingHom.comp τ) = τ := by ext x; simp
    have := H2.2.2.2 τ LL' τ' hτ
    rwa [e, neg_neg] at this

end Galois

section Side

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.ExpFrame GlobalTheory.TripleGal GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.GalDef
open Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.L2.Col Polynomial

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] [IsCMField E]

def SystemOf (ι : Qbar l ≃+* ℂ) {T : Type} (inc : T → (E →+* Qbar l)) (s : T → ℤ) {Pl : Type} (lab : Pl → HeightOneSpectrum (𝓞 E))
    (n : ℕ) (mu : T → ℕ → ℕ) (θ : Pl → ℕ → Qbar l) (π : Submodule ℂ (UA E n → ℂ)) : Prop :=
  IsAutRepU π ∧
  (∀ τ, ∃ lam : DomWeight n, (∀ a, lam.w a = (mu τ a : ℤ) + s τ) ∧ HasWeightAt π (ι.toRingHom.comp (inc τ)) lam ∧
    HasWeightAt π (ι.toRingHom.comp (cj (inc τ))) lam.dual) ∧
  (∀ v : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ v.asIdeal → IsUnramU π v) ∧
  ∀ Q, IsUnramU π (lab Q) ∧ ∃ (σ : SmIrr (GL (Fin n) ((lab Q).adicCompletion E))) (S : Multiset ℂˣ),
    IsCompAlong π (locU n (lab Q)) ((cLoc (lab Q)).comp (locU n (lab Q)).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL (lab Q) σ.ρ S ∧
      ∀ k ≤ n, ι (θ Q k) = GlobalTheory.LFun.satEig (Ideal.absNorm (lab Q).asIdeal) n S k

omit [IsCMField E] in
theorem card_of_hasSat {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {S : Multiset ℂˣ} (h : GlobalTheory.LFun.HasSatGL w ρ S) : S.card = n := by
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h.1
  exact (h.2 x hx h0).2.2.1

omit [IsCMField E] in
theorem absNorm_ne_zero (w : HeightOneSpectrum (𝓞 E)) : (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := fun h0 =>
  w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)

theorem SystemOf.weights {ι : Qbar l ≃+* ℂ} {T : Type} {inc : T → (E →+* Qbar l)} (half : IsHalf inc) {s : T → ℤ} {Pl : Type}
    {lab : Pl → HeightOneSpectrum (𝓞 E)} {n : ℕ} {mu : T → ℕ → ℕ} {θ : Pl → ℕ → Qbar l} {π : Submodule ℂ (UA E n → ℂ)}
    (h : SystemOf ι inc s lab n mu θ π) :
    ∃ lam : (E →+* ℂ) → DomWeight n, (∀ φ, HasWeightAt π φ (lam φ)) ∧
      (∀ τ a, (lam (ι.toRingHom.comp (inc τ))).w a = (mu τ a : ℤ) + s τ) ∧
      (∀ τ, lam (ι.toRingHom.comp (cj (inc τ))) = (lam (ι.toRingHom.comp (inc τ))).dual) ∧
      ∀ φ, ∃ τ, φ = ι.toRingHom.comp (inc τ) ∨ φ = ι.toRingHom.comp (cj (inc τ)) := by
  choose lam h1 h2 h3 using h.2.1
  obtain ⟨F, hF, hF'⟩ := exists_of_half half lam fun τ => (lam τ).dual
  have e : ∀ τ : E →+* Qbar l, ι.symm.toRingHom.comp (ι.toRingHom.comp τ) = τ := fun τ => by ext x; simp
  have hφ : ∀ φ : E →+* ℂ, ∃ τ, φ = ι.toRingHom.comp (inc τ) ∨ φ = ι.toRingHom.comp (cj (inc τ)) := fun φ => by
    obtain ⟨τ, a⟩ := half.2.2 (ι.symm.toRingHom.comp φ)
    refine ⟨τ, a.imp (fun a => ?_) fun a => ?_⟩ <;> · rw [← a]; ext x; simp
  refine ⟨fun φ => F (ι.symm.toRingHom.comp φ), fun φ => ?_, fun τ a => ?_, fun τ => ?_, hφ⟩
  · obtain ⟨τ, rfl | rfl⟩ := hφ φ
    · simpa only [e, hF] using h2 τ
    · simpa only [e, hF'] using h3 τ
  · simp only [e, hF, h1]
  · simp only [e, hF, hF']

theorem SystemOf.reads {ι : Qbar l ≃+* ℂ} {T : Type} {inc : T → (E →+* Qbar l)} {s : T → ℤ} {Pl : Type} (Fn : FrobNorm E Ω l Pl)
    (hlab : ∀ Q, IsSplitAt (Fn.lab Q) ∧ ((l : ℕ) : 𝓞 E) ∉ (Fn.lab Q).asIdeal)
    {n : ℕ} {mu : T → ℕ → ℕ} {θ : Pl → ℕ → Qbar l} {π : Submodule ℂ (UA E n → ℂ)} (h : SystemOf ι inc s Fn.lab n mu θ π)
    {cp cp' : G E Ω → Polynomial (Qbar l)} (hcp : FrobSat ι π Fn.sgn cp)
    (hcp' : ∀ g, cp' g = (cp g).scaleRoots ((Fn.tw g : (Qbar l)ˣ) : Qbar l)) : Fn.Reads n θ cp' := by
  intro Q B g hB hg
  obtain ⟨hu, σ, S, h1, h2, h3⟩ := h.2.2.2 Q
  rw [hcp', hcp _ (hlab Q).1 (hlab Q).2 hu σ S h1 h2 B g hB hg]
  exact reverse_scale_eq_hecke ι (absNorm_ne_zero _) S (card_of_hasSat h2) _ h3 _

variable (Ω) in

theorem galSide_of_systems (p1 : GlobalTheory.Published.ClozelCohomological) (p2 : GlobalTheory.Published.CohomologicalCsdTempered)
    (p3 : GlobalTheory.Published.HeckeLAdicCharacter) (p4 : GlobalTheory.Published.ChebotarevDegreeOne) (p5 : GlobalTheory.Published.DiscreteSpectrumGL)
    (p6 : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (p7 : GlobalTheory.Published.BaseChangeDefiniteUnitary)
    (p8 : GlobalTheory.Published.BhattScholzeCrystallineLattices) (p9 : GlobalTheory.Published.HeckeLAdicCharacterAbove) (p10 : GlobalTheory.Published.LocalLanglandsGL)
    (hE : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal)
    (ι : Qbar l ≃+* ℂ) {T : Type} [DecidableEq T] {inc : T → (E →+* Qbar l)} (half : IsHalf inc) (s : T → ℤ)
    {P : Par} {W : Wts T} (hP : P.Hyp) (hL : P.Large) (hW : W.Ok P) (F : Frame l T P.Nr) (Bk : (F.I → Qbar l) → Prop)
    {Pl : Type} (pt : Pl → Fin P.Nr → F.I) (lab : Pl → HeightOneSpectrum (𝓞 E))
    (cofin : {v : HeightOneSpectrum (𝓞 E) | (Ideal.absNorm v.asIdeal).Prime ∧ v ∉ Set.range lab}.Finite)
    (hlab : ∀ Q, IsSplitAt (lab Q) ∧ ((l : ℕ) : 𝓞 E) ∉ (lab Q).asIdeal)
    (haut : ∀ mu θ, (∀ τ, Antitone (res P.Nr (mu τ))) → F.IsEig mu θ → ∃ π, SystemOf ι inc s lab P.Nr mu (sysOf P.Nr pt θ) π)
    (hblk : ∀ θ, Bk θ → ∀ Q, ∃ ν : Qbar l, ‖ι ν‖ ^ 2 = (Ideal.absNorm (lab Q).asIdeal : ℝ) ^ (P.Nr - P.t) ∧
      blockPoly ν (Ideal.absNorm (lab Q).asIdeal) P.t ∣ heckePolyOf P.Nr (Ideal.absNorm (lab Q).asIdeal) (sysOf P.Nr pt θ Q)) :
    GalSide Ω inc P W F Bk := by
  have hN := hP.Nr_eq
  have ht := hP.t_ge
  have hm := hP.m_pos
  have hk := hP.m_le
  obtain ⟨c, hc, hc'⟩ := exists_of_half half (fun τ => (h0 P : ℤ) - P.Nr + 1 + s τ) fun τ => -s τ
  obtain ⟨tw, htw, hcr⟩ := exists_crys_char Ω p3 p9 ι c ((h0 P : ℤ) - P.Nr + 1) fun i => by
    obtain ⟨τ, rfl | rfl⟩ := half.2.2 i
    · rw [hc, hc']; ring
    · rw [cj_cj, hc, hc']; ring
  let Fn : FrobNorm E Ω l Pl := ⟨lab, -1, tw, htw, cofin⟩
  have main := GlobalTheory.GalAut.galoisRep_definiteUnitary p7 p5 p6 p1 p2 p3 p9 p4 p8 p10 E Ω hE P.Nr (by omega)
  refine ⟨Pl, pt, Fn, cj, Or.inr rfl, fun mu θ ha hθ => ?_, fun θ hθ hB => ?_⟩
  · obtain ⟨π, hπ⟩ := haut mu θ ha hθ
    obtain ⟨lam, hl, hl1, hl2, -⟩ := hπ.weights half
    obtain ⟨⟨r, hr, hf⟩, -⟩ := main π hπ.1 lam hl l ι hπ.2.2.1
    refine ⟨GlobalTheory.TwistAbove.twGL tw r,
      fun τ a => ((Fin.rev a : ℕ) : ℤ) - (lam (ι.toRingHom.comp τ)).w (Fin.rev a) + c τ, fun τ a => ⟨?_, ?_⟩, ?_,
      SystemOf.reads Fn hlab hπ hf fun g => charpoly_smul _ (Units.ne_zero _)⟩
    · have := a.2
      simp only [hl2, hc', DomWeight.dual, Fin.rev_rev, hl1, Formalism.CohomologicalDescent.UnitNormBounds.UN]
      rw [Fin.val_rev]
      omega
    · have := a.2
      simp only [cj_cj, hc, hl1, Formalism.CohomologicalDescent.UnitNormBounds.UN, Fin.val_rev]
      omega
    · convert crysWith_twist (r' := GlobalTheory.TwistAbove.twGL tw r) (fun _ => rfl) hr htw hcr using 2 with τ
      rw [jumpsOf, Multiset.map_map]
      conv_rhs => rw [← Multiset.map_univ_val_equiv Fin.revPerm, Multiset.map_map]
      rfl
  · have ha : ∀ τ, Antitone (res P.Nr (W.lam τ)) := fun τ a b h => hW.anti τ a b h b.2
    obtain ⟨π, hπ⟩ := haut W.lam θ ha hθ
    obtain ⟨lam, hl, hl1, hl2, hl3⟩ := hπ.weights half
    have r1 := fun τ => isRunAt_block hP hL hW τ _ _ (hl1 τ)
    have r2 := fun τ => isRunAt_dual (by omega) (r1 τ).1
    obtain ⟨-, v, hv, hd, -⟩ := (p4.dense (Ω := Ω) cofin).nonempty
    obtain ⟨Q, -⟩ : v ∈ Set.range lab := by
      by_contra h
      exact hv ⟨((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 v).2 hd, h⟩
    have hstr : HasString l π P.t := by
      obtain ⟨hu, σ, S, h1, h2, h3⟩ := hπ.2.2.2 Q
      obtain ⟨ν, hν, hdv⟩ := hblk θ hB Q
      obtain ⟨u, hu1, hu2⟩ := string_of_dvd ι (absNorm_ne_zero _) (by omega) S (card_of_hasSat h2) _ h3 ν hν hdv
      exact ⟨lab Q, (hlab Q).1, (hlab Q).2, hu, σ, S, u, h1, h2, hu1, hu2⟩
    obtain ⟨a, ρ, χ, bot, h1, h2, h3, h4, h5⟩ := (main π hπ.1 lam hl l ι hπ.2.2.1).2 P.t (by omega) (fun φ => by
      obtain ⟨τ, rfl | rfl⟩ := hl3 φ
      · exact ⟨_, (r1 τ).1⟩
      · exact ⟨_, hl2 τ ▸ (r2 τ).1⟩) hstr
    refine ⟨a, GlobalTheory.TwistAbove.twGL tw ρ, fun j => χ j * tw, fun τ => bot τ + c τ, h1,
      continuous_twist (fun _ => rfl) h2 htw, fun j => ?_, fun τ => ⟨?_, ?_⟩, SystemOf.reads Fn hlab hπ h5 fun g => ?_⟩
    · convert crysWith_twist (r' := rk1 (χ j * tw)) (fun g => ?_) (h3 j) htw hcr using 2 with τ
      · rw [Multiset.map_singleton, add_right_comm]
      · ext x y
        simp [rk1, Matrix.diagonal_apply, mul_comm]
    · have := hW.what₂ τ
      beta_reduce
      rw [h4 _ _ (hl2 τ ▸ (r2 τ).1), hl2, (r2 τ).2, (r1 τ).2, hc']
      omega
    · beta_reduce
      rw [cj_cj, h4 _ _ (r1 τ).1, (r1 τ).2, hc]
      omega
    · have e := scaleRoots_prod (Finset.univ.val.map fun j => ((χ j g : (Qbar l)ˣ) : Qbar l)) ((tw g : (Qbar l)ˣ) : Qbar l)
      rw [Multiset.map_map, Multiset.map_map] at e
      rw [mul_scaleRoots_of_noZeroDivisors, ← charpoly_smul _ (Units.ne_zero _)]
      exact congrArg₂ (· * ·) rfl e.symm

end Side

section Point

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame GlobalTheory.FrameAut
open Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.L2.Col

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem block_dvd {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} {F : Frame l ι N} {lam : ι → ℕ → ℕ}
    {K : Type} [Field K] [NumberField K] [StarRing K] {G0 : Type} [Group G0] [Fintype G0] {Pl0 : Type} {B : BlockDat K G0 Pl0}
    {w : HeightOneSpectrum (𝓞 K)} {R : Reads F lam B w} {θ : F.I → PadicAlgCl l} (h : R.HasBlock θ) (hn : B.n = N)
    {Pl : Type} (pt : Pl → Fin N → F.I) (P : Pl) (Q : B.Pl) (hQ : ∀ k, R.ix (pt P k) = (Q, (k : ℕ) + 1)) {ν : B.Pl → K} (hν : ν ∈ B.bl) :
    blockPoly (R.e0 (ν Q)) (B.q Q) B.t ∣ heckePolyOf N (B.q Q) (sysOf N pt θ P) := by
  subst hn
  have h1 := Reads.HasBlock.dvd h pt P Q hQ
  exact dvd_trans (List.dvd_prod (List.mem_map_of_mem (f := fun ν : B.Pl → K => blockPoly (R.e0 (ν Q)) (B.q Q) B.t) hν)) h1

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

theorem blk_numbers {j : Fin D.R.m} {P : Par} {W : Wts D.what₂.Tau} (hD : Dict L j P W) (hP : P.Hyp) (t : p.P.T) :
    (blk p j t).n = P.Nr ∧ (blk p j t).t = P.t ∧ ∃ ν, ν ∈ (blk p j t).bl := by
  obtain ⟨_, _, _, H⟩ := p.charW.base.fam.tie
  have h1 : (blk p j t).n = D.R.k + D.R.m - 1 + D.R.t := by
    show p.P.A3.A.r + p.P.A3.A.t = _
    rw [H.ranks.2.1, H.ranks.2.2]
    rfl
  have := hP.Nr_eq
  have := hP.m_pos
  have := hD.k
  have := hD.m
  have := hD.t
  exact ⟨by omega, H.ranks.2.2.trans hD.t.symm, List.exists_mem_of_ne_nil _ (List.cons_ne_nil _ _)⟩

set_option maxHeartbeats 1600000 in

theorem galAt_of_autAt (p1 : GlobalTheory.Published.ClozelCohomological) (p2 : GlobalTheory.Published.CohomologicalCsdTempered)
    (p3 : GlobalTheory.Published.HeckeLAdicCharacter) (p4 : GlobalTheory.Published.ChebotarevDegreeOne) (p5 : GlobalTheory.Published.DiscreteSpectrumGL)
    (p6 : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (p7 : GlobalTheory.Published.BaseChangeDefiniteUnitary)
    (p8 : GlobalTheory.Published.BhattScholzeCrystallineLattices) (p9 : GlobalTheory.Published.HeckeLAdicCharacterAbove) (p10 : GlobalTheory.Published.LocalLanglandsGL)
    {j : Fin D.R.m} {P : Par} {W : Wts D.what₂.Tau} (hD : Dict L j P W) (hN : NumOk P W) {w : HeightOneSpectrum (𝓞 D.what₂.LL)}
    (h : AutAt p j P W w) : GalAt p j P W w := by
  classical
  intro _ F R inc _ T
  obtain ⟨⟨hpl, hcof, hbl⟩, haut⟩ := h
  obtain ⟨hn, ht, ν, hν⟩ := blk_numbers p hD hN.1 (p.R.mu w)
  let Pl := {Q : (blk p j (p.R.mu w)).Pl // ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal}
  have hpt : ∀ (Q : Pl) (k : Fin P.Nr), ∃ i, R.ix i = (Q.1, (k : ℕ) + 1) := fun Q k =>
    (T.ix_range (Q.1, (k : ℕ) + 1)).2 ⟨Nat.le_add_left _ _, k.2, Q.2⟩
  choose pt hpt using hpt
  refine galSide_of_systems _ p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 (GlobalTheory.DefiniteBC.host_unramified D.host) T.io T.half T.sh hN.1 hN.2.1
    hN.2.2.1 F _ pt (fun Q => labOf p j (p.R.mu w) Q.1) (hcof.subset fun v hv => ⟨hv.1, fun ⟨Q, h1, h2⟩ => hv.2 ⟨⟨Q, h1⟩, h2⟩⟩)
    (fun Q => ⟨(hpl Q.1).1, fun h => Q.2 ((hpl Q.1).2.2.2.1 h)⟩) (fun mu θ ha hθ => ?_) fun θ hθ Q => ?_
  · obtain ⟨π, h1, h2, h3, h4⟩ := haut F R inc T mu θ ha hθ
    refine ⟨π, h1, h2, h3, fun Q => ?_⟩
    obtain ⟨hu, σ, S, a, b, c⟩ := h4 Q.1
    refine ⟨hu, σ, S, a, b, fun k hk => ?_⟩
    rcases k with _ | k
    · rw [sysOf_zero, map_one, GlobalTheory.LFun.satEig]
      simp [Multiset.esymm]
    · have e := c (pt Q ⟨k, hk⟩) (by rw [hpt])
      rw [hpt] at e
      exact (congrArg T.io (sysOf_succ P.Nr pt θ Q ⟨k, hk⟩)).trans e
  · refine ⟨R.e0 (ν Q.1), ?_, ?_⟩
    · rw [T.liftFrame_embedding_base, hbl ν hν, (hpl Q.1).2.2.1, hn, ht]
    · rw [(hpl Q.1).2.2.1, ← ht]
      exact block_dvd hθ hn pt Q Q.1 (hpt Q) hν

end Point

end GlobalTheory.FrameGal

open Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie in

theorem GlobalTheory.FrameGal.galSt : GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.CohomologicalCsdTempered → GlobalTheory.Published.HeckeLAdicCharacter →
    GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.DiscreteSpectrumGL → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal →
    GlobalTheory.Published.BaseChangeDefiniteUnitary → GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.HeckeLAdicCharacterAbove →
    GlobalTheory.Published.LocalLanglandsGL → SmallSt → GlobalTheory.ExpTie.GalSt := by
  intro p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 hS
  refine Closed.imp (GlobalTheory.T.small_estimate_implies_frame_automorphy hS) fun Fm _ _ H => ?_
  obtain ⟨a, ha⟩ := H
  exact ⟨a, fun x hx hle i p hp hm j P W hD hN w hw hR =>
    GlobalTheory.FrameGal.galAt_of_autAt p p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 hD hN (ha x hx hle i p hp hm j P W hD hN w hw hR)⟩

end
