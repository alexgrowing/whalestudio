import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

namespace Top

open MvPolynomial Finset

noncomputable section

def blockEmb (f N : ℕ) (σ : Fin f) : RootRing 1 N →ₐ[ℚ] RootRing f N :=
  rename (fun p : Fin 1 × Fin N => (σ, p.2))

theorem blockPermute_blockEmb (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) (σ : Fin f)
    (P : RootRing 1 N) :
    blockPermute f N w (blockEmb f N σ P) =
      blockEmb f N σ (blockPermute 1 N (fun _ => w σ) P) := by
  simp only [blockPermute, blockEmb, rename_rename]
  rfl

def HasDD (f N : ℕ) (H P : RootRing f N) : Prop :=
  antisymmetrize f N H = blockVandermonde f N * P

theorem vandermondeOf_X_ne_zero (f N : ℕ) (τ : Fin f) :
    vandermondeOf (fun i : Fin N => (X (τ, i) : RootRing f N)) ≠ 0 := by
  unfold vandermondeOf
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  have hij : i ≠ j := (ne_of_lt (Finset.mem_Ioi.mp hj))
  refine sub_ne_zero.mpr fun h => hij ?_
  have := X_injective (R := ℚ) h
  simpa using this

theorem blockVandermonde_ne_zero (f N : ℕ) : blockVandermonde f N ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun τ _ => vandermondeOf_X_ne_zero f N τ

theorem dividedDifference_eq_of_hasDD {f N : ℕ} {H P : RootRing f N} (h : HasDD f N H P) :
    dividedDifference f N H = algebraMap (RootRing f N) (FractionRing (RootRing f N)) P := by
  have hV : algebraMap (RootRing f N) (FractionRing (RootRing f N)) (blockVandermonde f N) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (blockVandermonde_ne_zero f N)
  rw [dividedDifference, h, map_mul, mul_div_cancel_left₀ _ hV]

theorem hasDD_of_dividedDifference_eq {f N : ℕ} {H P : RootRing f N}
    (h : dividedDifference f N H = algebraMap (RootRing f N) (FractionRing (RootRing f N)) P) :
    HasDD f N H P := by
  have hV : algebraMap (RootRing f N) (FractionRing (RootRing f N)) (blockVandermonde f N) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (blockVandermonde_ne_zero f N)
  rw [dividedDifference, div_eq_iff hV, ← map_mul] at h
  exact IsFractionRing.injective _ _ (by rw [h, mul_comm])

theorem antisymmetrize_add (f N : ℕ) (H H' : RootRing f N) :
    antisymmetrize f N (H + H') = antisymmetrize f N H + antisymmetrize f N H' := by
  simp [antisymmetrize, map_add, smul_add, Finset.sum_add_distrib]

theorem antisymmetrize_smul (f N : ℕ) (b : ℚ) (H : RootRing f N) :
    antisymmetrize f N (b • H) = b • antisymmetrize f N H := by
  simp [antisymmetrize, map_smul, Finset.smul_sum, smul_comm b]

theorem antisymmetrize_sum {ι : Type*} (s : Finset ι) (f N : ℕ) (H : ι → RootRing f N) :
    antisymmetrize f N (∑ i ∈ s, H i) = ∑ i ∈ s, antisymmetrize f N (H i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [antisymmetrize]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, antisymmetrize_add, ih]

theorem hasDD_add {f N : ℕ} {H H' P P' : RootRing f N} (h : HasDD f N H P) (h' : HasDD f N H' P') :
    HasDD f N (H + H') (P + P') := by
  rw [HasDD, antisymmetrize_add, h, h', mul_add]

theorem hasDD_smul {f N : ℕ} {H P : RootRing f N} (b : ℚ) (h : HasDD f N H P) :
    HasDD f N (b • H) (b • P) := by
  rw [HasDD, antisymmetrize_smul, h, mul_smul_comm]

theorem hasDD_sum {ι : Type*} (s : Finset ι) {f N : ℕ} {H P : ι → RootRing f N}
    (h : ∀ i ∈ s, HasDD f N (H i) (P i)) : HasDD f N (∑ i ∈ s, H i) (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [HasDD, antisymmetrize]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact hasDD_add (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem blockEmb_blockVandermonde (f N : ℕ) (σ : Fin f) :
    blockEmb f N σ (blockVandermonde 1 N) =
      vandermondeOf (fun i : Fin N => (X (σ, i) : RootRing f N)) := by
  simp [blockVandermonde, vandermondeOf, blockEmb, map_prod, map_sub, rename_X]

theorem blockVandermonde_eq_prod (f N : ℕ) :
    blockVandermonde f N = ∏ σ : Fin f, blockEmb f N σ (blockVandermonde 1 N) := by
  simp only [blockEmb_blockVandermonde]
  rfl

theorem antisymmetrize_one_eq (N : ℕ) (P : RootRing 1 N) :
    antisymmetrize 1 N P = ∑ v : Equiv.Perm (Fin N),
      (((Equiv.Perm.sign v : ℤˣ) : ℤ) : ℚ) • blockPermute 1 N (fun _ => v) P := by
  unfold antisymmetrize
  rw [← (Equiv.funUnique (Fin 1) (Equiv.Perm (Fin N))).symm.sum_comp]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [blockSign, Equiv.funUnique]
  rfl

theorem antisymmetrize_prod (f N : ℕ) (P : Fin f → RootRing 1 N) :
    antisymmetrize f N (∏ σ, blockEmb f N σ (P σ)) =
      ∏ σ, blockEmb f N σ (antisymmetrize 1 N (P σ)) := by
  simp_rw [antisymmetrize_one_eq, map_sum, Finset.prod_univ_sum, antisymmetrize, map_prod,
    blockPermute_blockEmb, map_smul]
  refine Finset.sum_congr (by simp) fun w _ => ?_
  simp only [blockSign, smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]

theorem hasDD_prod (f N : ℕ) (P Q : Fin f → RootRing 1 N) (h : ∀ σ, HasDD 1 N (P σ) (Q σ)) :
    HasDD f N (∏ σ, blockEmb f N σ (P σ)) (∏ σ, blockEmb f N σ (Q σ)) := by
  rw [HasDD, antisymmetrize_prod, blockVandermonde_eq_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun σ _ => ?_
  rw [h σ, map_mul]

theorem yRoot_eq_blockEmb (f r a : ℕ) (c : SmallBlock) (σ : Fin f) (i : Fin r) :
    yRoot f r a c σ i = blockEmb f (r + a) σ (yRoot 1 r a c 0 i) := by
  cases c <;> simp [yRoot, yIndex, blockEmb]

theorem zRoot_eq_blockEmb (f r a : ℕ) (c : SmallBlock) (σ : Fin f) (i : Fin a) :
    zRoot f r a c σ i = blockEmb f (r + a) σ (zRoot 1 r a c 0 i) := by
  cases c <;> simp [zRoot, zIndex, blockEmb]

theorem vandermondeOf_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ}
    (v : Fin m → R) : φ (vandermondeOf v) = vandermondeOf (fun i => φ (v i)) := by
  simp [vandermondeOf, map_prod, map_sub]

def fib1 (r a : ℕ) (c : SmallBlock) : RootRing 1 (r + a) :=
  vandermondeOf (yRoot 1 r a c 0) * vandermondeOf (zRoot 1 r a c 0)

theorem fibreClass_eq_prod (f r a : ℕ) (c : SmallBlock) :
    fibreClass f r a c = ∏ σ : Fin f, blockEmb f (r + a) σ (fib1 r a c) := by
  refine Finset.prod_congr rfl fun σ _ => ?_
  have h := vandermondeOf_map (blockEmb f (r + a) σ).toRingHom (yRoot 1 r a c 0)
  have h' := vandermondeOf_map (blockEmb f (r + a) σ).toRingHom (zRoot 1 r a c 0)
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h h'
  rw [fib1, map_mul, h, h']
  simp only [← yRoot_eq_blockEmb, ← zRoot_eq_blockEmb]

def yEval (r a : ℕ) (c : SmallBlock) : MvPolynomial (Fin r) ℚ →ₐ[ℚ] RootRing 1 (r + a) :=
  aeval (yRoot 1 r a c 0)

theorem blockEmb_yEval_psum (f r a : ℕ) (c : SmallBlock) (σ : Fin f) (k : ℕ) :
    blockEmb f (r + a) σ (yEval r a c (psum (Fin r) ℚ k)) = smallPowerSum f r a c k σ := by
  simp only [yEval, psum, map_sum, map_pow, aeval_X, smallPowerSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [yRoot_eq_blockEmb f r a c σ i]

theorem smallBlockMu_eq_sum (f r a : ℕ) (c : SmallBlock) :
    smallBlockMu f r a c = ∑ σ : Fin f, blockEmb f (r + a) σ (yEval r a c (psum (Fin r) ℚ 1)) := by
  simp only [yEval, psum, map_sum, pow_one, aeval_X, smallBlockMu]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun i _ => ?_
  rw [yRoot_eq_blockEmb f r a c σ i]

theorem completeSymmetric_zero (σ : Type*) [Fintype σ] [DecidableEq σ] :
    completeSymmetric σ 0 = 1 := by
  simp [completeSymmetric, hsymm_zero]

theorem completeSymmetric_neg (σ : Type*) [Fintype σ] [DecidableEq σ] {d : ℤ} (hd : d < 0) :
    completeSymmetric σ d = 0 := by
  simp [completeSymmetric, not_le.mpr hd]

theorem schur_zero (σ : Type*) [Fintype σ] [DecidableEq σ] (m : ℕ) :
    schur σ (0 : Fin m → ℕ) = 1 := by
  unfold schur
  rw [Matrix.det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [completeSymmetric_zero]
  · intro i j hij
    simp only [Matrix.of_apply, Pi.zero_apply, Nat.cast_zero, zero_sub]
    apply completeSymmetric_neg
    have : (j : ℕ) < i := hij
    omega

theorem constantCoeff_completeSymmetric (σ : Type*) [Fintype σ] [DecidableEq σ] (d : ℤ) :
    constantCoeff (completeSymmetric σ d) = if d = 0 then 1 else 0 := by
  unfold completeSymmetric
  split_ifs with h1 h2 h2
  · subst h2; simp [hsymm_zero]
  · have hpos : 0 < d.toNat := by omega
    obtain ⟨n, hn⟩ : ∃ n, d.toNat = n + 1 := ⟨d.toNat - 1, by omega⟩
    rw [hn]
    simp only [hsymm, map_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [map_multiset_prod, Multiset.map_map]
    apply Multiset.prod_eq_zero
    obtain ⟨x, hx⟩ : ∃ x, x ∈ s.1 :=
      Multiset.card_pos_iff_exists_mem.mp (by rw [s.2]; omega)
    exact Multiset.mem_map.mpr ⟨x, hx, by simp⟩
  · omega
  · simp

theorem constantCoeff_schur (σ : Type*) [Fintype σ] [DecidableEq σ] {m : ℕ} (ν : Fin m → ℕ)
    (hν : Antitone ν) : constantCoeff (schur σ ν) = if ν = 0 then 1 else 0 := by
  split_ifs with h
  · subst h; rw [schur_zero, map_one]
  · have hm : 0 < m := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; exact absurd (funext fun i => i.elim0) h
      · exact hm
    have h0 : 0 < ν ⟨0, hm⟩ := by
      by_contra h0
      refine h (funext fun i => ?_)
      have := hν (show (⟨0, hm⟩ : Fin m) ≤ i from Nat.zero_le _)
      simp only [Pi.zero_apply]
      omega
    unfold schur
    rw [RingHom.map_det]
    apply Matrix.det_eq_zero_of_row_eq_zero ⟨0, hm⟩
    intro j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      constantCoeff_completeSymmetric]
    rw [if_neg]
    simp only [Nat.cast_zero, sub_zero]
    omega

theorem constantCoeff_aeval_of_zero {ι κ : Type*} (g : ι → MvPolynomial κ ℚ)
    (hg : ∀ i, constantCoeff (g i) = 0) (p : MvPolynomial ι ℚ) :
    constantCoeff (aeval g p) = constantCoeff p := by
  have : (constantCoeff.comp (aeval g).toRingHom : MvPolynomial ι ℚ →+* ℚ) = constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro x; simp [constantCoeff_C]
    · intro i; simp [hg i]
  exact congrArg (fun φ : MvPolynomial ι ℚ →+* ℚ => φ p) this

def xSign (r a : ℕ) (c : SmallBlock) : MvPolynomial (Fin (r + a)) ℚ →ₐ[ℚ] RootRing 1 (r + a) :=
  aeval (fun i : Fin (r + a) => C c.sign * X ((0 : Fin 1), i))

def pushOut (r a : ℕ) (c : SmallBlock) (κ : ℚ) (lam : Fin r → ℕ) : RootRing 1 (r + a) :=
  if ∀ i, a ≤ lam i then C κ * xSign r a c (schur (Fin (r + a)) (fun i => lam i - a)) else 0

theorem constantCoeff_pushOut (r a : ℕ) (c : SmallBlock) (κ : ℚ) (lam : Fin r → ℕ)
    (hl : Antitone lam) :
    constantCoeff (pushOut r a c κ lam) = if lam = rectangle r a then κ else 0 := by
  unfold pushOut
  split_ifs with h1 h2 h2
  · subst h2
    have : (fun i : Fin r => rectangle r a i - a) = 0 := funext fun i => by simp [rectangle]
    rw [map_mul, constantCoeff_C, xSign, constantCoeff_aeval_of_zero _ (fun i => by simp), this,
      schur_zero, map_one, mul_one]
  · rw [map_mul, constantCoeff_C, xSign, constantCoeff_aeval_of_zero _ (fun i => by simp),
      constantCoeff_schur _ _ (fun i j hij => Nat.sub_le_sub_right (hl hij) a), if_neg, mul_zero]
    intro h0
    exact h2 (funext fun i => by
      have := congrFun h0 i
      simp only [Pi.zero_apply] at this
      have := h1 i
      simp [rectangle]; omega)
  · exact absurd (fun i => by rw [h2]; simp [rectangle]) h1
  · simp

theorem hasDD_schur (hB : LemmaB.Statement) (r a : ℕ) (c : SmallBlock) :
    ∃ κ : ℚ, (κ = (r.factorial : ℚ) * a.factorial ∨ κ = -((r.factorial : ℚ) * a.factorial)) ∧
      ∀ lam : Fin r → ℕ, Antitone lam →
        HasDD 1 (r + a) (yEval r a c (schur (Fin r) lam) * fib1 r a c) (pushOut r a c κ lam) := by
  obtain ⟨κ, hκ, h⟩ := hB r a c
  refine ⟨κ, hκ, fun lam hl => hasDD_of_dividedDifference_eq ?_⟩
  have := h lam hl
  rw [yEval, fib1, ← mul_assoc, this, pushOut, xSign]
  split_ifs <;> simp

theorem hasDD_schur_sum (r a : ℕ) (c : SmallBlock) (κ : ℚ)
    (hκ : ∀ lam : Fin r → ℕ, Antitone lam →
        HasDD 1 (r + a) (yEval r a c (schur (Fin r) lam) * fib1 r a c) (pushOut r a c κ lam))
    (s : Finset (Fin r → ℕ)) (hs : ∀ lam ∈ s, Antitone lam) (b : (Fin r → ℕ) → ℚ) :
    HasDD 1 (r + a) (yEval r a c (∑ lam ∈ s, C (b lam) * schur (Fin r) lam) * fib1 r a c)
      (∑ lam ∈ s, b lam • pushOut r a c κ lam) := by
  rw [map_sum, Finset.sum_mul]
  refine hasDD_sum s fun lam hlam => ?_
  have := hasDD_smul (b lam) (hκ lam (hs lam hlam))
  convert this using 1
  rw [map_mul, yEval, aeval_C, Algebra.smul_def, mul_assoc]

theorem antitone_of_mem_partitionsOf {m n : ℕ} {lam : Fin m → ℕ} (h : lam ∈ partitionsOf m n) :
    Antitone lam := by
  intro i j hij
  exact (Finset.mem_filter.mp h).2 i j hij

theorem sum_of_mem_partitionsOf {m n : ℕ} {lam : Fin m → ℕ} (h : lam ∈ partitionsOf m n) :
    ∑ i, lam i = n := by
  have := (Finset.mem_filter.mp h).1
  rw [Finset.Nat.mem_antidiagonalTuple] at this
  exact this

theorem constantCoeff_pushOut_sum (r a : ℕ) (c : SmallBlock) (κ : ℚ) (s : Finset (Fin r → ℕ))
    (hs : ∀ lam ∈ s, Antitone lam) (b : (Fin r → ℕ) → ℚ) :
    constantCoeff (∑ lam ∈ s, b lam • pushOut r a c κ lam) =
      if rectangle r a ∈ s then b (rectangle r a) * κ else 0 := by
  rw [map_sum]
  have : ∀ lam ∈ s, constantCoeff (b lam • pushOut r a c κ lam) =
      if lam = rectangle r a then b lam * κ else 0 := by
    intro lam hlam
    rw [smul_eq_C_mul, map_mul, constantCoeff_C, constantCoeff_pushOut r a c κ lam (hs lam hlam)]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']

theorem expand_blocks (f r a : ℕ) (c : SmallBlock) (g : Fin f → MvPolynomial (Fin r) ℚ) (e : ℕ) :
    (∏ σ, blockEmb f (r + a) σ (yEval r a c (g σ))) * smallBlockMu f r a c ^ e *
        fibreClass f r a c =
      ∑ m ∈ Finset.piAntidiag (Finset.univ : Finset (Fin f)) e,
        (Nat.multinomial Finset.univ m : ℚ) •
          ∏ σ, blockEmb f (r + a) σ
            (yEval r a c (g σ * psum (Fin r) ℚ 1 ^ m σ) * fib1 r a c) := by
  rw [smallBlockMu_eq_sum, Finset.sum_pow_eq_sum_piAntidiag, fibreClass_eq_prod, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  simp only [map_mul, map_pow, Finset.prod_mul_distrib]
  ring

def extraFactor (r q : ℕ) : MvPolynomial (Fin r) ℚ := if q = 0 then 1 else psum (Fin r) ℚ q

def blockCoeff {r : ℕ} (q m : ℕ) (lam : Fin r → ℕ) : ℚ :=
  if q = 0 then (if m = 0 then 1 else symmetricGroupCharacter lam (List.replicate m 1))
  else symmetricGroupCharacter lam (q :: List.replicate m 1)

theorem partitionsOf_zero (r : ℕ) : partitionsOf r 0 = {0} := by
  ext lam
  simp only [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple,
    Finset.mem_singleton]
  constructor
  · rintro ⟨h, -⟩
    funext i
    have := Finset.sum_eq_zero_iff.mp h i (Finset.mem_univ i)
    simpa using this
  · rintro rfl
    simp

theorem extraFactor_expand (hF : FrobeniusCharacterFormula.Statement) (r q m : ℕ) :
    extraFactor r q * psum (Fin r) ℚ 1 ^ m =
      ∑ lam ∈ partitionsOf r (q + m), C (blockCoeff q m lam) * schur (Fin r) lam := by
  unfold extraFactor blockCoeff
  by_cases hq : q = 0
  · subst hq
    simp only [if_true, one_mul, zero_add]
    by_cases hm : m = 0
    · subst hm
      simp [partitionsOf_zero, schur_zero]
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have := hF r 1 m' le_rfl
      rw [pow_succ', this, add_comm 1 m']
      refine Finset.sum_congr rfl fun lam _ => ?_
      rw [if_neg hm, List.replicate_succ]
  · simp only [if_neg hq]
    exact hF r q m (Nat.one_le_iff_ne_zero.mpr hq)

def blockOut (r a : ℕ) (c : SmallBlock) (κ : ℚ) (q m : ℕ) : RootRing 1 (r + a) :=
  ∑ lam ∈ partitionsOf r (q + m), blockCoeff q m lam • pushOut r a c κ lam

theorem hasDD_block (hF : FrobeniusCharacterFormula.Statement) (r a : ℕ) (c : SmallBlock) (κ : ℚ)
    (hκ : ∀ lam : Fin r → ℕ, Antitone lam →
        HasDD 1 (r + a) (yEval r a c (schur (Fin r) lam) * fib1 r a c) (pushOut r a c κ lam))
    (q m : ℕ) :
    HasDD 1 (r + a) (yEval r a c (extraFactor r q * psum (Fin r) ℚ 1 ^ m) * fib1 r a c)
      (blockOut r a c κ q m) := by
  rw [extraFactor_expand hF]
  exact hasDD_schur_sum r a c κ hκ _ (fun lam h => antitone_of_mem_partitionsOf h) _

theorem rectangle_mem_partitionsOf (r a t : ℕ) :
    rectangle r a ∈ partitionsOf r t ↔ t = r * a := by
  simp only [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple, rectangle,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  constructor
  · rintro ⟨h, -⟩; exact h.symm
  · rintro rfl; exact ⟨rfl, fun _ _ _ => le_rfl⟩

theorem constantCoeff_blockOut (r a : ℕ) (c : SmallBlock) (κ : ℚ) (q m : ℕ) :
    constantCoeff (blockOut r a c κ q m) =
      if q + m = r * a then blockCoeff q m (rectangle r a) * κ else 0 := by
  rw [blockOut, constantCoeff_pushOut_sum r a c κ _ (fun lam h => antitone_of_mem_partitionsOf h)]
  by_cases h : q + m = r * a
  · rw [if_pos ((rectangle_mem_partitionsOf r a (q + m)).mpr h), if_pos h]
  · rw [if_neg (fun h' => h ((rectangle_mem_partitionsOf r a (q + m)).mp h')), if_neg h]

theorem blockOut_eq_zero_of_lt (r a : ℕ) (c : SmallBlock) (κ : ℚ) (q m : ℕ)
    (h : q + m < r * a) : blockOut r a c κ q m = 0 := by
  refine Finset.sum_eq_zero fun lam hlam => ?_
  have hs := sum_of_mem_partitionsOf hlam
  rw [pushOut, if_neg, smul_zero]
  intro hall
  have : ∑ i : Fin r, a ≤ ∑ i, lam i := Finset.sum_le_sum fun i _ => hall i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  omega

end

end Top

end RestTerms

end GroundTheory.Heights₂.Heights
