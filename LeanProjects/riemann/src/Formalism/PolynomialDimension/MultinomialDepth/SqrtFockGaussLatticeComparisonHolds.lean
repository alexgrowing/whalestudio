import Formalism.PolynomialDimension.StatementHar
import Formalism.PolynomialDimension.MultinomialDepth.HarmonicDecompositionHolds
import Formalism.PolynomialDimension.MultinomialDepth.DiagLaplacianDivPowMemSqrtFockLattice

noncomputable section
open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.CountingSumsFrames
namespace Har4

theorem pairingPrime_holds : HPrime := by
  intro F _ k hk
  classical
  have hirr : Irreducible (hXY F k) := by
    have h := MvPolynomial.irreducible_sumSMulXSMulY (R := F) (n := Fin k)
      (Finsupp.equivFunOnFinite.symm (fun _ => (1:F))) ?_ ?_
    · convert h using 1
      simp [hXY, sumSMulXSMulY, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    · refine ⟨⟨0, by omega⟩, by simp, ⟨1, by omega⟩, by simp, ?_⟩
      simp [Fin.ext_iff]
    · intro r hr
      exact isUnit_of_dvd_one (by simpa using hr ⟨0, by omega⟩)
  exact hirr.prime

theorem coeff_mem_of_h_mul {K : Type} [Field K] {k : ℕ} (R : Subring K) (i0 : Fin k) (G : PolXY K k)
    (hG : ∀ m, coeff m (hXY K k * G) ∈ R) : ∀ m, coeff m G ∈ R := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨m0, hm0⟩ := hcon
  set S := G.support.filter (fun m => coeff m G ∉ R) with hS
  have hne : S.Nonempty := ⟨m0, by
    rw [hS, Finset.mem_filter, MvPolynomial.mem_support_iff]
    exact ⟨fun h => hm0 (h ▸ R.zero_mem), hm0⟩⟩
  obtain ⟨m, hmS, hmax⟩ := Finset.exists_max_image S (fun m => m (Sum.inl i0)) hne
  have hbig : ∀ m' : XY k →₀ ℕ, m (Sum.inl i0) < m' (Sum.inl i0) → coeff m' G ∈ R := by
    intro m' hlt
    by_contra hc
    have : m' ∈ S := by
      rw [hS, Finset.mem_filter, MvPolynomial.mem_support_iff]
      exact ⟨fun h => hc (h ▸ R.zero_mem), hc⟩
    have := hmax m' this
    omega
  have hmR : coeff m G ∉ R := (Finset.mem_filter.1 hmS).2
  apply hmR
  set M : XY k →₀ ℕ := Finsupp.single (Sum.inl i0) 1 + (Finsupp.single (Sum.inr i0) 1 + m) with hM
  have h1 := hG M
  rw [hXY, Finset.sum_mul, coeff_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0)] at h1
  have h2 : coeff M (X (Sum.inl i0) * X (Sum.inr i0) * G) = coeff m G := by
    rw [mul_assoc, hM, coeff_X_mul, coeff_X_mul]
  have h3 : ∑ i ∈ Finset.univ.erase i0, coeff M (X (Sum.inl i) * X (Sum.inr i) * G) ∈ R := by
    refine R.sum_mem fun i hi => ?_
    have hi' : i ≠ i0 := Finset.ne_of_mem_erase hi
    rw [mul_assoc, coeff_X_mul']
    split_ifs with ha
    · rw [coeff_X_mul']
      split_ifs with hb
      · apply hbig
        simp [hM, hi']
      · exact R.zero_mem
    · exact R.zero_mem
  rw [h2] at h1
  have := R.sub_mem h1 h3
  simpa using this

theorem glAct_X_inl {K : Type} [Field K] {k : ℕ} (g : GL (Fin k) K) (i : Fin k) :
    glAct g (X (Sum.inl i)) = ∑ j : Fin k, C ((g : Matrix (Fin k) (Fin k) K) i j) * X (Sum.inl j) := by
  simp only [glAct, aeval_X, Sum.elim_inl]

theorem glAct_X_inr {K : Type} [Field K] {k : ℕ} (g : GL (Fin k) K) (i : Fin k) :
    glAct g (X (Sum.inr i)) =
      ∑ j : Fin k, C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i) * X (Sum.inr j) := by
  simp only [glAct, aeval_X, Sum.elim_inr]

theorem glAct_hXY {K : Type} [Field K] {k : ℕ} (g : GL (Fin k) K) : glAct g (hXY K k) = hXY K k := by
  have hm : ∀ j l : Fin k, C (∑ i : Fin k, (g : Matrix (Fin k) (Fin k) K) i j * ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) l i) =
      (if l = j then 1 else 0 : PolXY K k) := by
    intro j l
    have e : (∑ i : Fin k, (g : Matrix (Fin k) (Fin k) K) i j * ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) l i) = (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) * (g : Matrix (Fin k) (Fin k) K)) l j := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs <;> simp
  unfold hXY
  simp only [map_sum, map_mul, glAct_X_inl, glAct_X_inr]
  calc ∑ i : Fin k, (∑ j : Fin k, C ((g : Matrix (Fin k) (Fin k) K) i j) * X (Sum.inl j)) *
        (∑ l : Fin k, C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) l i) * X (Sum.inr l))
      = ∑ i : Fin k, ∑ j : Fin k, ∑ l : Fin k, (C ((g : Matrix (Fin k) (Fin k) K) i j) * X (Sum.inl j)) *
          (C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) l i) * X (Sum.inr l)) := by
        simp only [Finset.sum_mul_sum]
    _ = ∑ j : Fin k, ∑ l : Fin k, ∑ i : Fin k, (C ((g : Matrix (Fin k) (Fin k) K) i j) * X (Sum.inl j)) *
          (C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) l i) * X (Sum.inr l)) :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ => Finset.sum_comm)
    _ = ∑ j : Fin k, ∑ l : Fin k, C (∑ i : Fin k, (g : Matrix (Fin k) (Fin k) K) i j * ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) l i) *
          (X (Sum.inl j) * X (Sum.inr l)) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        rw [map_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by rw [map_mul]; ring
    _ = ∑ i : Fin k, X (Sum.inl i) * X (Sum.inr i) := by
        simp only [hm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
          Finset.mem_univ, if_true]

theorem glAct_inv_glAct {K : Type} [Field K] {k : ℕ} (g : GL (Fin k) K) (f : PolXY K k) :
    glAct g⁻¹ (glAct g f) = f := by
  have key : (glAct g⁻¹).comp (glAct g) = AlgHom.id K (PolXY K k) := by
    apply MvPolynomial.algHom_ext
    rintro (i | i)
    · simp only [AlgHom.comp_apply, AlgHom.id_apply, glAct_X_inl, map_sum, map_mul,
        MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]
      have hm : ∀ l : Fin k, C (∑ j : Fin k, (g : Matrix (Fin k) (Fin k) K) i j *
          ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j l) = (if i = l then 1 else 0 : PolXY K k) := by
        intro l
        rw [← Matrix.mul_apply, Units.mul_inv, Matrix.one_apply]
        split_ifs <;> simp
      calc ∑ j : Fin k, C ((g : Matrix (Fin k) (Fin k) K) i j) *
            ∑ l : Fin k, C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j l) * X (Sum.inl l)
          = ∑ l : Fin k, C (∑ j : Fin k, (g : Matrix (Fin k) (Fin k) K) i j *
              ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j l) * X (Sum.inl l) := by
            simp only [map_sum, Finset.sum_mul, map_mul, mul_assoc, Finset.mul_sum]
            rw [Finset.sum_comm]
        _ = X (Sum.inl i) := by
          simp only [hm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    · simp only [AlgHom.comp_apply, AlgHom.id_apply, glAct_X_inr, map_sum, map_mul,
        MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, inv_inv]
      have hm : ∀ l : Fin k, C (∑ j : Fin k, ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i *
          (g : Matrix (Fin k) (Fin k) K) l j) = (if i = l then 1 else 0 : PolXY K k) := by
        intro l
        have e : (∑ j : Fin k, ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i *
            (g : Matrix (Fin k) (Fin k) K) l j) = ((g : Matrix (Fin k) (Fin k) K) *
            ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)) l i := by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
        rw [e, Units.mul_inv, Matrix.one_apply]
        by_cases h : i = l
        · subst h; simp
        · simp [h, Ne.symm h]
      calc ∑ j : Fin k, C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i) *
            ∑ l : Fin k, C ((g : Matrix (Fin k) (Fin k) K) l j) * X (Sum.inr l)
          = ∑ l : Fin k, C (∑ j : Fin k, ((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i *
              (g : Matrix (Fin k) (Fin k) K) l j) * X (Sum.inr l) := by
            simp only [map_sum, Finset.sum_mul, map_mul, mul_assoc, Finset.mul_sum]
            rw [Finset.sum_comm]
        _ = X (Sum.inr i) := by
          simp only [hm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h2 := congrArg (fun φ => φ f) key
  simpa using h2

theorem glAct_glAct_inv {K : Type} [Field K] {k : ℕ} (g : GL (Fin k) K) (f : PolXY K k) :
    glAct g (glAct g⁻¹ f) = f := by
  simpa using glAct_inv_glAct g⁻¹ f

theorem mem_latOf_iff {K : Type} [Field K] {k : ℕ} (g : GL (Fin k) K) (S : Set (PolXY K k)) (f : PolXY K k) :
    f ∈ latOf g S ↔ glAct g⁻¹ f ∈ S := by
  constructor
  · rintro ⟨h, hS, rfl⟩
    rwa [glAct_inv_glAct]
  · intro hf
    exact ⟨glAct g⁻¹ f, hf, glAct_glAct_inv g f⟩

def wXY (k : ℕ) : XY k → ℕ × ℕ := Sum.elim (fun _ => (1, 0)) (fun _ => (0, 1))

theorem weight_wXY {k : ℕ} (m : XY k →₀ ℕ) : Finsupp.weight (wXY k) m = (xDeg m, yDeg m) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type]
  ext <;> simp [wXY, xDeg, yDeg, Prod.fst_sum, Prod.snd_sum]

theorem mem_PolAB_iff {K : Type} [Field K] {k A B : ℕ} (f : PolXY K k) :
    f ∈ PolAB K k A B ↔ IsWeightedHomogeneous (wXY k) f (A, B) := by
  constructor
  · intro hf d hd
    have hf' : ∀ m ∈ f.support, xDeg m = A ∧ yDeg m = B := hf
    have h1 := hf' d (MvPolynomial.mem_support_iff.2 hd)
    rw [weight_wXY, h1.1, h1.2]
  · intro hf
    show ∀ m ∈ f.support, xDeg m = A ∧ yDeg m = B
    intro m hm
    have h1 := hf (MvPolynomial.mem_support_iff.1 hm)
    rw [weight_wXY] at h1
    exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩

theorem glAct_mem_PolAB {K : Type} [Field K] {k A B : ℕ} (g : GL (Fin k) K) (f : PolXY K k)
    (hf : f ∈ PolAB K k A B) : glAct g f ∈ PolAB K k A B := by
  rw [mem_PolAB_iff] at hf ⊢
  set σ : XY k → PolXY K k := Sum.elim
    (fun i : Fin k => ∑ j : Fin k, C ((g : Matrix (Fin k) (Fin k) K) i j) * X (Sum.inl j))
    (fun i : Fin k => ∑ j : Fin k, C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i) * X (Sum.inr j)) with hσdef
  have hgl : glAct g = aeval σ := rfl
  have hσ : ∀ v : XY k, IsWeightedHomogeneous (wXY k) (σ v) (wXY k v) := by
    rintro (i | i)
    · show IsWeightedHomogeneous (wXY k) (∑ j : Fin k, C ((g : Matrix (Fin k) (Fin k) K) i j) * X (Sum.inl j)) (wXY k (Sum.inl i))
      apply IsWeightedHomogeneous.sum
      intro j _
      have h := (isWeightedHomogeneous_C (wXY k) ((g : Matrix (Fin k) (Fin k) K) i j)).mul
        (isWeightedHomogeneous_X (R := K) (wXY k) (Sum.inl j))
      convert h using 1
      simp [wXY]
    · show IsWeightedHomogeneous (wXY k) (∑ j : Fin k, C (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i) * X (Sum.inr j)) (wXY k (Sum.inr i))
      apply IsWeightedHomogeneous.sum
      intro j _
      have h := (isWeightedHomogeneous_C (wXY k) (((g⁻¹ : GL (Fin k) K) : Matrix (Fin k) (Fin k) K) j i)).mul
        (isWeightedHomogeneous_X (R := K) (wXY k) (Sum.inr j))
      convert h using 1
      simp [wXY]
  rw [hgl, f.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro m hm
  rw [aeval_monomial, MvPolynomial.algebraMap_eq]
  have hdeg := hf (MvPolynomial.mem_support_iff.1 hm)
  rw [← hdeg]
  have hp : IsWeightedHomogeneous (wXY k) (m.prod fun v e => σ v ^ e) (Finsupp.weight (wXY k) m) := by
    rw [Finsupp.weight_apply, Finsupp.prod, Finsupp.sum]
    apply IsWeightedHomogeneous.prod
    intro v _
    exact (hσ v).pow (m v)
  rw [← zero_add (Finsupp.weight (wXY k) m)]
  exact (isWeightedHomogeneous_C (wXY k) (coeff m f)).mul hp

theorem pow_mul_inv_mem {K : Type} [Field K] [CharZero K] (R : Subring K) {p : ℕ} (hp : p.Prime)
    (hR : PLocal R p) {M e : ℕ} (hM : M ≠ 0) (hv : M.factorization p ≤ e) :
    (p : K) ^ e * (M : K)⁻¹ ∈ R := by
  have hsplit : p ^ M.factorization p * (M / p ^ M.factorization p) = M :=
    Nat.ordProj_mul_ordCompl_eq_self M p
  have hnd : ¬ p ∣ M / p ^ M.factorization p := Nat.not_dvd_ordCompl hp hM
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have e : (p : K) ^ e * (M : K)⁻¹ = (p : K) ^ (e - M.factorization p) * ((M / p ^ M.factorization p : ℕ) : K)⁻¹ := by
    conv_lhs => rw [← hsplit]
    rw [Nat.cast_mul, Nat.cast_pow, mul_inv, ← mul_assoc, ← pow_sub₀ _ hpK hv]
  rw [e]
  exact R.mul_mem (R.pow_mem (natCast_mem R p) _) (hR _ hnd)

theorem multinomial_factorization_le (p : ℕ) {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) :
    (Nat.multinomial s f).factorization p ≤ (s.card - 1) * Nat.log p (∑ i ∈ s, f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      simp [Nat.multinomial_singleton]
    · rw [Nat.multinomial_insert ha, Finset.sum_insert ha, Finset.card_insert_eq_ite, if_neg ha]
      have hc : (f a + ∑ i ∈ s, f i).choose (f a) ≠ 0 := (Nat.choose_pos (Nat.le_add_right _ _)).ne'
      have hm : Nat.multinomial s f ≠ 0 := (Nat.multinomial_pos _ _).ne'
      rw [Nat.factorization_mul hc hm, Finsupp.add_apply]
      have h1 : ((f a + ∑ i ∈ s, f i).choose (f a)).factorization p ≤ Nat.log p (f a + ∑ i ∈ s, f i) :=
        Nat.factorization_choose_le_log
      have h2 : Nat.log p (∑ i ∈ s, f i) ≤ Nat.log p (f a + ∑ i ∈ s, f i) :=
        Nat.log_mono_right (Nat.le_add_left _ _)
      have hcard : 1 ≤ s.card := hs.card_pos
      calc ((f a + ∑ i ∈ s, f i).choose (f a)).factorization p + (Nat.multinomial s f).factorization p
          ≤ Nat.log p (f a + ∑ i ∈ s, f i) + (s.card - 1) * Nat.log p (f a + ∑ i ∈ s, f i) :=
            add_le_add h1 (le_trans ih (Nat.mul_le_mul_left _ h2))
        _ = (s.card + 1 - 1) * Nat.log p (f a + ∑ i ∈ s, f i) := by
            have e : s.card + 1 - 1 = (s.card - 1) + 1 := by omega
            rw [e, add_mul, one_mul, add_comm]

def xMul {k : ℕ} (m : XY k →₀ ℕ) : ℕ := Nat.multinomial Finset.univ (fun i : Fin k => m (Sum.inl i))

def yMul {k : ℕ} (m : XY k →₀ ℕ) : ℕ := Nat.multinomial Finset.univ (fun i : Fin k => m (Sum.inr i))

theorem xFact_mul_xMul {k : ℕ} (m : XY k →₀ ℕ) : xFact m * xMul m = (xDeg m).factorial := by
  simp only [xFact, xMul, xDeg]
  exact Nat.multinomial_spec _ _

theorem yFact_mul_yMul {k : ℕ} (m : XY k →₀ ℕ) : yFact m * yMul m = (yDeg m).factorial := by
  simp only [yFact, yMul, yDeg]
  exact Nat.multinomial_spec _ _

theorem xMul_ne_zero {k : ℕ} (m : XY k →₀ ℕ) : xMul m ≠ 0 :=
  (Nat.multinomial_pos _ _).ne'
theorem yMul_ne_zero {k : ℕ} (m : XY k →₀ ℕ) : yMul m ≠ 0 :=
  (Nat.multinomial_pos _ _).ne'

theorem xMul_factorization_le {k : ℕ} (p : ℕ) (m : XY k →₀ ℕ) :
    (xMul m).factorization p ≤ (k - 1) * Nat.log p (xDeg m) := by
  simpa [xMul, xDeg, Finset.card_univ, Fintype.card_fin] using
    multinomial_factorization_le p Finset.univ (fun i : Fin k => m (Sum.inl i))

theorem yMul_factorization_le {k : ℕ} (p : ℕ) (m : XY k →₀ ℕ) :
    (yMul m).factorization p ≤ (k - 1) * Nat.log p (yDeg m) := by
  simpa [yMul, yDeg, Finset.card_univ, Fintype.card_fin] using
    multinomial_factorization_le p Finset.univ (fun i : Fin k => m (Sum.inr i))

theorem xFact_ne_zero {k : ℕ} (m : XY k →₀ ℕ) : xFact m ≠ 0 :=
  Finset.prod_ne_zero_iff.2 (fun i _ => Nat.factorial_ne_zero _)
theorem yFact_ne_zero {k : ℕ} (m : XY k →₀ ℕ) : yFact m ≠ 0 :=
  Finset.prod_ne_zero_iff.2 (fun i _ => Nat.factorial_ne_zero _)

section std
variable {K : Type} [Field K] [CharZero K] {k A B : ℕ} (R : Subring K)

theorem coeff_cases {f : PolXY K k} (hf : f ∈ PolAB K k A B) (m : XY k →₀ ℕ) :
    coeff m f = 0 ∨ (xDeg m = A ∧ yDeg m = B) := by
  by_cases h : coeff m f = 0
  · exact Or.inl h
  · exact Or.inr ((show ∀ m ∈ f.support, xDeg m = A ∧ yDeg m = B from hf) m
      (MvPolynomial.mem_support_iff.2 h))

theorem fock_to_gauss {f : PolXY K k} (hf : f ∈ PolAB K k A B) (h : f ∈ FockLat R) :
    (A.factorial : K) • f ∈ GaussLat R := by
  have h' : ∀ m, (xFact m : K) * coeff m f ∈ R := h
  show ∀ m, coeff m ((A.factorial : K) • f) ∈ R
  intro m
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  rcases coeff_cases hf m with h0 | ⟨hx, -⟩
  · rw [h0, mul_zero]
    exact R.zero_mem
  · rw [← hx, ← xFact_mul_xMul, Nat.cast_mul, mul_comm (xFact m : K), mul_assoc]
    exact R.mul_mem (natCast_mem R _) (h' m)

theorem gauss_to_fock {p : ℕ} (hp : p.Prime) (hR : PLocal R p) {f : PolXY K k} (hf : f ∈ PolAB K k A B)
    (h : f ∈ GaussLat R) :
    ((p : K) ^ ((k - 1) * Nat.log p A) * (A.factorial : K)⁻¹) • f ∈ FockLat R := by
  have h' : ∀ m, coeff m f ∈ R := h
  show ∀ m, (xFact m : K) * coeff m (((p : K) ^ ((k - 1) * Nat.log p A) * (A.factorial : K)⁻¹) • f) ∈ R
  intro m
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  rcases coeff_cases hf m with h0 | ⟨hx, -⟩
  · rw [h0, mul_zero, mul_zero]
    exact R.zero_mem
  · have hxm := xMul_ne_zero m
    have hxf : (xFact m : K) ≠ 0 := by exact_mod_cast xFact_ne_zero m
    have hmem := pow_mul_inv_mem R hp hR hxm (xMul_factorization_le p m)
    rw [← hx, ← xFact_mul_xMul, Nat.cast_mul, mul_inv]
    have e : (xFact m : K) * ((p : K) ^ ((k - 1) * Nat.log p (xDeg m)) *
        ((xFact m : K)⁻¹ * (xMul m : K)⁻¹) * coeff m f) =
        ((p : K) ^ ((k - 1) * Nat.log p (xDeg m)) * (xMul m : K)⁻¹) * coeff m f := by
      field_simp
    rw [e]
    exact R.mul_mem hmem (h' m)

theorem dual_to_fock {f : PolXY K k} (hf : f ∈ PolAB K k A B) (h : f ∈ DualLat R) :
    (B.factorial : K) • f ∈ FockLat R := by
  have h' : ∀ m, ((xFact m : K) * (yFact m : K)) * coeff m f ∈ R := h
  show ∀ m, (xFact m : K) * coeff m ((B.factorial : K) • f) ∈ R
  intro m
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  rcases coeff_cases hf m with h0 | ⟨-, hy⟩
  · rw [h0, mul_zero, mul_zero]
    exact R.zero_mem
  · rw [← hy, ← yFact_mul_yMul, Nat.cast_mul]
    have e : (xFact m : K) * (((yFact m : K) * (yMul m : K)) * coeff m f) =
        (yMul m : K) * (((xFact m : K) * (yFact m : K)) * coeff m f) := by ring
    rw [e]
    exact R.mul_mem (natCast_mem R _) (h' m)

theorem fock_to_dual {p : ℕ} (hp : p.Prime) (hR : PLocal R p) {f : PolXY K k} (hf : f ∈ PolAB K k A B)
    (h : f ∈ FockLat R) :
    ((p : K) ^ ((k - 1) * Nat.log p B) * (B.factorial : K)⁻¹) • f ∈ DualLat R := by
  have h' : ∀ m, (xFact m : K) * coeff m f ∈ R := h
  show ∀ m, ((xFact m : K) * (yFact m : K)) *
    coeff m (((p : K) ^ ((k - 1) * Nat.log p B) * (B.factorial : K)⁻¹) • f) ∈ R
  intro m
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  rcases coeff_cases hf m with h0 | ⟨-, hy⟩
  · rw [h0, mul_zero, mul_zero]
    exact R.zero_mem
  · have hym := yMul_ne_zero m
    have hyf : (yFact m : K) ≠ 0 := by exact_mod_cast yFact_ne_zero m
    have hmem := pow_mul_inv_mem R hp hR hym (yMul_factorization_le p m)
    rw [← hy, ← yFact_mul_yMul, Nat.cast_mul, mul_inv]
    have e : ((xFact m : K) * (yFact m : K)) * ((p : K) ^ ((k - 1) * Nat.log p (yDeg m)) *
        ((yFact m : K)⁻¹ * (yMul m : K)⁻¹) * coeff m f) =
        ((p : K) ^ ((k - 1) * Nat.log p (yDeg m)) * (yMul m : K)⁻¹) * ((xFact m : K) * coeff m f) := by
      field_simp
    rw [e]
    exact R.mul_mem hmem (h' m)

theorem sqrtFock_to_sqrtGauss {f : PolXY K k} (hf : f ∈ PolAB K k A B) (h : f ∈ SqrtFockLat R) :
    f ∈ SqrtGaussLat R (A.factorial * B.factorial) := by
  have h' : ∀ m, ((xFact m : K) * (yFact m : K)) * coeff m f ^ 2 ∈ R := h
  show ∀ m, ((A.factorial * B.factorial : ℕ) : K) * coeff m f ^ 2 ∈ R
  intro m
  rcases coeff_cases hf m with h0 | ⟨hx, hy⟩
  · rw [h0]
    simp
  · rw [← hx, ← hy, ← xFact_mul_xMul, ← yFact_mul_yMul]
    push_cast
    have e : (xFact m : K) * (xMul m : K) * ((yFact m : K) * (yMul m : K)) * coeff m f ^ 2 =
        ((xMul m : K) * (yMul m : K)) * (((xFact m : K) * (yFact m : K)) * coeff m f ^ 2) := by ring
    rw [e]
    exact R.mul_mem (R.mul_mem (natCast_mem R _) (natCast_mem R _)) (h' m)

theorem sqrtGauss_to_sqrtFock {p : ℕ} (hp : p.Prime) (hR : PLocal R p) {f : PolXY K k}
    (hf : f ∈ PolAB K k A B) (h : f ∈ SqrtGaussLat R (A.factorial * B.factorial)) :
    ((p : K) ^ ((k - 1) * Nat.log p (A + B + k))) • f ∈ SqrtFockLat R := by
  have h' : ∀ m, ((A.factorial * B.factorial : ℕ) : K) * coeff m f ^ 2 ∈ R := h
  show ∀ m, ((xFact m : K) * (yFact m : K)) * coeff m (((p : K) ^ ((k - 1) * Nat.log p (A + B + k))) • f) ^ 2 ∈ R
  intro m
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  rcases coeff_cases hf m with h0 | ⟨hx, hy⟩
  · rw [h0]
    simp
  · have hxb : (xMul m).factorization p ≤ (k - 1) * Nat.log p (A + B + k) :=
      le_trans (xMul_factorization_le p m) (Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega)))
    have hyb : (yMul m).factorization p ≤ (k - 1) * Nat.log p (A + B + k) :=
      le_trans (yMul_factorization_le p m) (Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega)))
    have hx1 := pow_mul_inv_mem R hp hR (xMul_ne_zero m) hxb
    have hy1 := pow_mul_inv_mem R hp hR (yMul_ne_zero m) hyb
    have hxf : (xMul m : K) ≠ 0 := by exact_mod_cast xMul_ne_zero m
    have hyf : (yMul m : K) ≠ 0 := by exact_mod_cast yMul_ne_zero m
    have hm := h' m
    rw [← hx, ← hy, ← xFact_mul_xMul, ← yFact_mul_yMul] at hm
    push_cast at hm
    have e : ((xFact m : K) * (yFact m : K)) * (((p : K) ^ ((k - 1) * Nat.log p (A + B + k))) * coeff m f) ^ 2 =
        ((((p : K) ^ ((k - 1) * Nat.log p (A + B + k))) * (xMul m : K)⁻¹) * (((p : K) ^ ((k - 1) * Nat.log p (A + B + k))) * (yMul m : K)⁻¹)) *
        ((xFact m : K) * (xMul m : K) * ((yFact m : K) * (yMul m : K)) * coeff m f ^ 2) := by
      first | (field_simp; ring) | field_simp
    rw [e]
    first | exact R.mul_mem (R.mul_mem hx1 hy1) hm |
      (convert R.mul_mem (R.mul_mem hx1 hy1) hm using 2; ring)

end std

theorem fockGaussLatticeComparison_holds : FockGaussXY := by
  intro K _ _ k A B p R g hk hp hR f hf
  have hf' : glAct g⁻¹ f ∈ PolAB K k A B := glAct_mem_PolAB g⁻¹ f hf
  constructor
  · intro h
    rw [mem_latOf_iff] at h ⊢
    rw [map_smul]
    exact fock_to_gauss R hf' h
  · intro h
    rw [mem_latOf_iff] at h ⊢
    rw [map_smul]
    exact gauss_to_fock R hp hR hf' h

theorem sqrtFockGaussLatticeComparison_holds : SqrtFockGaussXY := by
  intro K _ _ k A B p O g hk hp hR f hf
  have hf' : glAct g⁻¹ f ∈ PolAB K k A B := glAct_mem_PolAB g⁻¹ f hf
  constructor
  · intro h
    rw [mem_latOf_iff] at h ⊢
    exact sqrtFock_to_sqrtGauss O.toSubring hf' h
  · intro h
    rw [mem_latOf_iff] at h ⊢
    rw [map_smul]
    exact sqrtGauss_to_sqrtFock O.toSubring hp hR hf' h

theorem coeff_mem_of_h_pow_mul {K : Type} [Field K] {k : ℕ} (R : Subring K) (i0 : Fin k) (j : ℕ)
    (G : PolXY K k) (hG : hXY K k ^ j * G ∈ GaussLat R) : G ∈ GaussLat R := by
  induction j generalizing G with
  | zero => simpa using hG
  | succ n ih =>
    have h1 : hXY K k * G ∈ GaussLat R := ih (hXY K k * G) (by rw [← mul_assoc, ← pow_succ]; exact hG)
    exact coeff_mem_of_h_mul R i0 G h1

theorem gaussLemmaPairing_holds : GaussLemmaH := by
  intro K _ _ k O g j G hk h
  rw [mem_latOf_iff] at h ⊢
  rw [map_mul, map_pow, glAct_hXY] at h
  exact coeff_mem_of_h_pow_mul O.toSubring ⟨0, hk⟩ j _ h

theorem h_mul_mem_gauss {K : Type} [Field K] {k : ℕ} (R : Subring K) (G : PolXY K k) (hG : G ∈ GaussLat R) :
    hXY K k * G ∈ GaussLat R := by
  have hG' : ∀ m, coeff m G ∈ R := hG
  show ∀ m, coeff m (hXY K k * G) ∈ R
  intro m
  rw [MvPolynomial.coeff_mul]
  refine R.sum_mem fun x _ => R.mul_mem ?_ (hG' _)
  unfold hXY
  rw [MvPolynomial.coeff_sum]
  refine R.sum_mem fun i _ => ?_
  rw [MvPolynomial.coeff_X_mul', MvPolynomial.coeff_X']
  split_ifs <;> first | exact R.one_mem | exact R.zero_mem

theorem h_pow_mul_mem_gauss {K : Type} [Field K] {k : ℕ} (R : Subring K) (j : ℕ) (G : PolXY K k)
    (hG : G ∈ GaussLat R) : hXY K k ^ j * G ∈ GaussLat R := by
  induction j with
  | zero => simpa using hG
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    exact h_mul_mem_gauss R _ ih

theorem isotypicLattice_holds : LevelLattice := by
  intro K _ _ k a b j O g hk
  ext f
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
  constructor
  · rintro ⟨hf, w, hw, rfl⟩
    exact ⟨w, ⟨gaussLemmaPairing_holds K k O g j w hk hf, hw⟩, rfl⟩
  · rintro ⟨w, ⟨hwl, hw⟩, rfl⟩
    refine ⟨?_, w, hw, rfl⟩
    rw [mem_latOf_iff] at hwl ⊢
    rw [map_mul, map_pow, glAct_hXY]
    exact h_pow_mul_mem_gauss O.toSubring j _ hwl

theorem xDeg_add {k : ℕ} (m n : XY k →₀ ℕ) : xDeg (m + n) = xDeg m + xDeg n := by
  simp [xDeg, Finset.sum_add_distrib]
theorem yDeg_add {k : ℕ} (m n : XY k →₀ ℕ) : yDeg (m + n) = yDeg m + yDeg n := by
  simp [yDeg, Finset.sum_add_distrib]
theorem xDeg_single_inl {k : ℕ} (i : Fin k) (n : ℕ) : xDeg (Finsupp.single (Sum.inl i : XY k) n) = n := by
  simp [xDeg, Finsupp.single_apply]
theorem xDeg_single_inr {k : ℕ} (i : Fin k) (n : ℕ) : xDeg (Finsupp.single (Sum.inr i : XY k) n) = 0 := by
  simp [xDeg, Finsupp.single_apply]
theorem yDeg_single_inl {k : ℕ} (i : Fin k) (n : ℕ) : yDeg (Finsupp.single (Sum.inl i : XY k) n) = 0 := by
  simp [yDeg, Finsupp.single_apply]
theorem yDeg_single_inr {k : ℕ} (i : Fin k) (n : ℕ) : yDeg (Finsupp.single (Sum.inr i : XY k) n) = n := by
  simp [yDeg, Finsupp.single_apply]

section deg
variable {K : Type} [Field K] {k : ℕ}

private theorem coeff_pderiv_eq_coeff_add_single_mul_multinomial_depth (v : XY k) (F : PolXY K k) (m : XY k →₀ ℕ) :
    coeff m (pderiv v F) = coeff (m + Finsupp.single v 1) F * ((m v : K) + 1) := by
  refine MvPolynomial.induction_on' F ?_ ?_
  · intro s a
    rw [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases hs : s = m + Finsupp.single v 1
    · subst hs
      simp
    · rw [if_neg hs, zero_mul]
      split_ifs with h
      · have hsv : s v = 0 := by
          by_contra hne
          apply hs
          rw [← h]
          ext u
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
          split_ifs with hu
          · subst hu
            omega
          · omega
        simp [hsv]
      · rfl
  · intro p q hp hq
    rw [map_add, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add, add_mul]

theorem coeff_ctrF (f : PolXY K k) (m : XY k →₀ ℕ) :
    coeff m (ctrF K k f) = ∑ i : Fin k,
      coeff (m + Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr i) 1) f *
        ((m (Sum.inr i) : K) + 1) * ((m (Sum.inl i) : K) + 1) := by
  unfold ctrF
  rw [LinearMap.sum_apply, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply]
  show coeff m (pderiv (R := K) (Sum.inl i : XY k) (pderiv (R := K) (Sum.inr i : XY k) f)) = _
  rw [coeff_pderiv_eq_coeff_add_single_mul_multinomial_depth, coeff_pderiv_eq_coeff_add_single_mul_multinomial_depth, Finsupp.add_apply, Finsupp.single_apply, if_neg Sum.inl_ne_inr,
    add_zero]

theorem ctrF_mem_PolAB {a b : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k a b) :
    ctrF K k f ∈ PolAB K k (a - 1) (b - 1) := by
  show ∀ m ∈ (ctrF K k f).support, xDeg m = a - 1 ∧ yDeg m = b - 1
  intro m hm
  rw [MvPolynomial.mem_support_iff, coeff_ctrF] at hm
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  have hc : coeff (m + Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr i) 1) f ≠ 0 := by
    intro h0
    apply hi
    rw [h0]
    ring
  have hf' := (show ∀ m ∈ f.support, xDeg m = a ∧ yDeg m = b from hf) _ (MvPolynomial.mem_support_iff.2 hc)
  rw [xDeg_add, xDeg_add, yDeg_add, yDeg_add, xDeg_single_inl, xDeg_single_inr, yDeg_single_inl,
    yDeg_single_inr] at hf'
  omega

theorem ctrF_pow_mem_PolAB {a b : ℕ} (l : ℕ) {f : PolXY K k} (hf : f ∈ PolAB K k a b) :
    (ctrF K k ^ l) f ∈ PolAB K k (a - l) (b - l) := by
  induction l with
  | zero => simpa using hf
  | succ n ih =>
    rw [pow_succ']
    show ctrF K k ((ctrF K k ^ n) f) ∈ _
    have h := ctrF_mem_PolAB (K := K) ih
    convert h using 2 <;> omega

theorem ctrDiv_mem_PolAB {a b : ℕ} (l : ℕ) {f : PolXY K k} (hf : f ∈ PolAB K k a b) :
    ctrDiv K k l f ∈ PolAB K k (a - l) (b - l) := by
  unfold ctrDiv
  rw [LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (ctrF_pow_mem_PolAB l hf)

theorem hXY_mem_PolAB : hXY K k ∈ PolAB K k 1 1 := by
  rw [mem_PolAB_iff]
  unfold hXY
  apply IsWeightedHomogeneous.sum
  intro i _
  have h := (isWeightedHomogeneous_X (R := K) (wXY k) (Sum.inl i)).mul
    (isWeightedHomogeneous_X (R := K) (wXY k) (Sum.inr i))
  convert h using 1
  simp [wXY]

theorem mul_mem_PolAB {a b a' b' : ℕ} {f f' : PolXY K k} (hf : f ∈ PolAB K k a b)
    (hf' : f' ∈ PolAB K k a' b') : f * f' ∈ PolAB K k (a + a') (b + b') := by
  rw [mem_PolAB_iff] at hf hf' ⊢
  simpa using hf.mul hf'

theorem h_pow_mul_mem_PolAB {a b : ℕ} (l : ℕ) {f : PolXY K k} (hf : f ∈ PolAB K k a b) :
    hXY K k ^ l * f ∈ PolAB K k (a + l) (b + l) := by
  induction l with
  | zero => simpa using hf
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    have h := mul_mem_PolAB hXY_mem_PolAB ih
    convert h using 2 <;> omega

theorem hDiv_mem_PolAB {a b : ℕ} (l : ℕ) {f : PolXY K k} (hf : f ∈ PolAB K k a b) :
    hDiv K k l f ∈ PolAB K k (a + l) (b + l) := by
  unfold hDiv
  rw [LinearMap.smul_apply, LinearMap.mulLeft_apply]
  exact Submodule.smul_mem _ _ (h_pow_mul_mem_PolAB l hf)

theorem harProj_mem_PolAB {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    harProj K k A B f ∈ PolAB K k A B := by
  unfold harProj
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l hl => ?_
  rw [LinearMap.smul_apply, LinearMap.comp_apply]
  refine Submodule.smul_mem _ _ ?_
  have hl' : l ≤ min A B := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
  have h := hDiv_mem_PolAB (K := K) l (ctrDiv_mem_PolAB (K := K) l hf)
  rwa [Nat.sub_add_cancel (le_trans hl' (min_le_left _ _)),
    Nat.sub_add_cancel (le_trans hl' (min_le_right _ _))] at h

theorem levelProj_mem_PolAB {A B j : ℕ} (hj : j ≤ min A B) {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    levelProj K k A B j f ∈ PolAB K k A B := by
  unfold levelProj
  rw [LinearMap.smul_apply]
  refine Submodule.smul_mem _ _ ?_
  simp only [LinearMap.comp_apply]
  have h := hDiv_mem_PolAB (K := K) j (harProj_mem_PolAB (ctrDiv_mem_PolAB j hf))
  have hA : A - j + j = A := Nat.sub_add_cancel (le_trans hj (min_le_left _ _))
  have hB : B - j + j = B := Nat.sub_add_cancel (le_trans hj (min_le_right _ _))
  rwa [hA, hB] at h

theorem smul_mem_latOf_gauss (R : Subring K) (g : GL (Fin k) K) {r : K} (hr : r ∈ R) {f : PolXY K k}
    (hf : f ∈ latOf g (GaussLat R)) : r • f ∈ latOf g (GaussLat R) := by
  obtain ⟨h, hh, rfl⟩ := hf
  have hh' : ∀ m, coeff m h ∈ R := hh
  refine ⟨r • h, ?_, by rw [map_smul]⟩
  show ∀ m, coeff m (r • h) ∈ R
  intro m
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  exact R.mul_mem hr (hh' m)

theorem smul_mem_latOf_dual (R : Subring K) (g : GL (Fin k) K) {r : K} (hr : r ∈ R) {f : PolXY K k}
    (hf : f ∈ latOf g (DualLat R)) : r • f ∈ latOf g (DualLat R) := by
  obtain ⟨h, hh, rfl⟩ := hf
  have hh' : ∀ m, ((xFact m : K) * (yFact m : K)) * coeff m h ∈ R := hh
  refine ⟨r • h, ?_, by rw [map_smul]⟩
  show ∀ m, ((xFact m : K) * (yFact m : K)) * coeff m (r • h) ∈ R
  intro m
  rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_left_comm]
  exact R.mul_mem hr (hh' m)

end deg

theorem gauss_dual_of_fock {K : Type} [Field K] [CharZero K] {k A B p : ℕ} (R : Subring K) (g : GL (Fin k) K)
    (hk : 1 ≤ k) (hp : p.Prime) (hR : PLocal R p) (T : PolXY K k →ₗ[K] PolXY K k)
    (hT : ∀ f, f ∈ PolAB K k A B → T f ∈ PolAB K k A B) (n : ℕ) (hn : n ≤ 2 * Nat.log p (A + B + k))
    (hF : ∀ f, f ∈ PolAB K k A B → f ∈ latOf g (FockLat R) → ((p : K) ^ n) • T f ∈ latOf g (FockLat R))
    (f : PolXY K k) (hf : f ∈ PolAB K k A B) :
    (f ∈ latOf g (GaussLat R) → ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • T f ∈ latOf g (GaussLat R)) ∧
    (f ∈ latOf g (DualLat R) → ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • T f ∈ latOf g (DualLat R)) := by
  have hAf : (A.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hBf : (B.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hL : ∀ X : ℕ, X ≤ A + B + k →
      (k - 1) * Nat.log p X + n ≤ (k + 1) * Nat.log p (A + B + k) := by
    intro X hX
    have hlX : Nat.log p X ≤ Nat.log p (A + B + k) := Nat.log_mono_right hX
    calc (k - 1) * Nat.log p X + n ≤ (k - 1) * Nat.log p (A + B + k) + 2 * Nat.log p (A + B + k) :=
          add_le_add (Nat.mul_le_mul_left _ hlX) hn
      _ = (k + 1) * Nat.log p (A + B + k) := by rw [← add_mul]; congr 1; omega
  have hpow : ∀ a b : ℕ, a ≤ b → ∀ x : PolXY K k, ((p : K) ^ b) • x = ((p : K) ^ (b - a)) • (((p : K) ^ a) • x) := by
    intro a b hab x
    rw [smul_smul, ← pow_add, Nat.sub_add_cancel hab]
  have hpR : ∀ a : ℕ, (p : K) ^ a ∈ R := fun a => R.pow_mem (natCast_mem R p) a
  refine ⟨fun hG => ?_, fun hD => ?_⟩
  · have h1 := (fockGaussLatticeComparison_holds K k A B p R g hk hp hR f hf).2 hG
    have hcf : ((p : K) ^ ((k - 1) * Nat.log p A) * (A.factorial : K)⁻¹) • f ∈ PolAB K k A B :=
      Submodule.smul_mem _ _ hf
    have h2 := hF _ hcf h1
    have hpol : ((p : K) ^ n) • T (((p : K) ^ ((k - 1) * Nat.log p A) * (A.factorial : K)⁻¹) • f) ∈
        PolAB K k A B := Submodule.smul_mem _ _ (hT _ hcf)
    have h3 := (fockGaussLatticeComparison_holds K k A B p R g hk hp hR _ hpol).1 h2
    have e : (A.factorial : K) • (((p : K) ^ n) •
        T (((p : K) ^ ((k - 1) * Nat.log p A) * (A.factorial : K)⁻¹) • f)) =
        ((p : K) ^ ((k - 1) * Nat.log p A + n)) • T f := by
      rw [map_smul, smul_smul, smul_smul]
      congr 1
      field_simp
      ring
    rw [e] at h3
    rw [hpow _ _ (hL A (by omega))]
    exact smul_mem_latOf_gauss R g (hpR _) h3
  · have hf' := glAct_mem_PolAB g⁻¹ f hf
    have h1 : (B.factorial : K) • f ∈ latOf g (FockLat R) := by
      rw [mem_latOf_iff, map_smul]
      exact dual_to_fock R hf' ((mem_latOf_iff g _ f).1 hD)
    have hbf : (B.factorial : K) • f ∈ PolAB K k A B := Submodule.smul_mem _ _ hf
    have h2 := hF _ hbf h1
    have hpol : ((p : K) ^ n) • T ((B.factorial : K) • f) ∈ PolAB K k A B :=
      Submodule.smul_mem _ _ (hT _ hbf)
    have h3 : ((p : K) ^ ((k - 1) * Nat.log p B) * (B.factorial : K)⁻¹) •
        (((p : K) ^ n) • T ((B.factorial : K) • f)) ∈ latOf g (DualLat R) := by
      rw [mem_latOf_iff] at h2 ⊢
      rw [map_smul]
      exact fock_to_dual R hp hR (glAct_mem_PolAB g⁻¹ _ hpol) h2
    have e : ((p : K) ^ ((k - 1) * Nat.log p B) * (B.factorial : K)⁻¹) •
        (((p : K) ^ n) • T ((B.factorial : K) • f)) =
        ((p : K) ^ ((k - 1) * Nat.log p B + n)) • T f := by
      rw [map_smul, smul_smul, smul_smul]
      congr 1
      field_simp
      ring
    rw [e] at h3
    rw [hpow _ _ (hL B (by omega))]
    exact smul_mem_latOf_dual R g (hpR _) h3

theorem gaussProj_of (H : FockProj) : GaussProj := by
  intro K _ _ k A B p R g hk hp hR f hf
  have hhar := gauss_dual_of_fock R g hk hp hR (harProj K k A B) (fun f' hf' => harProj_mem_PolAB hf')
    (Nat.log p (A + B + k)) (by omega) (fun f' hf' hfl => (H K k A B p R g hk hp hR f' hf' hfl).1) f hf
  have lev := fun (j : ℕ) (hj : j ≤ min A B) => gauss_dual_of_fock R g hk hp hR (levelProj K k A B j)
    (fun f' hf' => levelProj_mem_PolAB hj hf') (2 * Nat.log p (A + B + k)) le_rfl
    (fun f' hf' hfl => (H K k A B p R g hk hp hR f' hf' hfl).2 j hj) f hf
  exact ⟨fun hG => ⟨hhar.1 hG, fun j hj => (lev j hj).1 hG⟩,
    fun hD => ⟨hhar.2 hD, fun j hj => (lev j hj).2 hD⟩⟩

theorem exponent_le {k A B a p e : ℕ} (hk : 1 ≤ k) (hp : p.Prime) (hA : A ≤ 8 * a) (hB : B ≤ 8 * a)
    (he : 3 * (Real.logb p (8 * (a : ℝ) + k - 1) + 1) + 4 * (k : ℝ) * (Real.logb p (8 * (a : ℝ) + k - 1) + 1)
      ≤ (e : ℝ)) : (k + 1) * Nat.log p (A + B + k) ≤ e := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  set L := Nat.log p (A + B + k) with hLdef
  set x : ℕ := 8 * a + k - 1 with hxdef
  have hxr : (x : ℝ) = 8 * (a : ℝ) + k - 1 := by
    rw [hxdef, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [← hxr] at he
  have hLX : (L : ℝ) ≤ Real.logb p x + 1 := by
    rcases Nat.eq_zero_or_pos L with hL0 | hLpos
    · rw [hL0]
      push_cast
      rcases Nat.eq_zero_or_pos x with hx0 | hxpos
      · rw [hx0]
        simp
      · have h0 : (0 : ℝ) ≤ Real.logb p x := Real.logb_nonneg hp1 (by exact_mod_cast hxpos)
        linarith
    · have hN : A + B + k ≠ 0 := by omega
      have hpow : p ^ L ≤ A + B + k := Nat.pow_log_le_self p hN
      have h2 : 2 * p ^ (L - 1) ≤ p ^ L := by
        have e1 : p ^ L = p * p ^ (L - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [e1]
        exact Nat.mul_le_mul_right _ hp.two_le
      have hy : p ^ (L - 1) ≤ x := by omega
      have hyR : ((p ^ (L - 1) : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hy
      have hposR : (0 : ℝ) < ((p ^ (L - 1) : ℕ) : ℝ) := by exact_mod_cast pow_pos hp.pos _
      have hlog := (Real.logb_le_logb hp1 hposR (lt_of_lt_of_le hposR hyR)).2 hyR
      rw [Nat.cast_pow, Real.logb_pow, Real.logb_self_eq_one hp1, mul_one] at hlog
      have e2 : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
        rw [Nat.cast_sub hLpos]
        simp
      linarith
  have hX1 : 0 ≤ Real.logb p x + 1 := le_trans (Nat.cast_nonneg L) hLX
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hfin : ((k : ℝ) + 1) * (L : ℝ) ≤ (e : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hLX (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1),
      mul_nonneg (by positivity : (0 : ℝ) ≤ 2 + 3 * (k : ℝ)) hX1]
  exact_mod_cast hfin

theorem gaussProjText_of (H : GaussProj) : GaussProjText := by
  intro K _ _ k A B a p e R g hk hp hR hA hB he f hf j hj
  have hE := exponent_le hk hp hA hB he
  have hpe : (p : K) ^ e = (p : K) ^ (e - (k + 1) * Nat.log p (A + B + k)) *
      (p : K) ^ ((k + 1) * Nat.log p (A + B + k)) := by
    rw [← pow_add, Nat.sub_add_cancel hE]
  have hmem : (p : K) ^ (e - (k + 1) * Nat.log p (A + B + k)) ∈ R := R.pow_mem (natCast_mem R p) _
  obtain ⟨h1, h2⟩ := H K k A B p R g hk hp hR f hf
  refine ⟨fun hG => ?_, fun hD => ?_⟩
  · rw [hpe, mul_smul]
    exact smul_mem_latOf_gauss R g hmem ((h1 hG).2 j hj)
  · rw [hpe, mul_smul]
    exact smul_mem_latOf_dual R g hmem ((h2 hD).2 j hj)

attribute [local instance] MvPolynomial.weightedGradedAlgebra in
open DirectSum in
theorem exists_cofactor {K : Type} [Field K] {k A B : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) {w G : PolXY K k}
    (hw : w ∈ PolAB K k A B) (h : w = hXY K k * G) :
    ∃ G' ∈ PolAB K k (A - 1) (B - 1), w = hXY K k * G' := by
  classical
  let 𝒜 := weightedHomogeneousSubmodule K (wXY k)
  have hh : hXY K k ∈ 𝒜 (1, 1) := (mem_PolAB_iff _).1 hXY_mem_PolAB
  have hw' : w ∈ 𝒜 (A, B) := (mem_PolAB_iff _).1 hw
  refine ⟨(decompose 𝒜 G (A - 1, B - 1) : PolXY K k), (mem_PolAB_iff _).2 (decompose 𝒜 G (A - 1, B - 1)).2, ?_⟩
  rw [← DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 hh, ← h]
  have : ((1, 1) + (A - 1, B - 1) : ℕ × ℕ) = (A, B) := by
    ext <;> simp <;> omega
  rw [this, DirectSum.decompose_of_mem_same 𝒜 hw']

theorem h_mul_eq_zero_of_deg {K : Type} [Field K] {k A B : ℕ} (hAB : A = 0 ∨ B = 0) {w G : PolXY K k}
    (hw : w ∈ PolAB K k A B) (h : w = hXY K k * G) : w = 0 := by
  subst h
  ext m
  rw [MvPolynomial.coeff_zero]
  by_cases h0 : coeff m (hXY K k * G) = 0
  · exact h0
  · obtain ⟨hx, hy⟩ := (show ∀ m ∈ (hXY K k * G).support, xDeg m = A ∧ yDeg m = B from hw) m
      (MvPolynomial.mem_support_iff.2 h0)
    unfold hXY
    rw [Finset.sum_mul, MvPolynomial.coeff_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases hAB with hA | hB
    · have hle : m (Sum.inl i) ≤ xDeg m :=
        Finset.single_le_sum (f := fun j => m (Sum.inl j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have hmi : m (Sum.inl i) = 0 := by omega
      rw [mul_assoc, MvPolynomial.coeff_X_mul', if_neg (by simpa [Finsupp.mem_support_iff] using hmi)]
    · have hle : m (Sum.inr i) ≤ yDeg m :=
        Finset.single_le_sum (f := fun j => m (Sum.inr j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have hmi : m (Sum.inr i) = 0 := by omega
      rw [mul_comm (X (Sum.inl i)) (X (Sum.inr i)), mul_assoc, MvPolynomial.coeff_X_mul',
        if_neg (by simpa [Finsupp.mem_support_iff] using hmi)]

theorem harQuot_of (H1 : HarProj) (H2 : GaussProj) : HarQuot := by
  intro K _ _ k A B p O g hk hp hR
  obtain ⟨H1a, H1b, H1c⟩ := H1 K k A B hk
  refine ⟨fun w G hw hwG => ?_, fun f hf hfl => ?_⟩
  · have hwP : w ∈ PolAB K k A B :=
      (Submodule.mem_inf.1 (show w ∈ PolAB K k A B ⊓ LinearMap.ker (ctrF K k) from hw)).1
    by_cases hAB : 1 ≤ A ∧ 1 ≤ B
    · obtain ⟨G', hG', hwG'⟩ := exists_cofactor hAB.1 hAB.2 hwP hwG
      have e1 := H1b w hw
      have e2 := H1c hAB.1 hAB.2 G' hG'
      rw [← hwG'] at e2
      rw [← e1]
      exact e2
    · exact h_mul_eq_zero_of_deg (by omega) hwP hwG
  · obtain ⟨hhar, g', hg', hdiff⟩ := H1a f hf
    have hEO : (p : K) ^ ((k + 1) * Nat.log p (A + B + k)) ∈ O.toSubring :=
      O.toSubring.pow_mem (natCast_mem _ p) _
    have hw := ((H2 K k A B p O.toSubring g hk hp hR f hf).1 hfl).1
    refine ⟨((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • harProj K k A B f, Submodule.smul_mem _ _ hhar,
      ((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • g', Submodule.smul_mem _ _ hg', hw, ?_, ?_⟩
    · apply gaussLemmaPairing_holds K k O g 1 _ hk
      rw [pow_one, mul_smul_comm, ← hdiff, smul_sub]
      have hf1 := smul_mem_latOf_gauss _ g hEO hfl
      rw [mem_latOf_iff] at hf1 hw ⊢
      rw [map_sub]
      have h1' : ∀ m, coeff m (glAct g⁻¹ (((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) • f)) ∈ O.toSubring := hf1
      have h2' : ∀ m, coeff m (glAct g⁻¹ (((p : K) ^ ((k + 1) * Nat.log p (A + B + k))) •
        harProj K k A B f)) ∈ O.toSubring := hw
      show ∀ m, coeff m (_ - _) ∈ O.toSubring
      intro m
      rw [MvPolynomial.coeff_sub]
      exact O.toSubring.sub_mem (h1' m) (h2' m)
    · rw [mul_smul_comm, ← hdiff, smul_sub]
      abel

end Har4

theorem fockGaussLatticeComparison_holds : FockGaussXY := Har4.fockGaussLatticeComparison_holds
theorem sqrtFockGaussLatticeComparison_holds : SqrtFockGaussXY := Har4.sqrtFockGaussLatticeComparison_holds
theorem gaussLemmaPairing_holds : GaussLemmaH := Har4.gaussLemmaPairing_holds
theorem pairingPrime_holds : HPrime := Har4.pairingPrime_holds
theorem isotypicLattice_holds : LevelLattice := Har4.isotypicLattice_holds
theorem gaussLatticeProjection_holds : GaussProj := Har4.gaussProj_of fockLatticeProjection_holds
theorem gaussLatticeProjectionExponent_holds : GaussProjText := Har4.gaussProjText_of gaussLatticeProjection_holds
theorem harmonicQuotient_holds : HarQuot := Har4.harQuot_of harmonicProjection_holds gaussLatticeProjection_holds

end Formalism.CountingSumsFrames
