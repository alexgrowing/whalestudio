import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

namespace Flag

open MvPolynomial Finset

noncomputable section

theorem vandermondeOf_eq_det {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) :
    vandermondeOf v = (Matrix.vandermonde (fun i => -v i)).det := by
  rw [Matrix.det_vandermonde, vandermondeOf]
  refine Finset.prod_congr rfl (fun i _ => Finset.prod_congr rfl (fun j _ => ?_))
  ring

theorem vandermondeOf_perm {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R)
    (σ : Equiv.Perm (Fin m)) :
    vandermondeOf (fun i => v (σ i)) = (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * vandermondeOf v := by
  rw [vandermondeOf_eq_det, vandermondeOf_eq_det]
  have : Matrix.vandermonde (fun i => -v (σ i)) =
      (Matrix.vandermonde (fun i => -v i)).submatrix σ id := by
    ext i j; rfl
  rw [this, Matrix.det_permute]

theorem derivation_prod_eq_zero {R A M : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] (D : Derivation R A M) {ι : Type*} (s : Finset ι) (g : ι → A) (hg : ∀ i ∈ s, D (g i) = 0) :
    D (∏ i ∈ s, g i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, hg a (Finset.mem_insert_self a s),
      ih (fun i hi => hg i (Finset.mem_insert_of_mem hi)), smul_zero, smul_zero, add_zero]

theorem derivation_vandermondeOf_eq_zero {R A M : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] (D : Derivation R A M) {m : ℕ} (v : Fin m → A) (hv : ∀ i j, D (v i) = D (v j)) :
    D (vandermondeOf v) = 0 := by
  unfold vandermondeOf
  refine derivation_prod_eq_zero D _ _ (fun i _ => derivation_prod_eq_zero D _ _ (fun j _ => ?_))
  rw [map_sub, hv i j, sub_self]

theorem blockPermute_blockPermute (f N : ℕ) (v w : Fin f → Equiv.Perm (Fin N)) (H : RootRing f N) :
    blockPermute f N v (blockPermute f N w H) = blockPermute f N (v * w) H := by
  simp only [blockPermute, rename_rename]
  rfl

theorem blockSign_mul (f N : ℕ) (v w : Fin f → Equiv.Perm (Fin N)) :
    blockSign f N (v * w) = blockSign f N v * blockSign f N w := by
  simp only [blockSign, ← Finset.prod_mul_distrib, Pi.mul_apply, Equiv.Perm.sign_mul, Units.val_mul,
    Int.cast_mul]

theorem blockSign_mul_self (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) :
    blockSign f N w * blockSign f N w = 1 := by
  simp only [blockSign, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun τ _ => ?_)
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

theorem blockPermute_X (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) (τ : Fin f) (i : Fin N) :
    blockPermute f N w (X (τ, i)) = X (τ, w τ i) := by
  simp [blockPermute]

theorem blockPermute_blockVandermonde (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) :
    blockPermute f N w (blockVandermonde f N) = blockSign f N w • blockVandermonde f N := by
  simp only [blockVandermonde, map_prod]
  have h1 : ∀ τ : Fin f, blockPermute f N w (vandermondeOf fun i : Fin N => (X (τ, i) : RootRing f N)) =
      (((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : RootRing f N) *
        vandermondeOf fun i : Fin N => (X (τ, i) : RootRing f N) := by
    intro τ
    have : blockPermute f N w (vandermondeOf fun i : Fin N => (X (τ, i) : RootRing f N)) =
        vandermondeOf fun i : Fin N => (X (τ, w τ i) : RootRing f N) := by
      simp only [vandermondeOf, map_prod, map_sub, blockPermute_X]
    rw [this]
    exact vandermondeOf_perm (fun i : Fin N => (X (τ, i) : RootRing f N)) (w τ)
  rw [Finset.prod_congr rfl (fun τ _ => h1 τ), Finset.prod_mul_distrib, Algebra.smul_def,
    blockSign, map_prod]
  simp

theorem blockVandermonde_ne_zero (f N : ℕ) : blockVandermonde f N ≠ 0 := by
  simp only [blockVandermonde, vandermondeOf]
  refine Finset.prod_ne_zero_iff.mpr (fun τ _ => Finset.prod_ne_zero_iff.mpr
    (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j hj => ?_)))
  rw [sub_ne_zero]
  intro h
  have := X_injective h
  simp only [Prod.mk.injEq, true_and] at this
  rw [Finset.mem_Ioi] at hj
  exact (ne_of_lt hj) this

theorem blockPermute_antisymmetrize (f N : ℕ) (v : Fin f → Equiv.Perm (Fin N)) (H : RootRing f N) :
    blockPermute f N v (antisymmetrize f N H) = blockSign f N v • antisymmetrize f N H := by
  simp only [antisymmetrize, map_sum, map_smul, blockPermute_blockPermute, Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft v) _ _ (fun w => ?_)
  simp only [Equiv.coe_mulLeft]
  congr 1
  rw [blockSign_mul, ← mul_assoc, blockSign_mul_self, one_mul]

theorem card_blockPerm (f N : ℕ) : Fintype.card (Fin f → Equiv.Perm (Fin N)) = N.factorial ^ f := by
  simp [Fintype.card_perm]

theorem antisymmetrize_blockVandermonde (f N : ℕ) :
    antisymmetrize f N (blockVandermonde f N) =
      ((N.factorial : ℚ) ^ f) • blockVandermonde f N := by
  simp only [antisymmetrize, blockPermute_blockVandermonde, smul_smul, blockSign_mul_self, one_smul,
    Finset.sum_const, Finset.card_univ, card_blockPerm]
  rw [← Nat.cast_smul_eq_nsmul ℚ]
  push_cast
  rfl

end

end Flag

theorem DividedDifferenceOfVandermonde.intersectionNumber_baseChange : DividedDifferenceOfVandermonde.Statement := by
  intro f N
  rw [dividedDifference, Flag.antisymmetrize_blockVandermonde, Algebra.smul_def, map_mul,
    mul_div_assoc, div_self, mul_one]
  · exact (IsScalarTower.algebraMap_apply ℚ (RootRing f N) _ _).symm
  · intro h
    exact Flag.blockVandermonde_ne_zero f N
      ((IsFractionRing.injective (RootRing f N) (FractionRing (RootRing f N))) (by simpa using h))

namespace Flag

open MvPolynomial Finset

noncomputable section

section Deriv

variable {σ ι : Type*}

def sumPderiv (s : Finset ι) (g : ι → σ) : Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ) :=
  ∑ l ∈ s, pderiv (g l)

theorem sumPderiv_apply (s : Finset ι) (g : ι → σ) (P : MvPolynomial σ ℚ) :
    sumPderiv s g P = ∑ l ∈ s, pderiv (g l) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sumPderiv]
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, ← ih]
    simp [sumPderiv, Finset.sum_insert hb]

theorem sumPderiv_X [DecidableEq σ] (s : Finset ι) (g : ι → σ) (v : σ) :
    sumPderiv s g (X v) = C (((s.filter fun l => g l = v).card : ℕ) : ℚ) := by
  rw [sumPderiv_apply, map_natCast]
  simp only [pderiv_X, Pi.single_apply]
  rw [Finset.sum_boole]
  simp only [eq_comm]

end Deriv

section Indices

variable {f r a : ℕ}

theorem yIndex_eq_yIndex_iff (c : SmallBlock) (τ σ : Fin f) (l i : Fin r) :
    yIndex f r a c τ l = yIndex f r a c σ i ↔ τ = σ ∧ l = i := by
  cases c <;> simp only [yIndex, Prod.mk.injEq, Fin.mk.injEq, Fin.ext_iff] <;> omega

theorem zIndex_eq_zIndex_iff (c : SmallBlock) (τ σ : Fin f) (l i : Fin a) :
    zIndex f r a c τ l = zIndex f r a c σ i ↔ τ = σ ∧ l = i := by
  cases c <;> simp only [zIndex, Prod.mk.injEq, Fin.mk.injEq, Fin.ext_iff] <;> omega

theorem yIndex_ne_zIndex (c : SmallBlock) (τ σ : Fin f) (l : Fin r) (i : Fin a) :
    yIndex f r a c τ l ≠ zIndex f r a c σ i := by
  cases c <;> simp only [yIndex, zIndex, ne_eq, Prod.mk.injEq, Fin.mk.injEq, not_and] <;>
    intro _ <;> omega

end Indices

section Rest

variable (f r a : ℕ) (c : SmallBlock)

theorem derivation_restPolynomial (D : Derivation ℚ (RootRing f (r + a)) (RootRing f (r + a)))
    (α β : Fin f → ℚ) (hy : ∀ σ i, D (X (yIndex f r a c σ i)) = C (α σ))
    (hz : ∀ σ i, D (X (zIndex f r a c σ i)) = C (β σ)) :
    D (fibreClass f r a c) = 0 ∧
    D (restPolynomial f r a c) =
      C (((f * (r * a) + 1 : ℕ) : ℚ) * (c.sign * r * ∑ σ, α σ)) *
        (smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c) := by
  have hyr : ∀ σ i, D (yRoot f r a c σ i) = C (c.sign * α σ) := by
    intro σ i
    rw [yRoot, C_mul', D.map_smul, hy, smul_eq_C_mul, ← C_mul]
  have hzr : ∀ σ i, D (zRoot f r a c σ i) = C (β σ) := fun σ i => hz σ i
  have hfib : D (fibreClass f r a c) = 0 := by
    unfold fibreClass
    refine derivation_prod_eq_zero D _ _ (fun σ _ => ?_)
    rw [Derivation.leibniz,
      derivation_vandermondeOf_eq_zero D _ (fun i j => by rw [hzr, hzr]),
      derivation_vandermondeOf_eq_zero D _ (fun i j => by rw [hyr, hyr]), smul_zero, smul_zero,
      add_zero]
  refine ⟨hfib, ?_⟩
  have hmu : D (smallBlockMu f r a c) = C (c.sign * r * ∑ σ, α σ) := by
    simp only [smallBlockMu, map_sum, hyr, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [show (r : RootRing f (r + a)) = C (r : ℚ) from (map_natCast C r).symm]
    simp_rw [← C_mul, ← map_sum]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    ring
  rw [restPolynomial, Derivation.leibniz, hfib, smul_zero, zero_add, Derivation.leibniz_pow, hmu]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
  simp only [map_mul, map_natCast, map_add, map_one]
  push_cast
  ring

theorem flagIntegral_C_mul (f N : ℕ) (x : ℚ) (Φ : RootRing f N) :
    flagIntegral f N (C x * Φ) = x * flagIntegral f N Φ := by
  simp only [flagIntegral, coeff_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  ring

theorem flagIntegral_add (f N : ℕ) (Φ Ψ : RootRing f N) :
    flagIntegral f N (Φ + Ψ) = flagIntegral f N Φ + flagIntegral f N Ψ := by
  simp only [flagIntegral, coeff_add, add_mul, Finset.sum_add_distrib]

theorem flagIntegral_zero (f N : ℕ) : flagIntegral f N 0 = 0 := by
  simp [flagIntegral]

end Rest

end

end Flag

open MvPolynomial

theorem FibreTranslationInvariance.intersectionNumber_baseChange : FibreTranslationInvariance.Statement := by
  classical
  intro f r a c τ
  constructor
  · have h := (Flag.derivation_restPolynomial f r a c
      (Flag.sumPderiv Finset.univ (yIndex f r a c τ)) (fun σ => if σ = τ then 1 else 0) (fun _ => 0)
      (fun σ i => by
        rw [Flag.sumPderiv_X]
        by_cases h : σ = τ
        · subst h
          rw [show (Finset.univ.filter fun l => yIndex f r a c σ l = yIndex f r a c σ i) = {i} by
            ext l; simp [Flag.yIndex_eq_yIndex_iff]]
          simp
        · rw [show (Finset.univ.filter fun l => yIndex f r a c τ l = yIndex f r a c σ i) = ∅ by
            ext l; simp [Flag.yIndex_eq_yIndex_iff, Ne.symm h]]
          simp [h])
      (fun σ i => by
        rw [Flag.sumPderiv_X]
        rw [show (Finset.univ.filter fun l => yIndex f r a c τ l = zIndex f r a c σ i) = ∅ by
          ext l; simp [Flag.yIndex_ne_zIndex]]
        simp)).1
    rw [Flag.sumPderiv_apply] at h
    exact h
  · have h := (Flag.derivation_restPolynomial f r a c
      (Flag.sumPderiv Finset.univ (zIndex f r a c τ)) (fun _ => 0) (fun σ => if σ = τ then 1 else 0)
      (fun σ i => by
        rw [Flag.sumPderiv_X]
        rw [show (Finset.univ.filter fun l => zIndex f r a c τ l = yIndex f r a c σ i) = ∅ by
          ext l
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          exact fun h => Flag.yIndex_ne_zIndex c σ τ i l h.symm]
        simp)
      (fun σ i => by
        rw [Flag.sumPderiv_X]
        by_cases h : σ = τ
        · subst h
          rw [show (Finset.univ.filter fun l => zIndex f r a c σ l = zIndex f r a c σ i) = {i} by
            ext l; simp [Flag.zIndex_eq_zIndex_iff]]
          simp
        · rw [show (Finset.univ.filter fun l => zIndex f r a c τ l = zIndex f r a c σ i) = ∅ by
            ext l; simp [Flag.zIndex_eq_zIndex_iff, Ne.symm h]]
          simp [h])).1
    rw [Flag.sumPderiv_apply] at h
    exact h

namespace Flag

open MvPolynomial Finset

theorem card_filter_pair {f N : ℕ} (s : Finset (Fin N)) (τ : Fin f) (v : Fin f × Fin N) :
    (s.filter fun i => ((τ, i) : Fin f × Fin N) = v).card = if v.1 = τ ∧ v.2 ∈ s then 1 else 0 := by
  rcases v with ⟨σ, j⟩
  by_cases h : σ = τ ∧ j ∈ s
  · obtain ⟨rfl, hj⟩ := h
    rw [if_pos ⟨rfl, hj⟩, Finset.card_eq_one]
    refine ⟨j, ?_⟩
    ext i
    simp only [Finset.mem_filter, Prod.mk.injEq, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro rfl; exact ⟨hj, rfl⟩
  · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi heq
    simp only [Prod.mk.injEq] at heq
    exact h ⟨heq.1.symm, heq.2 ▸ hi⟩

theorem sumPderiv_restPolynomial (f r a : ℕ) (c : SmallBlock) (τ : Fin f) (s : Finset (Fin (r + a)))
    (α β : Fin f → ℚ)
    (hy : ∀ σ i, (if (yIndex f r a c σ i).1 = τ ∧ (yIndex f r a c σ i).2 ∈ s then 1 else 0 : ℕ) =
      (α σ : ℚ))
    (hz : ∀ σ i, (if (zIndex f r a c σ i).1 = τ ∧ (zIndex f r a c σ i).2 ∈ s then 1 else 0 : ℕ) =
      (β σ : ℚ)) :
    ∑ i ∈ s, pderiv (τ, i) (restPolynomial f r a c) =
      C (((f * (r * a) + 1 : ℕ) : ℚ) * (c.sign * r * ∑ σ, α σ)) *
        (smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c) := by
  classical
  rw [← sumPderiv_apply s (fun i => ((τ, i) : Fin f × Fin (r + a)))]
  refine (derivation_restPolynomial f r a c _ α β (fun σ i => ?_) (fun σ i => ?_)).2
  · rw [sumPderiv_X, card_filter_pair, ← hy σ i]
  · rw [sumPderiv_X, card_filter_pair, ← hz σ i]

end Flag

theorem ShiftTotalValues.intersectionNumber_baseChange : ShiftTotalValues.Statement := by
  classical
  intro f r a τ
  have hsum : ∑ σ : Fin f, (if σ = τ then (1 : ℚ) else 0) = 1 := by simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [shiftFunctional, Flag.sumPderiv_restPolynomial f r a .last τ _ (fun _ => 0)
      (fun σ => if σ = τ then 1 else 0) (fun σ i => ?_) (fun σ i => ?_), Flag.flagIntegral_C_mul]
    · simp
    · rw [if_neg (by rintro ⟨-, hh⟩; have hh2 := (Finset.mem_filter.mp hh).2; simp [yIndex, SmallBlock.jIndex] at hh2)]; simp
    · by_cases h : σ = τ <;> simp [zIndex, SmallBlock.jIndex, Finset.mem_filter, h] <;> (try exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [SmallBlock.jIndex]⟩) <;> (try (rw [if_neg]; intro hh; have hh2 := (Finset.mem_filter.mp hh.2).2; simp [SmallBlock.jIndex] at hh2))
  · rw [totalFunctional, Flag.sumPderiv_restPolynomial f r a .last τ _
      (fun σ => if σ = τ then 1 else 0) (fun σ => if σ = τ then 1 else 0) (fun σ i => ?_)
      (fun σ i => ?_), Flag.flagIntegral_C_mul, hsum, fibreDegree]
    · simp [SmallBlock.sign]
    · by_cases h : σ = τ <;> simp [yIndex, h]
    · by_cases h : σ = τ <;> simp [zIndex, h]
  · rw [shiftFunctional, Flag.sumPderiv_restPolynomial f r a .first τ _
      (fun σ => if σ = τ then 1 else 0) (fun _ => 0) (fun σ i => ?_) (fun σ i => ?_),
      Flag.flagIntegral_C_mul, hsum, fibreDegree]
    · simp [SmallBlock.sign]
    · by_cases h : σ = τ <;> simp [yIndex, SmallBlock.jIndex, Finset.mem_filter, h] <;> (try exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [SmallBlock.jIndex]⟩) <;> (try (rw [if_neg]; intro hh; have hh2 := (Finset.mem_filter.mp hh.2).2; simp [SmallBlock.jIndex] at hh2))
    · rw [if_neg (by rintro ⟨-, hh⟩; have hh2 := (Finset.mem_filter.mp hh).2; simp [zIndex, SmallBlock.jIndex] at hh2)]; simp
  · rw [totalFunctional, Flag.sumPderiv_restPolynomial f r a .first τ _
      (fun σ => if σ = τ then 1 else 0) (fun σ => if σ = τ then 1 else 0) (fun σ i => ?_)
      (fun σ i => ?_), Flag.flagIntegral_C_mul, hsum, fibreDegree]
    · simp [SmallBlock.sign]
    · by_cases h : σ = τ <;> simp [yIndex, h]
    · by_cases h : σ = τ <;> simp [zIndex, h]

end RestTerms

end GroundTheory.Heights₂.Heights
