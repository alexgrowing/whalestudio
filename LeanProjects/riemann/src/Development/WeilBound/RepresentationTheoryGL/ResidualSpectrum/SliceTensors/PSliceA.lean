import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableParabolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliConstantTermVanishing

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.Reduction

namespace PositivityTheory.Rg.Rs.SliceClasses

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

set_option linter.unusedSectionVars false

theorem A_posIdele_one : posIdele (K := E) 1 one_pos = 1 := by
  unfold posIdele
  refine Finset.prod_eq_one fun w _ => ?_
  have : (⟨(1 : ℝ) ^ w.mult, pow_pos one_pos _⟩ : {r : ℝ // 0 < r}) = 1 := Subtype.ext (one_pow _)
  rw [this, map_one]

theorem A_diag_comm {n : ℕ} {R : Type*} [CommRing R] (d : Fin n → R) (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, M i j ≠ 0 → d i = d j) : diagonal d * M = M * diagonal d := by
  ext i j
  rw [diagonal_mul, mul_diagonal]
  by_cases hm : M i j = 0
  · simp [hm]
  · rw [h i j hm, mul_comm]

theorem A_tor_mul {n : ℕ} (x y : Fin n → ℝ) : An.tor E x * An.tor E y = An.tor E (x + y) := by
  unfold An.tor
  rw [← map_mul]
  congr 1
  funext i
  rw [Pi.mul_apply, posIdele_mul]
  congr 1
  simp [Real.exp_add]

theorem A_tor_zero {n : ℕ} : An.tor E (0 : Fin n → ℝ) = 1 := by
  unfold An.tor
  have e : (fun i : Fin n => posIdele (K := E) (Real.exp ((0 : Fin n → ℝ) i)) (Real.exp_pos _)) = 1 := by
    funext i
    have h1 : posIdele (K := E) (Real.exp ((0 : Fin n → ℝ) i)) (Real.exp_pos _) = posIdele (K := E) 1 one_pos := by
      congr 1; simp
    rw [h1, A_posIdele_one]
    rfl
  rw [e, map_one]

theorem A_aT_tor (N r : ℕ) (t : ℝ) : aT E N r t = An.tor E fun i : Fin N => if (i : ℕ) < r then t else 0 :=
  JDict.aT_eq N r t

theorem A_coe_tor {n : ℕ} (x : Fin n → ℝ) :
    ((An.tor E x : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E)) =
      diagonal fun i => ((posIdele (K := E) (Real.exp (x i)) (Real.exp_pos _) : (Ad E)ˣ) : Ad E) := rfl

theorem A_aT_comm {N r : ℕ} (t : ℝ) (g : GA E N)
    (h : ∀ i j, (g : Matrix (Fin N) (Fin N) (Ad E)) i j ≠ 0 → ((i : ℕ) < r ↔ (j : ℕ) < r)) :
    aT E N r t * g = g * aT E N r t := by
  rw [A_aT_tor]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, A_coe_tor]
  refine A_diag_comm _ _ fun i j hij => ?_
  have e : (if (i : ℕ) < r then t else 0) = (if (j : ℕ) < r then t else 0) := by
    by_cases hi : (i : ℕ) < r
    · rw [if_pos hi, if_pos ((h i j hij).1 hi)]
    · rw [if_neg hi, if_neg (fun hj => hi ((h i j hij).2 hj))]
  exact congrArg (fun x : ℝ => ((posIdele (K := E) (Real.exp x) (Real.exp_pos _) : (Ad E)ˣ) : Ad E)) e

theorem aT_add (N r : ℕ) (s t : ℝ) : aT E N r (s + t) = aT E N r s * aT E N r t := by
  rw [A_aT_tor, A_aT_tor, A_aT_tor, A_tor_mul]
  congr 1
  funext i
  simp only [Pi.add_apply]
  split_ifs <;> simp

theorem aT_zero (N r : ℕ) : aT E N r 0 = 1 := by
  rw [A_aT_tor, ← A_tor_zero (E := E) (n := N)]
  congr 1
  funext i
  simp

theorem aT_comm (N r r' : ℕ) (s t : ℝ) : aT E N r s * aT E N r' t = aT E N r' t * aT E N r s := by
  rw [A_aT_tor, A_aT_tor, A_tor_mul, A_tor_mul, add_comm]

theorem splitCentre_eq_aT (N : ℕ) (t : ℝ) : splitCentre E N t = aT E N N t := by
  rw [A_aT_tor, ← JDict.tor_const]
  congr 1
  funext i
  rw [if_pos i.2]

theorem A_stdSum_inl {r s : ℕ} (a : Fin r) : ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl a) : Fin (r + s)) : ℕ) = a := by
  simp [GlobalTheory.SmGL.stdSum]

theorem A_stdSum_inr {r s : ℕ} (b : Fin s) :
    ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr b) : Fin (r + s)) : ℕ) = r + b := by
  simp [GlobalTheory.SmGL.stdSum]

theorem A_lev_apply {R : Type} [CommRing R] {r s : ℕ} (m : GL (Fin r) R × GL (Fin s) R) (p q : Fin r ⊕ Fin s) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (GlobalTheory.SmGL.stdSum rfl p) (GlobalTheory.SmGL.stdSum rfl q) =
      fromBlocks (m.1 : Matrix (Fin r) (Fin r) R) 0 0 (m.2 : Matrix (Fin s) (Fin s) R) p q := by
  rw [CapStable.val_lev, CapStable.blockM, reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

theorem A_lev_tor {r s : ℕ} (x : Fin r → ℝ) (y : Fin s → ℝ) :
    lev (Ad E) r s (An.tor E x, An.tor E y) =
      An.tor E fun i : Fin (r + s) => if h : (i : ℕ) < r then x ⟨i, h⟩ else y ⟨i - r, by omega⟩ := by
  apply Units.ext
  ext i j
  obtain ⟨p, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨q, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  rw [A_lev_apply]
  have hinj := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).injective
  rcases p with a | b <;> rcases q with c | d
  · simp only [fromBlocks_apply₁₁, A_coe_tor, diagonal_apply, hinj.eq_iff, Sum.inl.injEq]
    by_cases h1 : a = c
    · subst h1
      have ha : ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl a) : Fin (r + s)) : ℕ) < r := by
        rw [A_stdSum_inl]; exact a.2
      rw [if_pos rfl, if_pos rfl, dif_pos ha]
      congr 3
    · rw [if_neg h1, if_neg h1]
  · simp [A_coe_tor, hinj.eq_iff]
  · simp [A_coe_tor, hinj.eq_iff]
  · simp only [fromBlocks_apply₂₂, A_coe_tor, diagonal_apply, hinj.eq_iff, Sum.inr.injEq]
    by_cases h1 : b = d
    · subst h1
      have hb : ¬ ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr b) : Fin (r + s)) : ℕ) < r := by
        rw [A_stdSum_inr]; omega
      rw [if_pos rfl, if_pos rfl, dif_neg hb]
      congr 3
      refine congrArg y (Fin.ext ?_)
      simp only [A_stdSum_inr]
      omega
    · rw [if_neg h1, if_neg h1]

theorem aT_comm_lev (r s : ℕ) (t : ℝ) (m : GA E r × GA E s) :
    aT E (r + s) r t * lev (Ad E) r s m = lev (Ad E) r s m * aT E (r + s) r t := by
  refine A_aT_comm t _ fun i j hij => ?_
  obtain ⟨p, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨q, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  rw [A_lev_apply] at hij
  rcases p with a | b <;> rcases q with c | d
  · rw [A_stdSum_inl, A_stdSum_inl]; exact iff_of_true a.2 c.2
  · exact absurd (by simp) hij
  · exact absurd (by simp) hij
  · rw [A_stdSum_inr, A_stdSum_inr]; exact iff_of_false (by omega) (by omega)

theorem lev_aT_left (r s r₁ : ℕ) (h : r₁ ≤ r) (t : ℝ) :
    lev (Ad E) r s (aT E r r₁ t, 1) = aT E (r + s) r₁ t := by
  rw [A_aT_tor, A_aT_tor, ← A_tor_zero (E := E) (n := s), A_lev_tor]
  congr 1
  funext i
  split_ifs <;> simp_all; omega

theorem lev_aT_right (r s r₂ : ℕ) (h : r₂ ≤ s) (t : ℝ) :
    lev (Ad E) r s (1, aT E s r₂ t) = aT E (r + s) (r + r₂) t * aT E (r + s) r (-t) := by
  rw [A_aT_tor, A_aT_tor, A_aT_tor, ← A_tor_zero (E := E) (n := r), A_lev_tor, A_tor_mul]
  congr 1
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  split_ifs <;> simp_all <;> omega

theorem A_unipGL_mul_diag {n r : ℕ} {R : Type*} [CommRing R] (d : Fin n → Rˣ) (X : UPos n r → R) :
    unipGL X * diagUnits n d = diagUnits n d * unipGL (fun p => ((d p.1.1)⁻¹ : Rˣ) * X p * d p.1.2) := by
  apply Units.ext
  simp only [Units.val_mul, coe_unipGL, coe_diagUnits, unipMatrix, add_mul, mul_add, one_mul, mul_one]
  congr 1
  ext i j
  rw [mul_diagonal, diagonal_mul, blockEntry_apply, blockEntry_apply]
  split_ifs
  · rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  · simp

theorem unip_mul_aT (N r : ℕ) (t : ℝ) (x : BlockIx N r → Ad E) :
    ∃ x' : BlockIx N r → Ad E, unip x * aT E N r t = aT E N r t * unip x' := by
  have h := A_unipGL_mul_diag (fun i : Fin N => posIdele (K := E) (Real.exp (if (i : ℕ) < r then t else 0))
    (Real.exp_pos _)) (r := r) x
  rw [GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip, GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip] at h
  exact ⟨_, by rw [A_aT_tor]; exact h⟩

theorem aT_comm_parGL {S : Finset ℕ} (N r r' : ℕ) (t : ℝ)
    (hS : ∀ q : PPos N S, ¬ IsTop r' q → ((q.1.1 : ℕ) < r ↔ (q.1.2 : ℕ) < r))
    (b : {q : PPos N S // ¬ IsTop r' q} → Ad E) :
    aT E N r t * parGL (joinPos (r := r') 0 b) = parGL (joinPos (r := r') 0 b) * aT E N r t := by
  refine A_aT_comm t _ fun i j hij => ?_
  by_cases hij' : i = j
  · rw [hij']
  rw [coe_parGL, parMatrix, Matrix.add_apply, Matrix.one_apply_ne hij', zero_add, parEntry_apply] at hij
  split_ifs at hij with h
  · rw [joinPos] at hij
    split_ifs at hij with ht
    · exact absurd rfl hij
    · exact hS _ ht
  · exact absurd rfl hij

theorem parabolic_position_left_bounds {r s r₁ : ℕ} (h : r₁ < r) (q : PPos (r + s) {r₁, r}) (hq : ¬ IsTop r q) :
    (q.1.1 : ℕ) < r₁ ∧ r₁ ≤ (q.1.2 : ℕ) ∧ (q.1.2 : ℕ) < r := by
  obtain ⟨s', hs', h1, h2⟩ := q.2
  have hq' : ¬ ((q.1.1 : ℕ) < r ∧ r ≤ (q.1.2 : ℕ)) := hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
  rcases hs' with rfl | rfl <;> omega

def eL (r s r₁ : ℕ) (h : r₁ < r) : UPos r r₁ ≃ {q : PPos (r + s) {r₁, r} // ¬ IsTop r q} where
  toFun p := ⟨⟨(Fin.castAdd s p.1.1, Fin.castAdd s p.1.2), r₁, by simp, by simpa using p.2.1, by simpa using p.2.2⟩,
    fun ht => by have := ht.2; simp at this; omega⟩
  invFun q := ⟨(⟨q.1.1.1, by have := parabolic_position_left_bounds h q.1 q.2; omega⟩, ⟨q.1.1.2, (parabolic_position_left_bounds h q.1 q.2).2.2⟩),
    (parabolic_position_left_bounds h q.1 q.2).1, (parabolic_position_left_bounds h q.1 q.2).2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem lev_unipGL_left (r s r₁ : ℕ) (h : r₁ < r) (A : UPos r r₁ → Ad E) :
    lev (Ad E) r s (unipGL A, 1) = parGL (joinPos (r := r) 0 fun q => A ((eL r s r₁ h).symm q)) := by
  apply Units.ext
  ext i j
  obtain ⟨p, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨q, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  have hinj := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).injective
  rw [A_lev_apply, coe_parGL, parMatrix, Matrix.add_apply, Matrix.one_apply, parEntry_apply]
  simp only [hinj.eq_iff]
  rcases p with a | b <;> rcases q with c | d
  · rw [fromBlocks_apply₁₁, coe_unipGL, unipMatrix, Matrix.add_apply, Matrix.one_apply, blockEntry_apply]
    simp only [Sum.inl.injEq]
    congr 1
    by_cases hb : (a : ℕ) < r₁ ∧ r₁ ≤ (c : ℕ)
    · have h' : ∃ s' ∈ ({r₁, r} : Finset ℕ), ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl a) : Fin (r + s)) : ℕ) < s' ∧
          s' ≤ ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl c) : Fin (r + s)) : ℕ) :=
        ⟨r₁, by simp, by rw [A_stdSum_inl]; exact hb.1, by rw [A_stdSum_inl]; exact hb.2⟩
      rw [dif_pos hb, dif_pos h', joinPos, dif_neg]
      · rfl
      · intro ht
        have := ht.2
        change r ≤ ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl c) : Fin (r + s)) : ℕ) at this
        rw [A_stdSum_inl] at this
        omega
    · rw [dif_neg hb, dif_neg]
      rintro ⟨s', hs', h1, h2⟩
      rw [A_stdSum_inl] at h1 h2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
      rcases hs' with rfl | rfl
      · exact hb ⟨h1, h2⟩
      · omega
  · rw [fromBlocks_apply₁₂]
    simp only [reduceCtorEq, if_false, Matrix.zero_apply, zero_add]
    split_ifs with h'
    · rw [joinPos, dif_pos]
      · rfl
      · change ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl a) : Fin (r + s)) : ℕ) < r ∧
          r ≤ ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr d) : Fin (r + s)) : ℕ)
        rw [A_stdSum_inl, A_stdSum_inr]
        omega
    · rfl
  · rw [fromBlocks_apply₂₁]
    simp only [reduceCtorEq, if_false, Matrix.zero_apply, zero_add]
    rw [dif_neg]
    rintro ⟨s', hs', h1, h2⟩
    rw [A_stdSum_inr, A_stdSum_inl] at *
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
    omega
  · rw [fromBlocks_apply₂₂]
    simp only [Sum.inr.injEq]
    rw [dif_neg, add_zero, Units.val_one, Matrix.one_apply]
    rintro ⟨s', hs', h1, h2⟩
    simp only [A_stdSum_inr] at h1 h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
    omega

theorem parabolic_position_right_bounds {r s r₂ : ℕ} (q : PPos (r + s) {r, r + r₂}) (hq : ¬ IsTop r q) :
    r ≤ (q.1.1 : ℕ) ∧ (q.1.1 : ℕ) < r + r₂ ∧ r + r₂ ≤ (q.1.2 : ℕ) := by
  obtain ⟨s', hs', h1, h2⟩ := q.2
  have hq' : ¬ ((q.1.1 : ℕ) < r ∧ r ≤ (q.1.2 : ℕ)) := hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
  rcases hs' with rfl | rfl <;> omega

def eR (r s r₂ : ℕ) (h : 0 < r₂) : UPos s r₂ ≃ {q : PPos (r + s) {r, r + r₂} // ¬ IsTop r q} where
  toFun p := ⟨⟨(Fin.natAdd r p.1.1, Fin.natAdd r p.1.2), r + r₂, by simp, by simp; omega, by simp; omega⟩,
    fun ht => by have := ht.1; simp at this⟩
  invFun q := ⟨(⟨q.1.1.1 - r, by have := parabolic_position_right_bounds q.1 q.2; omega⟩, ⟨q.1.1.2 - r, by have := parabolic_position_right_bounds q.1 q.2; omega⟩),
    by have := parabolic_position_right_bounds q.1 q.2; simp only; omega, by have := parabolic_position_right_bounds q.1 q.2; simp only; omega⟩
  left_inv p := Subtype.ext (Prod.ext (Fin.ext (by simp)) (Fin.ext (by simp)))
  right_inv q := by
    have := parabolic_position_right_bounds q.1 q.2
    exact Subtype.ext (Subtype.ext (Prod.ext (Fin.ext (by simp; omega)) (Fin.ext (by simp; omega))))

theorem lev_unipGL_right (r s r₂ : ℕ) (h : 0 < r₂) (A : UPos s r₂ → Ad E) :
    lev (Ad E) r s (1, unipGL A) = parGL (joinPos (r := r) 0 fun q => A ((eR r s r₂ h).symm q)) := by
  apply Units.ext
  ext i j
  obtain ⟨p, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨q, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  have hinj := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).injective
  rw [A_lev_apply, coe_parGL, parMatrix, Matrix.add_apply, Matrix.one_apply, parEntry_apply]
  simp only [hinj.eq_iff]
  rcases p with a | b <;> rcases q with c | d
  · rw [fromBlocks_apply₁₁]
    simp only [Sum.inl.injEq]
    rw [dif_neg, add_zero, Units.val_one, Matrix.one_apply]
    rintro ⟨s', hs', h1, h2⟩
    simp only [A_stdSum_inl] at h1 h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
    have := c.2
    omega
  · rw [fromBlocks_apply₁₂]
    simp only [reduceCtorEq, if_false, Matrix.zero_apply, zero_add]
    split_ifs with h'
    · rw [joinPos, dif_pos]
      · rfl
      · change ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl a) : Fin (r + s)) : ℕ) < r ∧
          r ≤ ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr d) : Fin (r + s)) : ℕ)
        rw [A_stdSum_inl, A_stdSum_inr]
        omega
    · rfl
  · rw [fromBlocks_apply₂₁]
    simp only [reduceCtorEq, if_false, Matrix.zero_apply, zero_add]
    rw [dif_neg]
    rintro ⟨s', hs', h1, h2⟩
    simp only [A_stdSum_inr, A_stdSum_inl] at h1 h2
    have := c.2
    omega
  · rw [fromBlocks_apply₂₂, coe_unipGL, unipMatrix, Matrix.add_apply, Matrix.one_apply, blockEntry_apply]
    simp only [Sum.inr.injEq]
    congr 1
    by_cases hb : (b : ℕ) < r₂ ∧ r₂ ≤ (d : ℕ)
    · have h' : ∃ s' ∈ ({r, r + r₂} : Finset ℕ), ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr b) : Fin (r + s)) : ℕ) < s' ∧
          s' ≤ ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr d) : Fin (r + s)) : ℕ) :=
        ⟨r + r₂, by simp, by rw [A_stdSum_inr]; omega, by rw [A_stdSum_inr]; omega⟩
      rw [dif_pos hb, dif_pos h', joinPos, dif_neg]
      · refine congrArg A (Subtype.ext (Prod.ext (Fin.ext ?_) (Fin.ext ?_))) <;> simp [eR, A_stdSum_inr]
      · intro ht
        have := ht.1
        change ((GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr b) : Fin (r + s)) : ℕ) < r at this
        rw [A_stdSum_inr] at this
        omega
    · rw [dif_neg hb, dif_neg]
      rintro ⟨s', hs', h1, h2⟩
      simp only [A_stdSum_inr] at h1 h2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs'
      rcases hs' with rfl | rfl
      · omega
      · exact hb ⟨by omega, by omega⟩

end PositivityTheory.Rg.Rs.SliceClasses

end
