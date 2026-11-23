import Mathlib

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}

theorem det_map_algebraMap {X : Type} [Fintype X] [DecidableEq X] (M : Matrix X X R) :
    (M.map (algebraMap R C)).det = algebraMap R C M.det := by
  rw [RingHom.map_det]
  rfl

theorem eq_one_of_le_one_of_mul_eq_one {a b : NNReal} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) :
    a = 1 := by
  have h1 := mul_le_of_le_one_right (zero_le : (0 : NNReal) ≤ a) hb
  rw [h] at h1
  exact le_antisymm ha h1

private lemma cols_mul_lemma {X : Type} [Fintype X] [DecidableEq X] {P Q : Matrix X X C}
    (h : Submodule.span R (Set.range fun j x => Q x j) ≤
      Submodule.span R (Set.range fun j x => P x j)) :
    ∃ A : Matrix X X R, Q = P * A.map (algebraMap R C) := by
  have hc : ∀ j, ∃ c : X → R, ∑ i, c i • (fun x => P x i) = fun x => Q x j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (h (Submodule.subset_span ⟨j, rfl⟩))
  choose c hc using hc
  refine ⟨Matrix.of fun i j => c j i, ?_⟩
  ext x j
  have hx := congrFun (hc j) x
  simp only [Finset.sum_apply, Pi.smul_apply] at hx
  rw [Matrix.mul_apply, ← hx]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Algebra.smul_def, mul_comm]

theorem valuation_det_eq_of_span_eq_alt (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    {P Q : Matrix X X C} (hP : IsUnit P.det)
    (h : Submodule.span R (Set.range fun j x => P x j) =
      Submodule.span R (Set.range fun j x => Q x j)) :
    v Q.det = v P.det := by
  obtain ⟨A, hA⟩ := cols_mul_lemma (R := R) h.ge
  obtain ⟨B, hB⟩ := cols_mul_lemma (R := R) h.le
  have hdQ : Q.det = P.det * algebraMap R C A.det := by
    rw [hA, Matrix.det_mul, det_map_algebraMap]
  have hdP : P.det = Q.det * algebraMap R C B.det := by
    rw [hB, Matrix.det_mul, det_map_algebraMap]
  have hAB : algebraMap R C A.det * algebraMap R C B.det = 1 := by
    refine mul_left_cancel₀ hP.ne_zero ?_
    calc P.det * (algebraMap R C A.det * algebraMap R C B.det)
        = P.det * algebraMap R C A.det * algebraMap R C B.det := (mul_assoc _ _ _).symm
      _ = P.det := by rw [← hdQ, ← hdP]
      _ = P.det * 1 := (mul_one _).symm
  have hvA : v (algebraMap R C A.det) = 1 :=
    eq_one_of_le_one_of_mul_eq_one (hv.map_le_one _) (hv.map_le_one _)
      (by rw [← map_mul v, hAB, map_one])
  rw [hdQ, map_mul, hvA, mul_one]

theorem exists_matrix_span_eq (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (M : Submodule R (X → C)) (hfg : M.FG)
    (hsp : Submodule.span C (M : Set (X → C)) = ⊤) :
    ∃ β : Matrix X X C, IsUnit β.det ∧ M = Submodule.span R (Set.range fun j x => β x j) := by
  classical
  obtain ⟨S, rfl⟩ := hfg
  rw [Submodule.span_span_of_tower] at hsp
  suffices key : ∀ (n : ℕ) (S : Finset (X → C)), S.card = n →
      Submodule.span C (↑S : Set (X → C)) = ⊤ →
      ∃ β : Matrix X X C, IsUnit β.det ∧
        Submodule.span R (↑S : Set (X → C)) = Submodule.span R (Set.range fun j x => β x j) from
    key _ S rfl hsp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hn hspC
  by_cases hli : LinearIndependent C (fun i : S => (i : X → C))
  · have hb := Module.Basis.mk hli (by simpa using hspC.ge)
    let e : X ≃ S := (hb.indexEquiv (Pi.basisFun C X)).symm
    refine ⟨Matrix.of fun x j => ((e j : S) : X → C) x, ?_, ?_⟩
    · refine (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 ?_)
      exact hli.comp e e.injective
    · congr 1
      ext f
      constructor
      · intro hf
        exact ⟨e.symm ⟨f, hf⟩, by ext x; simp⟩
      · rintro ⟨j, rfl⟩
        exact (e j).2
  · obtain ⟨g, hg, i1, hi1⟩ := Fintype.not_linearIndependent_iff.1 hli
    obtain ⟨i0, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => v (g i))
      ⟨i1, Finset.mem_univ _⟩
    have hg0 : g i0 ≠ 0 := by
      intro h0
      have h2 := hmax i1 (Finset.mem_univ _)
      rw [h0, map_zero] at h2
      exact hi1 ((Valuation.zero_iff v).1 (le_antisymm h2 zero_le))
    have key : (i0 : X → C) =
        ∑ i ∈ Finset.univ.erase i0, (-(g i * (g i0)⁻¹)) • (i : X → C) := by
      have h1 := Finset.add_sum_erase Finset.univ (fun i => g i • (i : X → C)) (Finset.mem_univ i0)
      rw [hg] at h1
      have h2 : g i0 • (i0 : X → C) = -∑ i ∈ Finset.univ.erase i0, g i • (i : X → C) :=
        eq_neg_of_add_eq_zero_left h1
      calc (i0 : X → C) = (g i0)⁻¹ • (g i0 • (i0 : X → C)) := by
            rw [smul_smul, inv_mul_cancel₀ hg0, one_smul]
        _ = _ := by
          rw [h2, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, neg_smul, mul_comm]
    have hle1 : ∀ i, v (-(g i * (g i0)⁻¹)) ≤ 1 := by
      intro i
      rw [Valuation.map_neg, map_mul, map_inv₀]
      calc v (g i) * (v (g i0))⁻¹ ≤ v (g i0) * (v (g i0))⁻¹ :=
            mul_le_mul_of_nonneg_right (hmax i (Finset.mem_univ _)) zero_le
        _ = 1 := mul_inv_cancel₀ ((Valuation.ne_zero_iff v).2 hg0)
    choose r hr using fun i => hv.exists_of_le_one (hle1 i)
    have hx0R : (i0 : X → C) ∈ Submodule.span R (↑(S.erase (i0 : X → C)) : Set (X → C)) := by
      have hsum : (∑ i ∈ Finset.univ.erase i0, (-(g i * (g i0)⁻¹)) • (i : X → C)) ∈
          Submodule.span R (↑(S.erase (i0 : X → C)) : Set (X → C)) := by
        refine Submodule.sum_mem _ fun i hi => ?_
        rw [← hr i, algebraMap_smul]
        refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
        exact Finset.mem_coe.2 (Finset.mem_erase.2
          ⟨fun h => (Finset.mem_erase.1 hi).1 (Subtype.ext h), i.2⟩)
      rw [← key] at hsum
      exact hsum
    have hx0C : (i0 : X → C) ∈ Submodule.span C (↑(S.erase (i0 : X → C)) : Set (X → C)) :=
      Submodule.span_le_restrictScalars R C _ hx0R
    have hS : (↑S : Set (X → C)) = insert (i0 : X → C) ↑(S.erase (i0 : X → C)) := by
      rw [← Finset.coe_insert, Finset.insert_erase i0.2]
    have hspR : Submodule.span R (↑S : Set (X → C)) =
        Submodule.span R (↑(S.erase (i0 : X → C)) : Set (X → C)) := by
      rw [hS, Submodule.span_insert_eq_span hx0R]
    have hspC' : Submodule.span C (↑(S.erase (i0 : X → C)) : Set (X → C)) = ⊤ := by
      rw [← hspC, hS, Submodule.span_insert_eq_span hx0C]
    obtain ⟨β, hβ, hβS⟩ := ih _ (by rw [← hn]; exact Finset.card_erase_lt_of_mem i0.2)
      (S.erase (i0 : X → C)) rfl hspC'
    exact ⟨β, hβ, hspR.trans hβS⟩

private lemma cols_le_lemma_2 {X : Type} [Fintype X] [DecidableEq X] {P Q : Matrix X X C}
    (A : Matrix X X R) (hA : Q = P * A.map (algebraMap R C)) :
    Submodule.span R (Set.range fun j x => Q x j) ≤
      Submodule.span R (Set.range fun j x => P x j) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have hcol : (fun x => Q x j) = ∑ i, A i j • fun x => P x i := by
    ext x
    simp [hA, Matrix.mul_apply, Finset.sum_apply, Algebra.smul_def, mul_comm]
  show (fun x => Q x j) ∈ Submodule.span R _
  rw [hcol]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem inv_mem_of_valuation_eq_one (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (A : Submodule R (X → C)) (P : Matrix X X C) (hP : IsUnit P.det)
    (hA : A = Submodule.span R (Set.range fun j x => P x j))
    (one : (1 : X → C) ∈ A) (mul : ∀ f g, f ∈ A → g ∈ A → f * g ∈ A)
    (u : X → C) (hu : u ∈ A) (hunit : ∀ x, v (u x) = 1) : u⁻¹ ∈ A := by
  have hu0 : ∀ x, u x ≠ 0 := fun x h0 => by simpa [h0] using hunit x
  have hPA : ∀ j, (fun x => P x j) ∈ A := fun j => by
    rw [hA]; exact Submodule.subset_span ⟨j, rfl⟩
  have hcolD : ∀ j, (fun x => (Matrix.diagonal u * P) x j) = u * fun x => P x j := by
    intro j; ext x; simp [Matrix.diagonal_mul]
  have hDle : Submodule.span R (Set.range fun j x => (Matrix.diagonal u * P) x j) ≤
      Submodule.span R (Set.range fun j x => P x j) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show (fun x => (Matrix.diagonal u * P) x j) ∈ Submodule.span R _
    rw [hcolD, ← hA]
    exact mul u _ hu (hPA j)
  obtain ⟨T, hT⟩ := cols_mul_lemma hDle
  have hdT : algebraMap R C T.det = ∏ x, u x := by
    have e := congrArg Matrix.det hT
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, det_map_algebraMap] at e
    exact mul_left_cancel₀ hP.ne_zero (by rw [← e]; ring)
  have hvT : v (algebraMap R C T.det) = 1 := by
    rw [hdT, map_prod]
    exact Finset.prod_eq_one fun x _ => hunit x
  have hy : algebraMap R C T.det ≠ 0 := by
    rw [hdT]; exact Finset.prod_ne_zero_iff.2 fun x _ => hu0 x
  obtain ⟨s, hs⟩ := hv.exists_of_le_one
    (show v (algebraMap R C T.det)⁻¹ ≤ 1 from le_of_eq (by rw [map_inv₀, hvT, inv_one]))
  have hTs : T.det * s = 1 := hv.hom_inj (by rw [map_mul, hs, mul_inv_cancel₀ hy, map_one])
  have hTu : IsUnit T.det := ⟨⟨T.det, s, hTs, by rw [mul_comm]; exact hTs⟩, rfl⟩
  have hPD : P = (Matrix.diagonal u * P) * (T⁻¹).map (algebraMap R C) := by
    rw [hT, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv T hTu]
    simp
  have hPle := cols_le_lemma_2 _ hPD
  have hmem : (1 : X → C) ∈
      Submodule.span R (Set.range fun j x => (Matrix.diagonal u * P) x j) :=
    hPle (by rw [← hA]; exact one)
  have hle : Submodule.span R (Set.range fun j x => (Matrix.diagonal u * P) x j) ≤
      A.comap (LinearMap.mulLeft R u⁻¹) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    convert hPA j using 1
    ext x
    simp [Matrix.diagonal_mul, hu0 x]
  simpa using hle hmem

theorem isUnit_det_of_span_eq (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    {P Q : Matrix X X C} (hP : IsUnit P.det)
    (h : Submodule.span R (Set.range fun j x => P x j) =
      Submodule.span R (Set.range fun j x => Q x j)) : IsUnit Q.det := by
  have hvQ := valuation_det_eq_of_span_eq_alt hv hP h
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, map_zero] at hvQ
  exact (Valuation.ne_zero_iff v).2 hP.ne_zero hvQ.symm

end ReciprocityTheory.PGsh.L2
