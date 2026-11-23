import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsZCombLimit
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsHilbert
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmAExpand
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreDim
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.Inter (famExt famExt_apply famExt_basis hermZpow hermLine_eq_of isSmoothHerm_tensor
  isSmoothHerm_hermZpow fam_update_eq_snoc fam_snoc_zpow)

noncomputable section

set_option linter.unusedSectionVars false

namespace ZCombLimit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem zcomb_eq_tensor_zpow (A B : HermLine ι) (m p : ℤ) :
    HermLine.zcomb A B m p = (hermZpow A m).tensor (hermZpow B p) :=
  hermLine_eq_of (by funext k; simp [HermLine.zcomb, HermLine.tensor, hermZpow])
    (by funext z; simp [HermLine.zcomb, HermLine.tensor, hermZpow])

theorem isSmoothHerm_zcomb_int {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (m p : ℤ) :
    IsSmoothHerm (HermLine.zcomb A B m p) := by
  rw [zcomb_eq_tensor_zpow]
  exact isSmoothHerm_tensor (isSmoothHerm_hermZpow hA m) (isSmoothHerm_hermZpow hB p)

theorem fam_update_zcomb_int {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)}
    {n : ℕ} (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (L : Fin (n + 1) → HermLine ι) (hL : ∀ j, IsSmoothHerm (L j)) (a : Fin (n + 1)) {A B : HermLine ι}
    (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (m p : ℤ) :
    I P (n + 1) (Function.update L a (HermLine.zcomb A B m p)) =
      m * I P (n + 1) (Function.update L a A) + p * I P (n + 1) (Function.update L a B) := by
  rw [zcomb_eq_tensor_zpow]
  have hAm := isSmoothHerm_hermZpow hA m
  have hBp := isSmoothHerm_hermZpow hB p
  have hR : ∀ i : Fin n, IsSmoothHerm ((fun i : Fin n => L (Equiv.swap a (Fin.last n) i.castSucc)) i) :=
    fun i => hL _
  rw [fam_update_eq_snoc hI hP L hL a (isSmoothHerm_tensor hAm hBp), fam_update_eq_snoc hI hP L hL a hA,
    fam_update_eq_snoc hI hP L hL a hB, hI.2.1 P n _ _ _ hP hR hAm hBp, fam_snoc_zpow hI hP _ hR hA m,
    fam_snoc_zpow hI hP _ hR hB p]

variable {J : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}

theorem eq_famExt_of_position (Q : HermLine ι → Prop) (e : Fin 2 → HermLine ι) (Z : HermLine ι) (w : Fin 2 → ℝ)
    (he : ∀ i, Q (e i)) (hZ : Q Z)
    (hposition : ∀ (L : Fin n → HermLine ι) (a : Fin n), (∀ j, Q (L j)) →
      J P n (Function.update L a Z) =
        w 0 * J P n (Function.update L a (e 0)) + w 1 * J P n (Function.update L a (e 1)))
    (T : Finset (Fin n)) (t : Fin n → Fin 2) :
    J P n (fun j => if j ∈ T then Z else e (t j)) =
      famExt J P n e (fun j => if j ∈ T then w else Pi.single (t j) 1) := by
  induction T using Finset.induction_on generalizing t with
  | empty =>
    simp only [Finset.notMem_empty, if_false]
    exact (famExt_basis e t).symm
  | insert a T ha ih =>
    have hins : ∀ {β : Type} (v : β) (F : Fin 2 → β),
        (fun j => if j ∈ insert a T then v else F (t j)) =
          Function.update (fun j => if j ∈ T then v else F (t j)) a v := by
      intro β v F
      funext j
      rcases eq_or_ne j a with rfl | h
      · simp
      · simp [h]
    have hupd : ∀ {β : Type} (v : β) (F : Fin 2 → β) (i : Fin 2),
        Function.update (fun j => if j ∈ T then v else F (t j)) a (F i) =
          fun j => if j ∈ T then v else F (Function.update t a i j) := by
      intro β v F i
      funext j
      rcases eq_or_ne j a with rfl | h
      · simp [ha]
      · simp [Function.update_of_ne h]
    have hQ : ∀ j, Q ((fun j => if j ∈ T then Z else e (t j)) j) := by
      intro j
      dsimp only
      split_ifs
      · exact hZ
      · exact he (t j)
    have eL : (fun j => if j ∈ insert a T then Z else e (t j)) =
        Function.update (fun j => if j ∈ T then Z else e (t j)) a Z :=
      hins Z e
    have eV : (fun j => if j ∈ insert a T then w else (Pi.single (t j) 1 : Fin 2 → ℝ)) =
        Function.update (fun j => if j ∈ T then w else (Pi.single (t j) 1 : Fin 2 → ℝ)) a w :=
      hins w fun i => Pi.single i 1
    have hL0 : Function.update (fun j => if j ∈ T then Z else e (t j)) a (e 0) =
        fun j => if j ∈ T then Z else e (Function.update t a 0 j) :=
      hupd Z e 0
    have hL1 : Function.update (fun j => if j ∈ T then Z else e (t j)) a (e 1) =
        fun j => if j ∈ T then Z else e (Function.update t a 1 j) :=
      hupd Z e 1
    have hV0 : Function.update (fun j => if j ∈ T then w else (Pi.single (t j) 1 : Fin 2 → ℝ)) a
        (Pi.single 0 1) = fun j => if j ∈ T then w else Pi.single (Function.update t a 0 j) 1 :=
      hupd w (fun i => Pi.single i 1) 0
    have hV1 : Function.update (fun j => if j ∈ T then w else (Pi.single (t j) 1 : Fin 2 → ℝ)) a
        (Pi.single 1 1) = fun j => if j ∈ T then w else Pi.single (Function.update t a 1 j) 1 :=
      hupd w (fun i => Pi.single i 1) 1
    have hw : w = w 0 • (Pi.single 0 1 : Fin 2 → ℝ) + w 1 • (Pi.single 1 1 : Fin 2 → ℝ) := by
      funext i
      fin_cases i <;> simp
    rw [eL, eV, hposition _ a hQ, hL0, hL1, ih, ih,
      congrArg (Function.update (fun j => if j ∈ T then w else (Pi.single (t j) 1 : Fin 2 → ℝ)) a) hw,
      MultilinearMap.map_update_add, MultilinearMap.map_update_smul, MultilinearMap.map_update_smul, hV0, hV1,
      smul_eq_mul, smul_eq_mul]

theorem famExt_const_smul (e : Fin 2 → HermLine ι) (c : ℝ) (w : Fin 2 → ℝ) :
    famExt J P n e (fun _ => c • w) = c ^ n * famExt J P n e (fun _ => w) := by
  rw [show (fun _ : Fin n => c • w) = fun i => (fun _ : Fin n => c) i • (fun _ : Fin n => w) i from rfl,
    MultilinearMap.map_smul_univ, smul_eq_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem exists_delta (e : Fin 2 → HermLine ι) (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      |famExt J P n e (fun _ => ![1 - k * t, t]) - J P n (fun _ => e 0)| < ε := by
  have hv : ∀ i : Fin 2, Continuous fun t : ℝ => (![1 - k * t, t] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      fun_prop
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      fun_prop
  have hg : Continuous fun t : ℝ => famExt J P n e (fun _ => ![1 - k * t, t]) := by
    simp only [famExt_apply]
    exact continuous_finsetSum _ fun s _ =>
      continuous_const.mul (continuous_finsetProd _ fun j _ => hv (s j))
  have h0 : famExt J P n e (fun _ => ![1 - k * (0 : ℝ), 0]) = J P n (fun _ => e 0) := by
    have e1 : (fun _ : Fin n => (![1 - k * (0 : ℝ), 0] : Fin 2 → ℝ)) =
        fun j => Pi.single ((fun _ => (0 : Fin 2)) j) 1 := by
      funext j i
      fin_cases i <;> simp
    rw [e1, famExt_basis]
    rfl
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuous_iff.mp hg 0 ε hε
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have := hδ' t (by simpa [Real.dist_eq] using ht)
  rwa [Real.dist_eq, h0] at this

theorem famExt_div (e : Fin 2 → HermLine ι) (k p q : ℕ) (hq : 0 < q) :
    famExt J P n e (fun _ => ![(((q : ℤ) - k * p : ℤ) : ℝ), ((p : ℤ) : ℝ)]) / (q : ℝ) ^ n =
      famExt J P n e (fun _ => ![1 - k * ((p : ℝ) / q), (p : ℝ) / q]) := by
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have hw : (![(((q : ℤ) - k * p : ℤ) : ℝ), ((p : ℤ) : ℝ)] : Fin 2 → ℝ) =
      (q : ℝ) • ![1 - k * ((p : ℝ) / q), (p : ℝ) / q] := by
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul]
      push_cast
      field_simp
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.smul_apply,
        smul_eq_mul, Int.cast_natCast]
      field_simp
  rw [hw, famExt_const_smul]
  field_simp

end ZCombLimit

open GroundTheory.Heights₂.Heights.NumbersDVR in

theorem ZCombLimit.genericFibre {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {d : ℕ} (hP : IsArithVar P (d + 1)) :
    GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime (P.map (MvPolynomial.map (Int.castRingHom ℚ))) ∧
      ringKrullDim (GroundTheory.Heights₂.Heights.NumbersDVR.MRing ι ℚ ⧸ P.map (MvPolynomial.map (Int.castRingHom ℚ))) =
        ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have : P.IsPrime := hPp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ P → m = 0 := by
    intro m hm
    have h1 : m ∈ P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) := hm
    rw [show P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hchar
  have hq : ReciprocityTheory.AnForm.R.extQ P = P.map (MvPolynomial.map (Int.castRingHom ℚ)) := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff]
    refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · rw [hq, hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · rw [hdim] at hform
    refine GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq (d + Fintype.card K) _ ?_
    rw [hform, show d + 1 + Fintype.card K = (d + Fintype.card K) + 1 by omega, Nat.cast_succ]

theorem ZCombLimit.proof (hM : MixedNumberPolynomial.Statement.{0}) : ZCombLimit.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D A B II k hII hY hA hB ε hε
  set P := mCoordIdeal y with hPdef
  have hI := hII K ι

  have hfullA : ∀ m p : ℤ, II K ι P (D + 1) (fun _ => HermLine.zcomb A B m p) =
      famExt (II K ι) P (D + 1) ![A, B] (fun _ => ![(m : ℝ), (p : ℝ)]) := by
    intro m p
    have h := ZCombLimit.eq_famExt_of_position (J := II K ι) (P := P) IsSmoothHerm ![A, B]
      (HermLine.zcomb A B m p) ![(m : ℝ), (p : ℝ)] (Fin.forall_fin_two.mpr ⟨hA, hB⟩)
      (ZCombLimit.isSmoothHerm_zcomb_int hA hB m p)
      (fun L a hL => by simpa using ZCombLimit.fam_update_zcomb_int hI hY L hL a hA hB m p)
      Finset.univ (fun _ => 0)
    simpa using h

  obtain ⟨-, hadd⟩ := hM ℚ K ι (P.map (MvPolynomial.map (Int.castRingHom ℚ))) D
    (ZCombLimit.genericFibre hY).1 (ZCombLimit.genericFibre hY).2
  let Jg : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ := fun P' n L =>
    (GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ (P'.map (MvPolynomial.map (Int.castRingHom ℚ)))
      (fun j => (L j).a) : ℝ)
  have hzs : ∀ (bs : Fin D → K → ℤ) (j : Fin D) (c : ℤ) (x : K → ℤ),
      GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ)))
          (Function.update bs j (c • x)) =
        c * GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ (P.map (MvPolynomial.map (Int.castRingHom ℚ)))
          (Function.update bs j x) := by
    intro bs j c x
    let φ : (K → ℤ) →+ ℤ := AddMonoidHom.mk' (fun x => GroundTheory.Heights₂.Heights.NumbersDVR.intNum ℚ
      (P.map (MvPolynomial.map (Int.castRingHom ℚ))) (Function.update bs j x)) (fun x y => hadd bs j x y)
    exact (map_zsmul φ c x).trans (smul_eq_mul _ _)
  have hfullG : ∀ m p : ℤ, (genDeg P D (HermLine.zcomb A B m p).a : ℝ) =
      famExt Jg P D ![A, B] (fun _ => ![(m : ℝ), (p : ℝ)]) := by
    intro m p
    have hposition : ∀ (L : Fin D → HermLine ι) (a : Fin D), (∀ _ : Fin D, True) →
        Jg P D (Function.update L a (HermLine.zcomb A B m p)) =
          (![(m : ℝ), (p : ℝ)] : Fin 2 → ℝ) 0 * Jg P D (Function.update L a (![A, B] 0)) +
            (![(m : ℝ), (p : ℝ)] : Fin 2 → ℝ) 1 * Jg P D (Function.update L a (![A, B] 1)) := by
      intro L a _
      have hcomp : ∀ Z : HermLine ι, (fun j => (Function.update L a Z j).a) =
          Function.update (fun j => (L j).a) a Z.a := by
        intro Z
        funext j
        rcases eq_or_ne j a with rfl | h
        · simp
        · simp [Function.update_of_ne h]
      simp only [Jg, hcomp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have ha : (HermLine.zcomb A B m p).a = m • A.a + p • B.a := rfl
      rw [ha, hadd, hzs, hzs]
      push_cast
      ring
    have h := ZCombLimit.eq_famExt_of_position (J := Jg) (P := P) (fun _ => True) ![A, B]
      (HermLine.zcomb A B m p) ![(m : ℝ), (p : ℝ)] (fun _ => trivial) trivial hposition Finset.univ (fun _ => 0)
    simpa [Jg, genDeg] using h
  obtain ⟨δ₁, hδ₁, h₁⟩ := ZCombLimit.exists_delta (J := II K ι) (P := P) (n := D + 1) ![A, B] k ε hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := ZCombLimit.exists_delta (J := Jg) (P := P) (n := D) ![A, B] k ε hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun p q hp hq hpq => ⟨?_, ?_⟩⟩
  · have ht : |(p : ℝ) / q| < δ₁ := by
      rw [abs_of_nonneg (by positivity)]
      exact hpq.trans_le (min_le_left _ _)
    have h := h₁ _ ht
    rw [← ZCombLimit.famExt_div ![A, B] k p q hq, ← hfullA] at h
    simpa using h
  · have ht : |(p : ℝ) / q| < δ₂ := by
      rw [abs_of_nonneg (by positivity)]
      exact hpq.trans_le (min_le_right _ _)
    have h := h₂ _ ht
    rw [← ZCombLimit.famExt_div ![A, B] k p q hq, ← hfullG] at h
    simpa [Jg, genDeg] using h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
