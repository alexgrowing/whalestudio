import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullFormsGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullRatiosAlgebraic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCoordArithOfFnField
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GenericComplexPoint
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.FibreNormCharpolyFalse
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace PullFormsGeneric

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem aeval_mem (F : IntermediateField ℚ Ω) (w : (Σ k, ι k) → Ω) (hw : ∀ p, w p ∈ F) (f : MRing ι) :
    aeval w f ∈ F := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [aeval_C, algebraMap_int_eq, eq_intCast]; exact intCast_mem F a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p q hp => rw [map_mul, aeval_X]; exact mul_mem hp (hw q)

omit [CharZero Ω] in

theorem aeval_scale {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) (y : (Σ k, ι k) → Ω) (t : K → Ω) :
    aeval (fun p => y p * t p.1) g = aeval y g * ∏ k, t k ^ d k := by
  have h := congrArg (MvPolynomial.eval t) (ProjLine.mConeMap_eq_of_isMultiHomog y hg)
  rw [map_mul, eval_C, map_prod] at h
  simp only [map_pow, eval_X] at h
  rw [← h, mConeMap, aeval_def, aeval_def, eval₂_comp_left]
  congr 1
  · exact RingHom.ext_int _ _
  · funext p
    simp

theorem blockFnField_eq_top {y : (Σ k, ι k) → Ω} (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hB : Birational y) : blockFnField y = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hB x
  set t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
  have ht : ∏ k, t k ^ d k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (inv_ne_zero (hc k))
  have hw : ∀ p, y p * t p.1 ∈ blockFnField y := fun p =>
    IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, by simp [t, div_eq_mul_inv]⟩
  have hx : x = aeval (fun p => y p * t p.1) g / aeval (fun p => y p * t p.1) h := by
    rw [aeval_scale hg, aeval_scale hh, hgh, mul_div_mul_right _ _ ht, mul_div_cancel_right₀ _ hh0]
  rw [hx]
  exact div_mem (aeval_mem _ _ hw g) (aeval_mem _ _ hw h)

theorem trdeg_eq {y : (Σ k, ι k) → Ω} {D : ℕ} (hA : IsArithVar (mCoordIdeal y) (D + 1))
    (hB : Birational y) : Algebra.trdeg ℚ Ω = D := by
  obtain ⟨_, ⟨_, _, hrel⟩, _, hdim⟩ := hA
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hrel
  rw [CoordArithOfFnField.dim_eq y c hc] at hdim
  have h1 : (Algebra.trdeg ℤ (blockFnField y)).toENat = D := by
    generalize (Algebra.trdeg ℤ (blockFnField y)).toENat = n at hdim ⊢
    induction n using ENat.recTopCoe with
    | top =>
      exfalso
      simp only [top_add] at hdim
      norm_cast at hdim
    | coe n =>
      norm_cast at hdim ⊢
      omega
  rw [Cardinal.toENat_eq_natCast] at h1
  have hE : blockFnField y ≃ₐ[ℤ] Ω :=
    ((IntermediateField.equivOfEq (blockFnField_eq_top c hc hB)).trans
      IntermediateField.topEquiv).toRingEquiv.toIntAlgEquiv
  have h2 : Algebra.trdeg ℤ Ω = D := by rw [← hE.trdeg_eq]; convert h1
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  rw [← h2, ← trdeg_add_eq ℤ ℚ (A := Ω), trdeg_eq_zero (R := ℤ) (A := ℚ), zero_add]

omit [CharZero Ω] in

theorem exists_ne_zero {y : (Σ k, ι k) → Ω} {D : ℕ} {e : K → ℕ} {L : Fin (D + 1) → MRing ι}
    (hA : IsArithVar (mCoordIdeal y) (D + 1)) (hL : ∀ j, IsMultiHomog (L j) e)
    (hz : ∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) :
    ∃ j, aeval y (L j) ≠ 0 := by
  have hne : ¬ (⊤ : Ideal (MRing ι)) ≤ mCoordIdeal y := fun h =>
    (RingHom.ker_isPrime (mConeMap y)).ne_top (top_le_iff.mp h)
  obtain ⟨z, hzP, -⟩ := exists_mcPts_not_mem_mcPts hA hne
  obtain ⟨j, hj⟩ := hz z hzP
  refine ⟨j, fun h0 => hj (hzP.2 _ ?_)⟩
  change mConeMap y (L j) = 0
  rw [ProjLine.mConeMap_eq_of_isMultiHomog y (hL j), h0, map_zero, zero_mul]

def dehom {D : ℕ} (j₀ : Fin (D + 1)) (F : MvPolynomial (Fin (D + 1)) ℚ) : MvPolynomial {i // i ≠ j₀} ℚ :=
  bind₁ (fun i => if h : i = j₀ then 1 else X ⟨i, h⟩) F

omit [Field Ω] [CharZero Ω] in
theorem aeval_dehom {A : Type} [CommRing A] [Algebra ℚ A] {D : ℕ} (j₀ : Fin (D + 1))
    (F : MvPolynomial (Fin (D + 1)) ℚ) (u : {i // i ≠ j₀} → A) :
    aeval u (dehom j₀ F) = aeval (fun i => if h : i = j₀ then 1 else u ⟨i, h⟩) F := by
  rw [dehom, aeval_bind₁]
  refine congrArg (fun f => aeval f F) (funext fun i => ?_)
  split_ifs <;> simp

end PullFormsGeneric

open PullFormsGeneric in

theorem PullFormsGeneric.proof (hR : PullRatiosAlgebraic.Statement) : PullFormsGeneric.Statement := by
  intro K _ ι _ Ω _ _ y D e L hA hB he hL hz d F hF h0
  classical
  obtain ⟨j₀, hj₀⟩ := exists_ne_zero hA hL hz
  set a := aeval y (L j₀)
  set r : {i // i ≠ j₀} → Ω := fun i => aeval y (L i.1) / a

  have hP : pullField y L = IntermediateField.adjoin ℚ (Set.range r) := by
    have hw : ∀ i, aeval y (L i) / a ∈ IntermediateField.adjoin ℚ (Set.range r) := by
      intro i
      by_cases h : i = j₀
      · subst h; rw [div_self hj₀]; exact one_mem _
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨i, h⟩, rfl⟩
    apply le_antisymm
    · rw [pullField, IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, j, hj, rfl⟩
      rw [← div_div_div_cancel_right₀ hj₀]
      exact div_mem (hw i) (hw j)
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin _ _ ⟨i.1, j₀, hj₀, rfl⟩

  obtain ⟨_, ⟨_, _, hrel⟩, _, _⟩ := hA
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hrel
  have hrel' : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => ⟨c k, hc k⟩
  have halg : Algebra.IsAlgebraic (Algebra.adjoin ℚ (Set.range r)) Ω := by
    refine ⟨fun x => IntermediateField.isAlgebraic_adjoin_iff.mp ?_⟩
    have hle : blockFnField y ≤
        (algebraicClosure (IntermediateField.adjoin ℚ (Set.range r)) Ω).restrictScalars ℚ := by
      rw [blockFnField, IntermediateField.adjoin_le_iff]
      rintro _ ⟨p, q, hpq, rfl⟩
      refine (IntermediateField.mem_restrictScalars _).mpr (mem_algebraicClosure_iff.mpr ?_)
      have := hR K ι Ω y D e L hrel' he hL hz p q hpq
      rwa [hP] at this
    have hx := hle ((blockFnField_eq_top c hc hB).symm ▸ IntermediateField.mem_top : x ∈ blockFnField y)
    exact mem_algebraicClosure_iff.mp ((IntermediateField.mem_restrictScalars _).mp hx)

  have hcard : Cardinal.mk {i : Fin (D + 1) // i ≠ j₀} ≤ Algebra.trdeg ℚ Ω := by
    rw [trdeg_eq ⟨‹_›, ⟨‹_›, ‹_›, hrel⟩, ‹_›, ‹_›⟩ hB, Cardinal.mk_fintype]
    norm_cast
    simp [Fintype.card_subtype_compl]
  have hind : AlgebraicIndependent ℚ r :=
    (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℚ r hcard).1

  have hw : (fun i => if h : i = j₀ then (1 : Ω) else r ⟨i, h⟩) = fun i => aeval y (L i) / a := by
    funext i
    split_ifs with h
    · subst h; exact (div_self hj₀).symm
    · rfl
  have hr0 : aeval r (dehom j₀ F) = 0 := by
    rw [aeval_dehom, hw]
    have h1 := FibreNormCharpoly.aeval_mul_of_isHomogeneous hF a (fun i => aeval y (L i) / a)
    simp only [mul_div_cancel₀ _ hj₀] at h1
    rw [h0] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero _ hj₀)
  have hG : dehom j₀ F = 0 := hind.eq_zero_of_aeval_eq_zero _ hr0

  have hFX : F * X j₀ = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [map_mul, eval_X, map_zero]
    by_cases hx : x j₀ = 0
    · rw [hx, mul_zero]
    · have h1 := FibreNormCharpoly.aeval_mul_of_isHomogeneous (Ω := ℚ) hF (x j₀) (fun i => x i / x j₀)
      have h2 := aeval_dehom j₀ F (fun i => x i.1 / x j₀)
      have hw' : (fun i => if h : i = j₀ then (1 : ℚ) else x i / x j₀) = fun i => x i / x j₀ := by
        funext i
        split_ifs with h
        · subst h; exact (div_self hx).symm
        · rfl
      rw [hG, map_zero, hw'] at h2
      have e1 : eval x F = x j₀ ^ d * eval (fun i => x i / x j₀) F := by
        have hs : (fun j => x j₀ * (x j / x j₀)) = x := funext fun j => mul_div_cancel₀ _ hx
        rw [hs] at h1
        rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval]
        exact h1
      have e2 : eval (fun i => x i / x j₀) F = 0 := by
        rw [← coe_aeval_eq_eval]
        exact h2.symm
      rw [e1, e2, mul_zero, zero_mul]
  exact (mul_eq_zero.mp hFX).resolve_right (X_ne_zero _)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
