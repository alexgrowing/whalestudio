import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFrameClassProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardUniCosetsLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorsProdDenominatorUnitriangularFactorsStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.IntClsCount

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

omit [TopologicalSpace E] in
theorem uni_mul {N : ℕ} {A B : Matrix (Fin N) (Fin N) E} (hA : IsUni A) (hB : IsUni B) :
    IsUni (A * B) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · rw [hA.1 i l h, zero_mul]
    · rw [hB.1 l j (lt_of_lt_of_le hij h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.2, hB.2, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hA.1 i l h, zero_mul]
      · rw [hB.1 l i h, mul_zero]
    · simp

theorem int_mul (L : LocE F E) {N : ℕ} {A B : Matrix (Fin N) (Fin N) E} (hA : IsIntM L A)
    (hB : IsIntM L B) : IsIntM L (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact L.O.sum_mem fun l _ => L.O.mul_mem (hA i l) (hB l j)

theorem det_mem (L : LocE F E) {N : ℕ} {A : Matrix (Fin N) (Fin N) E} (hA : IsIntM L A) :
    A.det ∈ L.O := by
  rw [Matrix.det_apply']
  exact L.O.sum_mem fun σ _ => L.O.mul_mem (intCast_mem _ _) (L.O.prod_mem fun i _ => hA _ _)

theorem exists_inv (L : LocE F E) {N : ℕ} {A : Matrix (Fin N) (Fin N) E} (hA : IsUni A)
    (hI : IsIntM L A) : ∃ B, IsUni B ∧ IsIntM L B ∧ A * B = 1 ∧ B * A = 1 := by
  have ht : A.BlockTriangular id := fun i j h => hA.1 i j h
  have hd : A.det = 1 := by
    rw [Matrix.det_of_upperTriangular ht]; simp [hA.2]
  have hu : IsUnit A.det := by rw [hd]; exact isUnit_one
  letI := A.invertibleOfIsUnitDet hu
  have hti : A⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular ht
  have h1 : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hu
  refine ⟨A⁻¹, ⟨fun i j h => hti h, fun i => ?_⟩, fun i j => ?_, h1, Matrix.nonsing_inv_mul A hu⟩
  · have h2 := congrFun (congrFun h1 i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hA.2, one_mul, Matrix.one_apply_eq] at h2
    · exact h2
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hA.1 i l h, zero_mul]
      · rw [hti (show id i < id l from h), mul_zero]
    · simp
  · rw [Matrix.inv_def, hd, Ring.inverse_one, one_smul, Matrix.adjugate_apply]
    refine det_mem L fun a b => ?_
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]
      split_ifs
      · exact L.O.one_mem
      · exact L.O.zero_mem
    · exact hI a b

theorem exists_reps (L : LocE F E) (t : E) (m : ℕ) (hm : m ≠ 0)
    (hc : Nat.card (L.O ⧸ Ideal.span {y : L.O | (y : E) = t}) = m) (N : ℕ) :
    ∃ R : Set (Matrix (Fin N) (Fin N) E), R.encard ≤ ((m ^ (N * (N - 1) / 2) : ℕ) : ℕ∞) ∧
      (∀ B ∈ R, IsUni B ∧ IsIntM L B) ∧
      ∀ B, IsUni B → IsIntM L B → ∃ B₀ ∈ R, ∀ i j, ∃ c ∈ L.O, B i j - B₀ i j = t * c := by
  set I : Ideal L.O := Ideal.span {y : L.O | (y : E) = t} with hI
  haveI : Finite (L.O ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hm)
  have hmem : ∀ y ∈ I, ∃ c ∈ L.O, (y : E) = t * c := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => exact ⟨1, L.O.one_mem, by rw [mul_one]; exact hx⟩
    | zero => exact ⟨0, L.O.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, e⟩ := hx
      obtain ⟨d, hd, e'⟩ := hy
      exact ⟨c + d, L.O.add_mem hc hd, by push_cast; rw [e, e', mul_add]⟩
    | smul a x _ hx =>
      obtain ⟨c, hc, e⟩ := hx
      exact ⟨a * c, L.O.mul_mem a.2 hc, by rw [smul_eq_mul]; push_cast; rw [e]; ring⟩
  let lift : ((j : Fin N) → Fin j → L.O ⧸ I) → Matrix (Fin N) (Fin N) E := fun x i j =>
    if h : i < j then ((x j ⟨i, h⟩).out : L.O) else if i = j then 1 else 0
  refine ⟨Set.range lift, ?_, ?_, ?_⟩
  · rw [← Set.image_univ]
    refine (Set.encard_image_le _ _).trans (le_of_eq ?_)
    rw [Set.encard_univ, ENat.card_eq_coe_natCard]
    congr 1
    rw [Nat.card_pi]
    simp only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin, hc]
    rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun j => j) N, Finset.sum_range_id]
  · rintro _ ⟨x, rfl⟩
    refine ⟨⟨fun i j h => ?_, fun i => ?_⟩, fun i j => ?_⟩
    · simp only [lift]
      rw [dif_neg (not_lt_of_gt h), if_neg (ne_of_gt h)]
    · simp [lift]
    · simp only [lift]
      split_ifs
      · exact Subtype.property _
      · exact L.O.one_mem
      · exact L.O.zero_mem
  · intro B hB hBI
    refine ⟨_, ⟨fun j i => Ideal.Quotient.mk I ⟨B ⟨i, i.2.trans j.2⟩ j, hBI _ _⟩, rfl⟩,
      fun i j => ?_⟩
    simp only [lift]
    split_ifs with h1 h2
    · have h3 : (⟨B i j, hBI i j⟩ : L.O) - (Ideal.Quotient.mk I ⟨B i j, hBI i j⟩).out ∈ I := by
        rw [← Ideal.Quotient.eq]
        exact (Quotient.out_eq _).symm
      exact hmem _ h3
    · subst h2
      exact ⟨0, L.O.zero_mem, by rw [hB.2]; simp⟩
    · exact ⟨0, L.O.zero_mem, by rw [hB.1 i j (lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2))]; simp⟩

omit [TopologicalSpace E] in
theorem rmul_mul {n N : ℕ} (x : Fin N → Fin n → E) (A B : Matrix (Fin N) (Fin N) E) (j : Fin N) :
    ∑ i, (A * B) i j • x i = ∑ l, B l j • ∑ i, A i l • x i := by
  simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem pairing (L : LocE F E) {r k : ℕ} (S : Frames L r k)
    (u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a b : Fin (r + 1)) :
    (cT L u * S.Zh * u') a b = S.h (∑ i, u' i b • S.f' i) (∑ i, u i a • S.f i) := by
  have h1 : ∀ (y : S.V) (c : Fin (r + 1) → E) (x : Fin (r + 1) → S.V),
      S.h (∑ i, c i • x i) y = ∑ i, c i * S.h (x i) y := by
    intro y c x
    simp only [Frames.h, hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    simp only [mul_assoc]
  have h2 : ∀ (y : S.V) (c : Fin (r + 1) → E) (x : Fin (r + 1) → S.V),
      S.h y (∑ i, c i • x i) = ∑ i, L.cj (c i) * S.h y (x i) := by
    intro y c x
    simp only [Frames.h, hf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
      Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  rw [h1]
  simp only [h2, Matrix.mul_apply, cT, Frames.Zh, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

def coset (L : LocE F E) {N : ℕ} (u : Matrix (Fin N) (Fin N) E) : Set (Matrix (Fin N) (Fin N) E) :=
  {v | ∃ A, IsUni A ∧ IsIntM L A ∧ v = u * A}

theorem exists_section (L : LocE F E) (N : ℕ) :
    ∃ s : Set (Matrix (Fin N) (Fin N) E) → Matrix (Fin N) (Fin N) E,
      ∀ u, ∃ A, IsUni A ∧ IsIntM L A ∧ u = s (coset L u) * A := by
  refine ⟨fun C => if h : ∃ u, C = coset L u then h.choose else 0, fun u => ?_⟩
  have h : ∃ v, coset L u = coset L v := ⟨u, rfl⟩
  simp only [dif_pos h]
  have h1 : u ∈ coset L u := by
    refine ⟨1, ⟨fun i j hij => Matrix.one_apply_ne (ne_of_gt hij), fun i => Matrix.one_apply_eq i⟩,
      fun i j => ?_, (mul_one u).symm⟩
    rw [Matrix.one_apply]
    split_ifs
    · exact L.O.one_mem
    · exact L.O.zero_mem
  exact h.choose_spec.subset h1

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 0 ≤ S.vD → ({C : Set S.FrP | S.IsIntCls C ∧ ∃ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni u ∧ IsUni u' ∧ (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = true → u i j ∈ L.O) ∧ C = S.frameCls (fun j => ∑ i, u i j • S.f i) fun j => ∑ i, u' i j • S.f' i}.encard : ℝ≥0∞) ≤ (S.q : ℝ≥0∞) ^ (r * (r + 1) * (S.vth + S.vD).toNat) := by
  intro F _ _ _ _ _ E _ _ _ L r k S hvD
  obtain ⟨-, -, -, -, -, hcard, hq, -⟩ := GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr
  have hth : S.th = (S.ϖ : F) ^ S.vth.toNat := by
    unfold Frames.th Frames.vth; split_ifs <;> simp
  have hv0 : 0 ≤ S.vth := by unfold Frames.vth; split_ifs <;> simp
  obtain ⟨R, hR, hRu, hRs⟩ := exists_reps L (algebraMap F E S.th) (resQ S.ϖ ^ (2 * S.vth.toNat))
    (pow_ne_zero _ (by omega)) (by rw [hth]; exact hcard _) (r + 1)
  obtain ⟨s, hs⟩ := exists_section L (r + 1)
  set T := {C : Set S.FrP | S.IsIntCls C ∧ ∃ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni u ∧ IsUni u' ∧ (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = true → u i j ∈ L.O) ∧ C = S.frameCls (fun j => ∑ i, u i j • S.f i) fun j => ∑ i, u' i j • S.f' i} with hT
  rcases T.eq_empty_or_nonempty with h0 | ⟨C₀, hC₀⟩
  · rw [h0]; simp
  set Δ : E := ∏ l : Fin (r + 2), (if S.D l ≠ 0 then S.D l else 1) with hΔ
  have hden : ∀ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni u → IsUni u' →
      (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = true → u i j ∈ L.O) →
      S.IsIntCls (S.frameCls (fun j => ∑ i, u i j • S.f i) fun j => ∑ i, u' i j • S.f' i) →
      Δ ∈ L.O ∧ IsUnit Δ ∧ vE L S.ϖ (Δ * L.cj Δ) = S.vD ∧
        ∀ i j, L.cj Δ * u i j ∈ L.O ∧ Δ * u' i j ∈ L.O := by
    intro u u' hu hu' hb hint
    refine GlobalTheory.T.leadingMinors_prod_denominator_unitriangular_factors L r k S u u' hu hu' hb (fun a b => ?_) Δ hΔ
    rw [pairing]
    exact hint.2 _ (GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).1 a b
  obtain ⟨hΔO, hΔu, hΔv⟩ : Δ ∈ L.O ∧ IsUnit Δ ∧ vE L S.ϖ (Δ * L.cj Δ) = S.vD := by
    obtain ⟨hi, u, u', hu, hu', hb, rfl⟩ := hC₀
    obtain ⟨a, b, c, -⟩ := hden u u' hu hu' hb hi
    exact ⟨a, b, c⟩
  have hcjO : L.cj Δ ∈ L.O := ((GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.1 Δ hΔO).1
  have c1 := GlobalTheory.HL.encard_uniCosets_le L S.ϖ S.ϖ_irr (L.cj Δ) hcjO (hΔu.map L.cj) (r + 1)
  have c2 := GlobalTheory.HL.encard_uniCosets_le L S.ϖ S.ϖ_irr Δ hΔO hΔu (r + 1)
  rw [L.cj_cj, mul_comm (L.cj Δ) Δ, hΔv] at c1
  rw [hΔv] at c2
  set S₁ := {C : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E) | ∃ u, IsUni u ∧ (∀ i j, L.cj Δ * u i j ∈ L.O) ∧ C = {v | ∃ A, IsUni A ∧ IsIntM L A ∧ v = u * A}} with hS₁
  set S₂ := {C : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E) | ∃ u, IsUni u ∧ (∀ i j, Δ * u i j ∈ L.O) ∧ C = {v | ∃ A, IsUni A ∧ IsIntM L A ∧ v = u * A}} with hS₂
  have hsub : T ⊆ (fun p => S.frameCls (fun j => ∑ i, s p.1 i j • S.f i)
      fun j => ∑ i, (s p.2.1 * p.2.2) i j • S.f' i) '' (S₁ ×ˢ S₂ ×ˢ R) := by
    rintro C ⟨hi, u, u', hu, hu', hb, rfl⟩
    obtain ⟨-, -, -, hd⟩ := hden u u' hu hu' hb hi
    obtain ⟨A, hA, hAI, eA⟩ := hs u
    obtain ⟨A', hA', hAI', eA'⟩ := hs u'
    obtain ⟨Ai, hAi, hAiI, -, e2⟩ := exists_inv L hA hAI
    obtain ⟨B₀, hB₀, hcong⟩ := hRs (A' * Ai) (uni_mul hA' hAi) (int_mul L hAI' hAiI)
    obtain ⟨Bi, hBi, hBiI, e3, e4⟩ := exists_inv L (hRu B₀ hB₀).1 (hRu B₀ hB₀).2
    refine ⟨(coset L u, coset L u', B₀), ⟨⟨u, hu, fun i j => (hd i j).1, rfl⟩,
      ⟨u', hu', fun i j => (hd i j).2, rfl⟩, hB₀⟩, ?_⟩
    refine (((GlobalTheory.HL.FrameClass.frame_classes L r k S _ _).2.1
      (fun j => ∑ i, u i j • S.f i, fun j => ∑ i, u' i j • S.f' i) ?_).1).symm
    have hBA := uni_mul hBi hA'
    refine ⟨A, Bi * A', hAI, int_mul L hBiI hAI', fun i j h => ⟨hA.1 i j h, hBA.1 i j h⟩,
      fun i => ⟨hA.2 i, hBA.2 i⟩, ?_, fun j => ?_, fun j => ?_⟩
    · choose c hc ec using hcong
      have e5 : A' * Ai - B₀ = algebraMap F E S.th • Matrix.of c := by
        ext i j; simp [ec]
      have e6 : Bi * A' - A = algebraMap F E S.th • (Bi * Matrix.of c * A) := by
        rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← e5, Matrix.mul_sub, Matrix.sub_mul, e4,
          Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, e2, Matrix.mul_one]
      intro i j
      exact ⟨(Bi * Matrix.of c * A) i j, int_mul L (int_mul L hBiI hc) hAI i j,
        congrFun (congrFun e6 i) j⟩
    · dsimp only
      rw [← rmul_mul, ← eA]
    · dsimp only
      rw [← rmul_mul, Matrix.mul_assoc, ← Matrix.mul_assoc B₀, e3, Matrix.one_mul, ← eA']
  have h1 : T.encard ≤ S₁.encard * (S₂.encard * R.encard) := by
    refine (Set.encard_le_encard hsub).trans ((Set.encard_image_le _ _).trans ?_)
    rw [Set.encard_prod, Set.encard_prod]
  have h2 : (T.encard : ℝ≥0∞) ≤ (S₁.encard : ℝ≥0∞) * ((S₂.encard : ℝ≥0∞) * (R.encard : ℝ≥0∞)) := by
    rw [← ENat.toENNReal_mul, ← ENat.toENNReal_mul]
    exact ENat.toENNReal_le.2 h1
  have h3 : (R.encard : ℝ≥0∞) ≤
      (resQ S.ϖ : ℝ≥0∞) ^ (2 * S.vth.toNat * ((r + 1) * (r + 1 - 1) / 2)) := by
    refine (ENat.toENNReal_le.2 hR).trans (le_of_eq ?_)
    rw [ENat.toENNReal_coe, ← pow_mul, Nat.cast_pow]
  refine h2.trans ((mul_le_mul' c1 (mul_le_mul' c2 h3)).trans (le_of_eq ?_))
  rw [← pow_add, ← pow_add, Frames.q, Int.toNat_add hv0 hvD]
  congr 1
  have h4 : (r + 1) * (r + 1 - 1) / 2 * 2 = r * (r + 1) := by
    rw [Nat.add_sub_cancel, mul_comm (r + 1) r]
    exact Nat.div_mul_cancel (Nat.even_mul_succ_self r).two_dvd
  rw [← h4]; ring

end GlobalTheory.IntClsCount
