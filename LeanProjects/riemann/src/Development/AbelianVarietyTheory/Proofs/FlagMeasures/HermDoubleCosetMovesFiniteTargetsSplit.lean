import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NoLeak
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetMoveTermWeightCharacterStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralLinearPositiveNormBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFineSubgroupMovesAtLatticeStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem split_by_target {W Y Z : Type} [AddCommGroup W] (A B : AddSubgroup W) (M : W → Prop) (m : W → Z)
    (f : Y → Z) (hf : Function.Injective f) (hB : Fine A (ind M) B)
    (hm : ∀ w, M w → ∀ b ∈ B, m (w + b) = m w) (hex : ∀ w, M w → ∃ y, f y = m w) (c : ℝ) (hc : 0 ≤ c) :
    {y | ∃ w, M w ∧ f y = m w}.Finite ∧ (∀ y, Nice A (ind fun w => M w ∧ f y = m w)) ∧
    {y | c * (cint A (ind fun w => M w ∧ f y = m w)).re ≠ 0}.Finite ∧
    (∀ y, 0 ≤ c * (cint A (ind fun w => M w ∧ f y = m w)).re) ∧
    ∀ (P : Y → Prop) (g : Y → ℂ) (G : W → ℂ), (∀ w y, (M w ∧ f y = m w) → G w = if P y then g y else 0) →
      (∀ w, ¬ M w → G w = 0) → Nice A G ∧
      ∑ᶠ y : {y // P y}, ((c * (cint A (ind fun w => M w ∧ f y = m w)).re : ℝ) : ℂ) * g y =
        (c : ℂ) * cint A G := by
  obtain ⟨hBA, hidx, hinv, hfin⟩ := hB
  have hsupp : Function.support (ind M) = {w | M w} := by
    ext w
    simp [ind]
  have hMinv : ∀ w, ∀ b ∈ B, (M (w + b) ↔ M w) := by
    intro w b hb
    have h := hinv w b hb
    simp only [ind] at h
    by_cases h1 : M (w + b) <;> by_cases h2 : M w <;> simp [h1, h2] at h ⊢
  have hTfin : {y | ∃ w, M w ∧ f y = m w}.Finite := by
    let g : Y → W ⧸ B := fun y =>
      if h : ∃ w, M w ∧ f y = m w then (QuotientAddGroup.mk h.choose : W ⧸ B) else 0
    refine Set.Finite.of_finite_image (f := g) (hfin.subset ?_) ?_
    · rintro _ ⟨y, hy, rfl⟩
      have hy' : ∃ w, M w ∧ f y = m w := hy
      refine ⟨hy'.choose, ?_, ?_⟩
      · rw [hsupp]
        exact hy'.choose_spec.1
      · simp only [g, dif_pos hy']
    · intro y1 hy1 y2 hy2 heq
      have hy1' : ∃ w, M w ∧ f y1 = m w := hy1
      have hy2' : ∃ w, M w ∧ f y2 = m w := hy2
      simp only [g, dif_pos hy1', dif_pos hy2'] at heq
      apply hf
      rw [hy1'.choose_spec.2, hy2'.choose_spec.2]
      have hb : -hy1'.choose + hy2'.choose ∈ B := QuotientAddGroup.eq.mp heq
      have h := hm _ hy1'.choose_spec.1 _ hb
      rw [add_neg_cancel_left] at h
      exact h.symm
  have hFine : ∀ y, Fine A (ind fun w => M w ∧ f y = m w) B := by
    intro y
    refine ⟨hBA, hidx, ?_, hfin.subset ?_⟩
    · intro w b hb
      simp only [ind]
      by_cases hw : M w
      · have h1 : M (w + b) := (hMinv w b hb).mpr hw
        simp only [h1, hw, true_and, hm w hw b hb]
      · have h1 : ¬ M (w + b) := fun h => hw ((hMinv w b hb).mp h)
        simp only [h1, hw, false_and]
    · apply Set.image_mono
      intro w hw
      rw [hsupp]
      by_contra hM
      refine (Function.mem_support.mp hw) ?_
      simp only [ind]
      rw [if_neg (fun h => hM h.1)]
  have hnice : ∀ y, Nice A (ind fun w => M w ∧ f y = m w) := fun y => ⟨B, hFine y⟩
  have hzero : ∀ y, y ∉ {y | ∃ w, M w ∧ f y = m w} → cint A (ind fun w => M w ∧ f y = m w) = 0 := by
    intro y hy
    have h : (ind fun w => M w ∧ f y = m w) = fun _ => 0 := by
      funext w
      simp only [ind]
      rw [if_neg]
      exact fun h => hy ⟨w, h⟩
    rw [h]
    simp [cint]
  obtain ⟨-, hI2, hI3, hI4⟩ := GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound A
  refine ⟨hTfin, hnice, hTfin.subset ?_, fun y => mul_nonneg hc (hI3 _).1, ?_⟩
  · intro y hy
    change c * _ ≠ 0 at hy
    by_contra hyT
    rw [hzero y hyT] at hy
    simp at hy
  · intro P g G hG hG0
    have hGeq : G = fun w => ∑ y ∈ hTfin.toFinset.filter P, g y * ind (fun w => M w ∧ f y = m w) w := by
      funext w
      by_cases hw : M w
      · obtain ⟨y0, hy0⟩ := hex w hw
        have hy0T : y0 ∈ hTfin.toFinset := by
          rw [Set.Finite.mem_toFinset]
          exact ⟨w, hw, hy0⟩
        rw [hG w y0 ⟨hw, hy0⟩]
        have hother : ∀ y, y ≠ y0 → ind (fun w => M w ∧ f y = m w) w = 0 := by
          intro y hne
          simp only [ind]
          rw [if_neg]
          rintro ⟨-, h⟩
          exact hne (hf (h.trans hy0.symm))
        by_cases hP : P y0
        · rw [if_pos hP, Finset.sum_eq_single y0]
          · simp only [ind]
            rw [if_pos ⟨hw, hy0⟩, mul_one]
          · intro y _ hne
            rw [hother y hne, mul_zero]
          · intro h
            exact absurd (Finset.mem_filter.mpr ⟨hy0T, hP⟩) h
        · rw [if_neg hP, Finset.sum_eq_zero]
          intro y hy
          have hne : y ≠ y0 := by
            rintro rfl
            exact hP (Finset.mem_filter.mp hy).2
          rw [hother y hne, mul_zero]
      · rw [hG0 w hw, Finset.sum_eq_zero]
        intro y _
        simp only [ind]
        rw [if_neg (fun h => hw h.1), mul_zero]
    have hcG : Nice A G ∧ cint A G =
        ∑ y ∈ hTfin.toFinset.filter P, g y * cint A (ind fun w => M w ∧ f y = m w) := by
      obtain ⟨hn, hs⟩ := hI4 Y (hTfin.toFinset.filter P)
        (fun y w => g y * ind (fun w => M w ∧ f y = m w) w) (fun y _ => (hI2 (g y) _ (hnice y)).1)
      rw [hGeq]
      exact ⟨hn, hs.trans (Finset.sum_congr rfl fun y _ => (hI2 (g y) _ (hnice y)).2)⟩
    refine ⟨hcG.1, ?_⟩
    rw [hcG.2]
    have hsub : Function.support (fun y : {y // P y} =>
        ((c * (cint A (ind fun w => M w ∧ f y.1 = m w)).re : ℝ) : ℂ) * g y.1) ⊆
        ↑(hTfin.toFinset.subtype P) := by
      intro y hy
      rw [Finset.mem_coe, Finset.mem_subtype, Set.Finite.mem_toFinset]
      by_contra hyT
      refine (Function.mem_support.mp hy) ?_
      rw [hzero y.1 hyT]
      simp
    rw [finsum_eq_sum_of_support_subset _ hsub]
    refine (Finset.sum_subtype_eq_sum_filter
      (fun y => ((c * (cint A (ind fun w => M w ∧ f y = m w)).re : ℝ) : ℂ) * g y)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have him := (hI3 (fun w => M w ∧ f y = m w)).2
    have hre : ((cint A (ind fun w => M w ∧ f y = m w)).re : ℂ) = cint A (ind fun w => M w ∧ f y = m w) :=
      Complex.ext (by simp) (by simp [him])
    push_cast
    rw [hre]
    ring

theorem moves_split_by_target : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → {Λ₁ : Submodule L.O S.V | ∃ w, S.MvTo (j + 1) d Λ Λ₁ w}.Finite ∧ (∀ Λ₁, Nice (S.refA (j + 1) Λ) (ind (S.MvTo (j + 1) d Λ Λ₁))) ∧ {Λ₁ | S.kern β (j + 1) βJ d Λ Λ₁ ≠ 0}.Finite ∧ (∀ Λ₁, 0 ≤ S.kern β (j + 1) βJ d Λ Λ₁) ∧ ∀ (P : Submodule L.O S.V → Prop) (g : Submodule L.O S.V → ℂ) (G : S.MW → ℂ), (∀ w Λ₁, S.MvTo (j + 1) d Λ Λ₁ w → G w = if P Λ₁ then g Λ₁ else 0) → (∀ w, ¬ S.Mv (j + 1) d Λ w → G w = 0) → Nice (S.refA (j + 1) Λ) G ∧ ∑ᶠ y : {y // P y}, (S.kern β (j + 1) βJ d Λ y : ℂ) * g y = (S.cK β βJ : ℂ) * cint (S.refA (j + 1) Λ) G := by
  intro F _ _ _ _ _ E _ _ _ L r k S j β βJ d Λ hT hFF
  obtain ⟨B, hB, hinv⟩ := GlobalTheory.T.exists_fineSubgroup_moves_at_lattice L r k S j β βJ d Λ hT hFF
  have hex : ∀ w, S.Mv (j + 1) d Λ w →
      ∃ Λ₁ : Submodule L.O S.V, (Λ₁ : Set S.V) = S.moved Λ w.1.1 w.2.1 (S.sOf w) := by
    intro w hw
    obtain ⟨Λ₁, h1, -⟩ := GlobalTheory.T.hermitianDoubleCoset_move_term_weight_character L r k S j β βJ d Λ hT hFF w.1.1 w.1.2 w.2.1 (S.sOf w) hw
    exact ⟨Λ₁, h1⟩
  have hc : 0 ≤ S.cK β βJ := by
    unfold Frames.cK
    positivity
  exact split_by_target (S.refA (j + 1) Λ) B (S.Mv (j + 1) d Λ)
    (fun w => S.moved Λ w.1.1 w.2.1 (S.sOf w)) (fun Λ₁ : Submodule L.O S.V => (Λ₁ : Set S.V))
    SetLike.coe_injective hB (fun w hw b hb => (hinv w hw b hb).1) hex (S.cK β βJ) hc

end GlobalTheory.HL
