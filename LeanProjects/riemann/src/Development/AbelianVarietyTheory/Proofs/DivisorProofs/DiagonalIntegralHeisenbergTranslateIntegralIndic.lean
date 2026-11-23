import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagWZero
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.InertLagInd

variable {F : Type} [Field F] [NumberField F] {v : Pl F} {κ : Type} [Fintype κ]

theorem invOf_two_mem (h : (2 : 𝓞 F) ∉ v.asIdeal) : ⅟(2 : Fv F v) ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.valuation F (algebraMap (𝓞 F) F 2) = 1 := (v.valuation_eq_one_iff_notMem (K := F)).2 h
  rw [map_ofNat] at h1
  have h2 : Valued.v (algebraMap F (Fv F v) (2 : F)⁻¹) = v.valuation F (2 : F)⁻¹ :=
    v.valuedAdicCompletion_eq_valuation' _
  simp only [map_inv₀] at h2
  rw [h1, inv_one, map_ofNat] at h2
  rw [invOf_eq_inv, map_inv₀, h2]

theorem schr_box_apply (ψ : AddChar (Fv F v) ℂ) (φ₁ φ₂ : (κ → Fv F v) → ℂ) (w : (κ → Fv F v) × (κ → Fv F v))
    (x : κ → Fv F v) :
    schr ψ (Sum.elim w.1 0, Sum.elim w.2 0) (boxFun φ₁ φ₂) (Sum.elim x x) =
      ψ (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) * (φ₁ (x + w.1) * φ₂ x) := by
  simp only [schr, boxFun, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero]
  congr 2
  all_goals (congr 1; funext i; simp)

end GlobalTheory.InertLagInd

namespace GlobalTheory.InertLagInd

theorem diagW_box_indicator : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ]
    (ψ : AddChar (AF F) ℂ), PsiUnr ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∃ φ₀ ∈ SB (κ → Fv F v), ∃ c : ℂ, c ≠ 0 ∧ ∃ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U ∧ IsCompact U ∧ 0 ∈ U ∧
      ∀ w, diagW (psiAt ψ v) μ (boxFun φ₀ φ₀) w = U.indicator (fun _ => c) w := by
  intro F _ _ v κ _ ψ hψ h2 μ hμ
  classical
  letI : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  haveI := hμ
  obtain ⟨S, hS⟩ : ∃ S : Set (κ → Fv F v), S = {x | ∀ k, x k ∈ v.adicCompletionIntegers F} := ⟨_, rfl⟩
  have hmem : ∀ x, x ∈ S ↔ ∀ k, x k ∈ v.adicCompletionIntegers F := fun x => by subst hS; rfl
  have hpi : S = Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
    ext x; simp [hmem]
  have hSo : IsOpen S := by
    rw [hpi]; exact isOpen_set_pi Set.finite_univ (fun _ _ => Valued.isOpen_integer _)
  have hSc : IsCompact S := by
    rw [hpi]; exact isCompact_univ_pi (fun _ => PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v)
  have h0S : (0 : κ → Fv F v) ∈ S := (hmem 0).2 fun k => zero_mem _
  have hadd : ∀ {a}, a ∈ S → ∀ x, (x + a ∈ S ↔ x ∈ S) := fun {a} ha x => by
    rw [hmem, hmem]
    rw [hmem] at ha
    exact ⟨fun h k => by simpa using sub_mem (h k) (ha k), fun h k => add_mem (h k) (ha k)⟩
  have hind : ∀ {a}, a ∈ S → ∀ x, S.indicator (1 : (κ → Fv F v) → ℂ) (x + a) = S.indicator 1 x := fun ha x => by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hadd ha x).2 hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt (hadd ha x).1 hx)]
  have hψ1 : ∀ y ∈ v.adicCompletionIntegers F, psiAt ψ v y = 1 := fun y hy => by
    rw [psiAt_apply]; simpa using (hψ 1).2 (one_mem _) y hy
  have hφ : S.indicator (1 : (κ → Fv F v) → ℂ) ∈ SB (κ → Fv F v) := by
    rw [hS]; exact GlobalTheory.StdVacuum.indicator_mem_SB v
  refine ⟨S.indicator 1, hφ, ((μ.real S : ℝ) : ℂ), ?_, S ×ˢ S, hSo.prod hSo, hSc.prod hSc, ⟨h0S, h0S⟩, ?_⟩
  · have h1 : μ S ≠ 0 := hSo.measure_ne_zero μ ⟨0, h0S⟩
    have h2' : μ S ≠ ⊤ := hSc.measure_lt_top.ne
    exact Complex.ofReal_ne_zero.2 (by rw [measureReal_def]; exact ENNReal.toReal_ne_zero.2 ⟨h1, h2'⟩)
  intro w
  simp only [diagW, schr_box_apply]
  by_cases hw1 : w.1 ∈ S
  · by_cases hw2 : w.2 ∈ S
    · rw [Set.indicator_of_mem (Set.mem_prod.2 ⟨hw1, hw2⟩)]
      have key : ∀ x, psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) *
          (S.indicator 1 (x + w.1) * S.indicator 1 x) = S.indicator (1 : (κ → Fv F v) → ℂ) x := by
        intro x
        rw [hind hw1 x]
        by_cases hx : x ∈ S
        · rw [Set.indicator_of_mem hx, hψ1]
          · simp
          · rw [hmem] at hx hw1 hw2
            exact add_mem (sum_mem fun i _ => mul_mem (hx i) (hw2 i))
              (mul_mem (invOf_two_mem h2) (sum_mem fun i _ => mul_mem (hw1 i) (hw2 i)))
        · simp [Set.indicator_of_notMem hx]
      simp_rw [key]
      rw [show S.indicator (1 : (κ → Fv F v) → ℂ) = S.indicator (fun _ => (1 : ℂ)) from rfl,
        integral_indicator_const _ hSo.measurableSet]
      simp
    · rw [Set.indicator_of_notMem (fun h => hw2 (Set.mem_prod.1 h).2)]
      obtain ⟨i, hi⟩ : ∃ i, w.2 i ∉ v.adicCompletionIntegers F := by
        by_contra h; push_neg at h; exact hw2 ((hmem _).2 h)
      obtain ⟨y, hy, hne⟩ : ∃ y ∈ v.adicCompletionIntegers F, psiLoc ψ v (w.2 i * y) ≠ 1 := by
        by_contra h; push_neg at h; exact hi ((hψ _).1 h)
      have ha : Pi.single i y ∈ S := (hmem _).2 fun k => by
        rw [Pi.single_apply]; split_ifs
        · exact hy
        · exact zero_mem _
      set g : (κ → Fv F v) → ℂ := fun x => psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) *
          (S.indicator 1 (x + w.1) * S.indicator 1 x) with hg
      have hshift : ∀ x, g (x + Pi.single i y) = psiAt ψ v (w.2 i * y) * g x := by
        intro x
        simp only [hg]
        rw [add_right_comm, hind ha, hind ha, add_dotProduct, single_dotProduct,
          show x ⬝ᵥ w.2 + y * w.2 i + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) =
            w.2 i * y + (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) by ring, AddChar.map_add_eq_mul]
        ring
      have hI : ∫ x, g x ∂μ = psiAt ψ v (w.2 i * y) * ∫ x, g x ∂μ := by
        rw [← integral_const_mul, ← integral_add_right_eq_self _ (Pi.single i y)]
        simp only [hshift]
      rw [psiAt_apply] at hI
      have : (1 - psiLoc ψ v (w.2 i * y)) * ∫ x, g x ∂μ = 0 := by rw [sub_mul, one_mul, ← hI, sub_self]
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne.symm)
  · rw [Set.indicator_of_notMem (fun h => hw1 (Set.mem_prod.1 h).1)]
    have hz : ∀ x, psiAt ψ v (x ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2)) *
        (S.indicator (1 : (κ → Fv F v) → ℂ) (x + w.1) * S.indicator 1 x) = 0 := by
      intro x
      by_cases hx : x ∈ S
      · have : x + w.1 ∉ S := fun h => hw1 (by rw [add_comm] at h; exact (hadd hx w.1).1 h)
        simp [Set.indicator_of_notMem this]
      · simp [Set.indicator_of_notMem hx]
    simp_rw [hz]
    exact integral_zero _ _

end GlobalTheory.InertLagInd
end
