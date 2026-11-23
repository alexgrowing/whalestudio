import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntIndMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAndSeparates

open MeasureTheory Matrix ValuativeRel

noncomputable section
namespace GlobalTheory.HeisUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

def entryForm (c : k) (i0 : Fin n) (j : Fin d) : Matrix (Fin n) (Fin d) k →ₗ[k] k where
  toFun Y := c * Y i0 j
  map_add' Y Y' := by simp [mul_add]
  map_smul' a Y := by simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem mu_tr_eq_smul (ψ0 : AddChar k ℂ)
    (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ))
    (hι : Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _))
    (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hTr : ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C))
    (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hMu : ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y)
    (φ0 : (Fin n × Fin d → k) → ℂ) (hφ0 : φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k)) (hι0 : ι φ0 = intInd k n d)
    (l : Matrix (Fin n) (Fin d) k →ₗ[k] k)
    (hl : ∀ Y : Matrix (Fin n) (Fin d) k, (∀ i j, Y i j ∈ 𝒪[k]) → ψ0 (l Y) = 1)
    (C : Matrix (Fin n) (Fin d) k) :
    Mu l (Tr C φ0) = ψ0 (l (-C)) • Tr C φ0 := by
  obtain ⟨hT, hTι⟩ := hTr C φ0 hφ0
  obtain ⟨hM, hMι⟩ := hMu l _ hT
  refine hι hM ((GlobalTheory.WeilM.SB _).smul_mem _ hT) ?_
  rw [map_smul, hMι, hTι, hι0]
  funext Y
  simp only [Pi.smul_apply, smul_eq_mul, intInd]
  by_cases h : ∀ i j, (Y + C) i j ∈ 𝒪[k]
  · have e : ψ0 (l Y) = ψ0 (l (-C)) := by
      calc ψ0 (l Y) = ψ0 (l (Y + C) + l (-C)) := by rw [← map_add]; congr 2; abel
        _ = ψ0 (l (-C)) := by rw [AddChar.map_add_eq_mul, hl _ h, one_mul]
    rw [e]
  · rw [Set.indicator_of_notMem (show Y + C ∉ {Y : Matrix (Fin n) (Fin d) k | ∀ i j, Y i j ∈ 𝒪[k]} from h)]
    simp

theorem inner_eq_mul_inner (ψ0 : AddChar k ℂ)
    (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hMuI : ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ)
    (μ : @Measure (Fin n × Fin d → k) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (l : Matrix (Fin n) (Fin d) k →ₗ[k] k) (f f' : (Fin n × Fin d → k) → ℂ)
    (hf : f ∈ GlobalTheory.WeilM.SB _) (hf' : f' ∈ GlobalTheory.WeilM.SB _) (a b : ℂ) (ha : Mu l f = a • f) (hb : Mu l f' = b • f') :
    ∫ y, f y * (starRingEnd ℂ) (f' y) ∂μ = a * (starRingEnd ℂ) b * ∫ y, f y * (starRingEnd ℂ) (f' y) ∂μ := by
  rw [← integral_const_mul, ← hMuI μ hμ l f hf f' hf', ha, hb]
  congr 1; funext y
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring

end GlobalTheory.HeisUnit

namespace GlobalTheory.HeisUnit

theorem cosetRep_sub_apply {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n d : ℕ} (ϖ : kˣ) (i0 : Fin n) (T T' : Fin d → SplitFlip.Res k 1) (j : Fin d) :
    (cosetRep ϖ i0 T' - cosetRep ϖ i0 T) i0 j =
      (ϖ : k)⁻¹ * (((Quotient.out (T j) : 𝒪[k]) : k) - ((Quotient.out (T' j) : 𝒪[k]) : k)) := by
  simp [cosetRep]; ring

theorem not_mem_int_of_ne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (hϖ : SplitFlip.IsUnif ϖ) (t t' : SplitFlip.Res k 1) (h : t ≠ t') :
    (ϖ : k)⁻¹ * (((Quotient.out t : 𝒪[k]) : k) - ((Quotient.out t' : 𝒪[k]) : k)) ∉ 𝒪[k] := by
  intro ha
  apply h
  rw [← Ideal.Quotient.mk_out t, ← Ideal.Quotient.mk_out t', Ideal.Quotient.eq]
  have hs : Quotient.out t - Quotient.out t' ∈ Ideal.span {(⟨ϖ, hϖ.mem⟩ : 𝒪[k])} := by
    refine Ideal.mem_span_singleton'.2 ⟨⟨_, ha⟩, Subtype.ext ?_⟩
    simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub]
    field_simp
  convert hs using 1
  exact (pow_one _).trans hϖ.maximalIdeal_eq

theorem orth_of_charsep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ)
    (hcs : (∀ x, ‖ψ0 x‖ = 1) ∧ ∀ a : k, a ∉ 𝒪[k] → ∃ c : k, (∀ y ∈ 𝒪[k], ψ0 (c * y) = 1) ∧ ψ0 (c * a) ≠ 1)
    (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ))
    (hι : Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _))
    (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hTr : ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C))
    (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hMu : ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y)
    (hMuI : ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ)
    (φ0 : (Fin n × Fin d → k) → ℂ) (hφ0 : φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k)) (hι0 : ι φ0 = intInd k n d)
    (ϖ : kˣ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (i0 : Fin n) (T T' : Fin d → GlobalTheory.SplitFlip.Res k 1) (hTT : T ≠ T')
    (μ : @Measure (Fin n × Fin d → k) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∫ y, Tr (cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y) ∂μ = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hTT
  set C := cosetRep ϖ i0 T
  set C' := cosetRep ϖ i0 T'
  have hna := not_mem_int_of_ne ϖ hϖ (T j) (T' j) hj
  rw [← cosetRep_sub_apply ϖ i0 T T' j] at hna
  obtain ⟨c, hc1, hc2⟩ := hcs.2 _ hna
  have hl : ∀ Y : Matrix (Fin n) (Fin d) k, (∀ i j, Y i j ∈ 𝒪[k]) → ψ0 (entryForm c i0 j Y) = 1 :=
    fun Y hY => hc1 _ (hY i0 j)
  have e1 := mu_tr_eq_smul ψ0 ι hι Tr hTr Mu hMu φ0 hφ0 hι0 _ hl C
  have e2 := mu_tr_eq_smul ψ0 ι hι Tr hTr Mu hMu φ0 hφ0 hι0 _ hl C'
  have hI := inner_eq_mul_inner ψ0 Mu hMuI μ hμ (entryForm c i0 j) _ _ (hTr C φ0 hφ0).1 (hTr C' φ0 hφ0).1 _ _ e1 e2
  have hA : ψ0 (entryForm c i0 j (-C)) * (starRingEnd ℂ) (ψ0 (entryForm c i0 j (-C'))) ≠ 1 := by
    rw [← Complex.inv_eq_conj (hcs.1 _), ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul, ← map_neg, ← map_add,
      neg_neg, neg_add_eq_sub]
    exact hc2
  set I := ∫ y, Tr C φ0 y * (starRingEnd ℂ) (Tr C' φ0 y) ∂μ
  have h0 : (1 - ψ0 (entryForm c i0 j (-C)) * (starRingEnd ℂ) (ψ0 (entryForm c i0 j (-C')))) * I = 0 := by
    linear_combination hI
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 (Ne.symm hA))

end GlobalTheory.HeisUnit

namespace GlobalTheory.HeisUnit

theorem tr_cosetRep_orth {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ) (hψc : Continuous ψ0) (hψ1 : ψ0 ≠ 1)
    (ι : ((Fin n × Fin d → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ))
    (hι : Set.InjOn ι (GlobalTheory.WeilM.SB (Fin n × Fin d → k) : Set _))
    (Tr : Matrix (Fin n) (Fin d) k → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hTr : ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C))
    (Mu : (Matrix (Fin n) (Fin d) k →ₗ[k] k) → ((Fin n × Fin d → k) → ℂ) → (Fin n × Fin d → k) → ℂ)
    (hMu : ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y)
    (hMuI : ∀ μ : @Measure (Fin n × Fin d → k) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ)
    (φ0 : (Fin n × Fin d → k) → ℂ) (hφ0 : φ0 ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → k)) (hι0 : ι φ0 = intInd k n d)
    (ϖ : kˣ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (i0 : Fin n) (T T' : Fin d → GlobalTheory.SplitFlip.Res k 1) (hTT : T ≠ T')
    (μ : @Measure (Fin n × Fin d → k) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∫ y, Tr (cosetRep ϖ i0 T) φ0 y * (starRingEnd ℂ) (Tr (cosetRep ϖ i0 T') φ0 y) ∂μ = 0 :=
  orth_of_charsep ψ0 (GlobalTheory.CharSep.unitary_and_separates ψ0 hψc hψ1) ι hι Tr hTr Mu hMu hMuI φ0 hφ0 hι0 ϖ hϖ i0 T T'
    hTT μ hμ

end GlobalTheory.HeisUnit
