import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootExtractionLemmaSheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypicalCurvesTangentAndBasesStatement

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem det_eq_det_minor_of_unit_rows {K : Type} [CommRing K] {i d : ℕ} (r : Fin i → Fin d)
    (hr : Function.Injective r) (M : Matrix (Fin d) (Fin d) K)
    (hM : ∀ e, e ∉ Set.range r → ∀ c, M e c = if c = e then 1 else 0) :
    M.det = (M.submatrix r r).det := by
  classical
  let E : Fin i ⊕ {e // e ∉ Set.range r} ≃ Fin d :=
    (Equiv.sumCongr (Equiv.ofInjective r hr) (Equiv.refl _)).trans
      (Equiv.sumCompl (fun e => e ∈ Set.range r))
  have hEl : ∀ a, E (Sum.inl a) = r a := fun a => rfl
  have hEr : ∀ e, E (Sum.inr e) = e.1 := fun e => rfl
  rw [← Matrix.det_submatrix_equiv_self E M, ← Matrix.fromBlocks_toBlocks (M.submatrix E E)]
  have h21 : (M.submatrix E E).toBlocks₂₁ = 0 := by
    ext e b
    simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply, Matrix.zero_apply, hEl, hEr]
    rw [hM e.1 e.2, if_neg]
    rintro h
    exact e.2 ⟨b, h⟩
  have h22 : (M.submatrix E E).toBlocks₂₂ = 1 := by
    ext e e'
    simp only [Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply, hEr, Matrix.one_apply]
    rw [hM e.1 e.2]
    by_cases hee : e = e'
    · subst hee; simp
    · rw [if_neg (fun h => hee (Subtype.ext h).symm), if_neg hee]
  have h11 : (M.submatrix E E).toBlocks₁₁ = M.submatrix r r := by
    ext a b
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply, hEl]
  rw [h21, Matrix.det_fromBlocks_zero₂₁, h22, Matrix.det_one, mul_one, h11]

end GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem exists_basis_adapted_frame : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (d h : ℕ), 0 < h →
    ∀ (ty : Fin d → ZMod h) (G : LogFGL v d), MuAction G p h ty → ∀ (τ : ZMod h) (j i : ℕ),
    (Finset.univ.filter fun a => ty a = τ + 1).card ≤ j → ∀ u : Fin i → Fin d → C,
    IsSatFrame v u → (∀ a e, ty e ≠ τ → u a e = 0) →
    ∃ (γ : Fin d → Fin d → PowerSeries C) (r : Fin i ↪ Fin d) (g : Matrix (Fin i) (Fin i) C),
      IsBasis G p ty γ ∧ (∀ a b, IsIntV v (g a b)) ∧ v g.det = 0 ∧
      (∀ a, tangent (γ (r a)) = ∑ a', g a a' • u a') ∧
      ∀ a : Fin i, j ≤ a.val → G.lc p (γ (r a)) 1 = 0 := by
  intro C _ _ _ v p hp hv d h hh ty G hmu τ j i hj u hu hut
  classical
  obtain ⟨hPT2, -⟩ := GlobalTheory.T.typicalCurveEigenspace_and_basisExists
  choose η hηc hηt hηtan using fun a : Fin i =>
    hPT2 C v p hp hv d h hh ty G hmu τ (u a) (hu.1 a) (hut a)
  have hspan : Module.finrank C (Submodule.span C (Set.range fun a =>
      (LinearMap.id : (Fin d → C) →ₗ[C] (Fin d → C)) (G.lc p (η a) 1))) ≤ j := by
    let W := Submodule.span C
      (Set.range fun e : {e : Fin d // ty e = τ + 1} => (Pi.single e.1 (1 : C) : Fin d → C))
    have hle : Submodule.span C (Set.range fun a =>
        (LinearMap.id : (Fin d → C) →ₗ[C] (Fin d → C)) (G.lc p (η a) 1)) ≤ W := by
      rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      show G.lc p (η a) 1 ∈ W
      rw [← Finset.univ_sum_single (G.lc p (η a) 1)]
      refine Submodule.sum_mem _ fun e _ => ?_
      by_cases he : ty e = τ + 1
      · have : (Pi.single e (G.lc p (η a) 1 e) : Fin d → C) =
            G.lc p (η a) 1 e • (Pi.single e (1 : C) : Fin d → C) := by
          ext c; simp [Pi.single_apply]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨e, he⟩, rfl⟩)
      · rw [(hηt a).2 1 e (by simpa using he), Pi.single_zero]
        exact Submodule.zero_mem _
    calc _ ≤ Module.finrank C W := Submodule.finrank_mono hle
      _ ≤ Fintype.card {e : Fin d // ty e = τ + 1} := finrank_range_le_card _
      _ = _ := Fintype.card_subtype _
      _ ≤ j := hj
  obtain ⟨x, hxi, hxd, hxt, hxty, hxl⟩ := GlobalTheory.T.root_extraction_lemma_sheaf C v p hp hv d h i ty τ G η
    (fun a => hηc a) (fun a => hηt a) 1 j le_rfl (Fin d → C) LinearMap.id hspan
  set γ' : Fin i → Fin d → PowerSeries C :=
    fun w => G.sumF fun u => rescaleCurve (x w u) (η u) with hγ'
  have hγ'c : ∀ w, IsCurve v (γ' w) := fun w =>
    (pt6' C v p hp hv d i G η (x w) (fun a => hηc a) (fun a => hxi w a)).1
  obtain ⟨r0, hr0⟩ := hu.2
  set U : Matrix (Fin i) (Fin i) C := Matrix.of fun a b => u a (r0 b) with hU
  have hUne : U.det ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hr0
    exact WithTop.top_ne_zero hr0
  have hinj : Function.Injective r0 := by
    intro b1 b2 heq
    by_contra hne
    exact hUne (Matrix.det_zero_of_column_eq hne (fun a => by simp [hU, heq]))
  have hty0 : ∀ b, ty (r0 b) = τ := by
    intro b
    by_contra hne
    exact hUne (Matrix.det_eq_zero_of_column_eq_zero b (fun a => by simp [hU, hut a _ hne]))
  choose ζ hζc hζt hζtan using fun e : Fin d =>
    hPT2 C v p hp hv d h hh ty G hmu (ty e) (Pi.single e 1)
      (fun c => by
        unfold IsIntV
        by_cases hc : c = e
        · subst hc; simp
        · simp [Pi.single_apply, hc])
      (fun c hc => by
        have : c ≠ e := fun h' => hc (h' ▸ rfl)
        simp [Pi.single_apply, this])
  let γ : Fin d → Fin d → PowerSeries C := fun e =>
    if hm : e ∈ Set.range r0 then γ' ((Equiv.ofInjective r0 hinj).symm ⟨e, hm⟩) else ζ e
  have hγr : ∀ a, γ (r0 a) = γ' a := by
    intro a
    simp only [γ, dif_pos (Set.mem_range_self a)]
    rw [Equiv.ofInjective_symm_apply]
  have hγn : ∀ e, e ∉ Set.range r0 → γ e = ζ e := fun e he => by simp only [γ, dif_neg he]
  have htan : ∀ a, tangent (γ (r0 a)) = ∑ a', x a a' • u a' := by
    intro a
    rw [hγr, hxt a]
    simp only [hηtan]
  refine ⟨γ, ⟨r0, hinj⟩, x, ⟨fun e => ?_, fun e => ?_, ?_⟩, hxi, hxd, htan, fun a ha => ?_⟩
  · by_cases he : e ∈ Set.range r0
    · obtain ⟨b, rfl⟩ := he
      rw [hγr]; exact hγ'c b
    · rw [hγn e he]; exact hζc e
  · by_cases he : e ∈ Set.range r0
    · obtain ⟨b, rfl⟩ := he
      rw [hγr, hty0]; exact hxty b
    · rw [hγn e he]; exact hζt e
  · rw [det_eq_det_minor_of_unit_rows r0 hinj]
    · have hsub : (Matrix.of fun a b => tangent (γ a) b).submatrix r0 r0 = x * U := by
        ext a b
        simp only [Matrix.submatrix_apply, Matrix.of_apply, htan, Matrix.mul_apply, hU,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [hsub, Matrix.det_mul, AddValuation.map_mul, hxd, hr0, add_zero]
    · intro e he c
      simp only [Matrix.of_apply, hγn e he, hζtan, Pi.single_apply]
  · show G.lc p (γ (r0 a)) 1 = 0
    rw [hγr]
    simpa using hxl a ha

end GlobalTheory.FGDepth
