import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DoubledIsotropicStructureGeneral
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MapConjInv
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.DblLag

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

omit [NumberField E] [IsCMField E] in
theorem mem_botSpan (g : M2 E r) (v : Fin r ⊕ Fin r → E) :
    v ∈ botSpan g ↔ ∃ c : Fin r → E, Sum.elim 0 c ᵥ* g = v := by
  rw [botSpan, Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun c => Eq.congr_left ?_
  ext j
  simp [vecMul, dotProduct, Finset.sum_apply]

theorem pair_vecMul (A B : M2 E r) (u v : Fin r ⊕ Fin r → E) :
    ((u ᵥ* A) ᵥ* B) ⬝ᵥ (fun j => cc ((v ᵥ* A) j)) = (u ᵥ* (A * B * ccT A)) ⬝ᵥ fun j => cc (v j) := by
  have e : (fun j => cc ((v ᵥ* A) j)) = ccT A *ᵥ fun j => cc (v j) := by
    ext j
    simp only [vecMul, mulVec, dotProduct, cc, ccT, map_sum, map_mul, transpose_apply, map_apply,
      mul_comm]
  rw [e, dotProduct_mulVec, vecMul_vecMul, vecMul_vecMul, Matrix.mul_assoc]

theorem iso_of_mem {g : M2 E r} (hg : g ∈ UU E r) {u v : Fin r ⊕ Fin r → E}
    (hu : u ∈ botSpan g) (hv : v ∈ botSpan g) :
    (u ᵥ* Matrix.J (Fin r) E) ⬝ᵥ (fun j => cc (v j)) = 0 := by
  obtain ⟨c, rfl⟩ := (mem_botSpan _ _).1 hu
  obtain ⟨d, rfl⟩ := (mem_botSpan _ _).1 hv
  have h : ccT (ccT g) * Matrix.J (Fin r) E * ccT g = Matrix.J (Fin r) E :=
    (HAct.group_part hg).2.2.1
  rw [HAct.ccT_ccT] at h
  rw [pair_vecMul, h, Matrix.J, vecMul_fromBlocks]
  simp [dotProduct, cc]

theorem finrank_botSpan {g : M2 E r} (hg : g ∈ UU E r) : Module.finrank E (botSpan g) = r := by
  have h : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).2 (HAct.group_part hg).1
  have hl := (Matrix.linearIndependent_rows_iff_isUnit.2 h).comp _
    (Sum.inr_injective (α := Fin r) (β := Fin r))
  have := finrank_span_eq_card hl
  rw [Fintype.card_fin] at this
  exact this

variable (X : Data E r)

theorem isUnit_dblT : IsUnit (dblT X) :=
  IsUnit.of_mul_eq_one_right _ (DblPair.dblT_left X)

theorem pair_dblT (x y x' y' : Fin r → E) :
    ((Sum.elim x y ᵥ* dblT X) ᵥ* Matrix.J (Fin r) E) ⬝ᵥ (fun j => cc ((Sum.elim x' y' ᵥ* dblT X) j)) =
      X.κ0 / 2 * (herm X.Gm x x' - herm X.Gm y y') := by
  rw [pair_vecMul, DblPair.dblT_form, vecMul_fromBlocks]
  have e : ∀ x y : Fin r → E, herm X.Gm x y = ∑ b, (x ᵥ* X.Gm) b * cc (y b) := fun x y => by
    rw [herm, Finset.sum_comm]
    simp only [vecMul, dotProduct, Finset.sum_mul]
  simp [dotProduct, e, vecMul_neg, vecMul_smul, mul_add, Finset.mul_sum, mul_assoc, sub_eq_add_neg]

theorem mem_iota (γ : GL (Fin r) E) (x y : Fin r → E) :
    Sum.elim x y ᵥ* dblT X ∈ botSpan (iota X 1 γ) ↔ y = (γ⁻¹).1 *ᵥ x := by
  have hinj : Function.Injective fun v => v ᵥ* dblT X :=
    Matrix.vecMul_injective_iff_isUnit.2 (isUnit_dblT X)
  have hk : (2 * (X.κ0 / 4)) ≠ 0 := by simp [DblPair.kappa_ne X]
  have key : ∀ c : Fin r → E, Sum.elim 0 c ᵥ* iota X 1 γ =
      Sum.elim (c ᵥ* ((2 * (X.κ0 / 4))⁻¹ • X.Gm⁻¹))
        ((γ⁻¹).1 *ᵥ (c ᵥ* ((2 * (X.κ0 / 4))⁻¹ • X.Gm⁻¹))) ᵥ* dblT X := fun c => by
    rw [iota, Matrix.inv_eq_left_inv (DblPair.dblT_left X), ← vecMul_vecMul, ← vecMul_vecMul,
      vecMul_fromBlocks, vecMul_fromBlocks]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_vecMul, vecMul_zero, zero_add, add_zero,
      inv_one, Units.val_one, transpose_one, vecMul_one, vecMul_transpose]
  rw [mem_botSpan]
  constructor
  · rintro ⟨c, hc⟩
    rw [key] at hc
    have h := hinj hc
    have h1 := congrArg (· ∘ Sum.inl) h
    have h2 := congrArg (· ∘ Sum.inr) h
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h1 h2
    rw [← h2, h1]
  · rintro rfl
    refine ⟨x ᵥ* ((2 * (X.κ0 / 4)) • X.Gm), ?_⟩
    rw [key, vecMul_vecMul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hk,
      mul_nonsing_inv _ (Ne.isUnit X.Gm_det), one_smul, vecMul_one]

noncomputable def coord : ((Fin r → E) × (Fin r → E)) ≃ₗ[E] (Fin r ⊕ Fin r → E) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin r) E E).symm.trans
    (LinearEquiv.ofBijective (dblT X).vecMulLinear
      ⟨Matrix.vecMul_injective_iff_isUnit.2 (isUnit_dblT X),
        Matrix.vecMul_surjective_iff_isUnit.2 (isUnit_dblT X)⟩)

theorem coord_apply (p : (Fin r → E) × (Fin r → E)) :
    coord X p = Sum.elim p.1 p.2 ᵥ* dblT X := rfl

end GlobalTheory.SW.DblLag

open GlobalTheory.SW.DblLag in

theorem GlobalTheory.SW.lag_graph_or_isotropic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ γ γ' : GL (Fin r) E, IsUn X γ → IsUn X γ' → botSpan (iota X 1 γ) = botSpan (iota X 1 γ') → γ = γ') ∧ ∀ U : Lag E r, (∃ γ : GL (Fin r) E, IsUn X γ ∧ botSpan (iota X 1 γ) = U.1) ∨ ∃ ξ : Fin r → E, ξ ≠ 0 ∧ herm X.Gm ξ ξ = 0 ∧ Sum.elim ξ 0 ᵥ* dblT X ∈ U.1 := by
  intro E _ _ _ r X
  refine ⟨fun γ γ' _ _ h => ?_, ?_⟩
  · refine inv_injective (Units.ext (Matrix.toLin'.injective (LinearMap.ext fun x => ?_)))
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← mem_iota X, ← h, mem_iota]
  rintro ⟨U, g, hg, rfl⟩
  set I := (botSpan g).comap (coord X).toLinearMap with hI
  have hm : ∀ p, p ∈ I ↔ Sum.elim p.1 p.2 ᵥ* dblT X ∈ botSpan g := fun p => Iff.rfl
  have hiso : ∀ p ∈ I, ∀ q ∈ I, herm X.Gm p.1 q.1 - herm X.Gm p.2 q.2 = 0 := fun p hp q hq => by
    have := iso_of_mem hg ((hm p).1 hp) ((hm q).1 hq)
    rw [pair_dblT] at this
    exact (mul_eq_zero.1 this).resolve_left (by simp [DblPair.kappa_ne X])
  have hd : Module.finrank E I = r := by
    rw [hI, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq, finrank_botSpan hg]
  obtain ⟨a1, -, -, -, -, -, a2, -⟩ :=
    (doubled_isotropic_structure X.Gm X.Gm_herm X.Gm_det).1 I hiso hd
  by_cases h0 : DoubledSpace.left I = ⊥
  · obtain ⟨δ, ⟨d1, d2⟩, -⟩ := a2.1 h0
    refine Or.inl ⟨δ⁻¹, fun x y => ?_, ?_⟩
    · rw [← d1, mulVec_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec, one_mulVec]
    · ext v
      obtain ⟨⟨x, y⟩, rfl⟩ := (coord X).surjective v
      rw [coord_apply, mem_iota, inv_inv, ← d2, hm]
  · obtain ⟨ξ, hξ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    exact Or.inr ⟨ξ, hne, a1 ξ hξ ξ hξ, (hm (ξ, 0)).1 hξ⟩
