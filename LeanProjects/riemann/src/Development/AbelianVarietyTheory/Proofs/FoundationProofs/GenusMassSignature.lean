import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelfDualLatticeMass
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.MassFormulaPositivity

noncomputable section

namespace GlobalTheory.Proof.GenusMassSignature

open NumberField Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeMass Matrix
open scoped ComplexOrder MatrixOrder

theorem denseRange_of_not_isReal {K : Type} [Field K] (σ : K →+* ℂ)
    (h : ¬ ComplexEmbedding.IsReal σ) : DenseRange σ := by
  have hc : IsClosed (σ.fieldRange.topologicalClosure : Set ℂ) :=
    Subfield.isClosed_topologicalClosure _
  rcases Complex.subfield_eq_of_closed hc with h1 | h1
  · exfalso
    apply h
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : σ x ∈ σ.fieldRange.topologicalClosure := Subfield.le_topologicalClosure _ ⟨x, rfl⟩
    rw [h1] at hx
    obtain ⟨r, hr⟩ := hx
    rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
    exact Complex.conj_ofReal r
  · have : closure (Set.range σ) = Set.univ := by
      have := congrArg (fun S : Subfield ℂ => (S : Set ℂ)) h1
      exact this
    exact dense_iff_closure_eq.2 this

theorem hasSignature_of_posDef {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} (h : J.PosDef) :
    Formalism.UG.HasSignature J n 0 := by
  let e : Fin n ≃ Fin n ⊕ Fin 0 := (Equiv.sumEmpty (Fin n) (Fin 0)).symm
  have h1 : (J.reindex e e).PosDef := by
    simpa using h.submatrix (e := e.symm) e.symm.injective
  have hJ : Formalism.UG.Jpq n 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  set A := J.reindex e e with hA
  have hS : star (CFC.sqrt A) = CFC.sqrt A := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hSS : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A h1.posSemidef.nonneg
  have hu : IsUnit (CFC.sqrt A) := by
    have := h1.isUnit
    rw [← hSS] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨U, hU⟩ := hu
  refine ⟨e, U⁻¹, ?_⟩
  have hc : Formalism.UG.cT (starRingEnd ℂ) ((U⁻¹ : GL (Fin n ⊕ Fin 0) ℂ) : Matrix _ _ ℂ) =
      star ((U⁻¹ : GL (Fin n ⊕ Fin 0) ℂ) : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) := by
    ext i j; rfl
  have hA2 : A = star (U : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) * U := by
    rw [hU, hS, hSS]
  rw [hJ, hc, ← hA, hA2, ← mul_assoc, ← star_mul, mul_assoc, Units.mul_inv, star_one, one_mul]

section Field

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem emb_form (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))
    (W : HSpace E) (τ : E →+* ℂ) (x : W.V) :
    τ (W.hD x x) = star (fun i => τ (W.frame.repr x i)) ⬝ᵥ
        (W.gram.map τ).mulVec (fun i => τ (W.frame.repr x i)) := by
  unfold HSpace.hD
  conv_lhs => rw [← W.frame.sum_repr x]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, map_mul, RingHom.id_apply, starRingEnd_apply, hst, dotProduct, Matrix.mulVec,
    Matrix.map_apply, HSpace.gram, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_isHermitian (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))
    (W : HSpace E) (τ : E →+* ℂ) : (W.gram.map τ).IsHermitian := by
  ext i k
  rw [conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, HSpace.gram, HSpace.gram,
    ← W.herm.eq (W.frame k) (W.frame i), starRingEnd_apply, hst]
  rfl

theorem pos_iff_posDef (htc : IsTotallyComplex E)
    (hst : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))
    (W : HSpace E) (τ : E →+* ℂ) :
    (∀ x : W.V, x ≠ 0 → 0 < (τ (W.hD x x)).re) ↔ (W.gram.map τ).PosDef := by
  constructor
  · intro h
    have hH := gram_isHermitian hst W τ
    have hd : DenseRange τ :=
      denseRange_of_not_isReal τ (IsTotallyComplex.complexEmbedding_not_isReal τ)
    have hdn : DenseRange fun (l : Fin W.rank → E) => (fun i => τ (l i)) :=
      DenseRange.piMap (fun _ : Fin W.rank => hd)
    have hco : ∀ l : Fin W.rank → E, τ (W.hD (W.frame.equivFun.symm l) (W.frame.equivFun.symm l)) =
        star (fun i => τ (l i)) ⬝ᵥ (W.gram.map τ).mulVec (fun i => τ (l i)) := by
      intro l
      rw [emb_form hst]
      have : ∀ i, W.frame.repr (W.frame.equivFun.symm l) i = l i := fun i =>
        congrFun (W.frame.equivFun.apply_symm_apply l) i
      simp only [this]
    have hne : ∀ l : Fin W.rank → E, l ≠ 0 → W.frame.equivFun.symm l ≠ 0 := fun l hl h0 =>
      hl (W.frame.equivFun.symm.injective (by rw [h0, map_zero]))
    have hpsd : (W.gram.map τ).PosSemidef := by
      refine PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_
      rw [Complex.nonneg_iff]
      refine ⟨?_, (hH.im_star_dotProduct_mulVec_self x).symm⟩
      refine hdn.induction_on (p := fun y => 0 ≤ (star y ⬝ᵥ ((W.gram.map τ) *ᵥ y)).re) x ?_ ?_
      · exact isClosed_le continuous_const (by fun_prop)
      · intro l
        by_cases hl : l = 0
        · subst hl
          simp [dotProduct]
        · have := h _ (hne l hl)
          rw [hco] at this
          exact this.le
    rw [hpsd.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro h0
    have h1 : W.gram.det = 0 := by
      apply τ.injective
      rw [RingHom.map_det, map_zero]
      exact h0
    obtain ⟨l, hl, hl0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h1
    have h2 : (W.gram.map τ).mulVec (fun i => τ (l i)) = 0 := by
      funext i
      have := congrArg τ (congrFun hl0 i)
      simpa [Matrix.mulVec, dotProduct] using this
    have := h _ (hne l hl)
    rw [hco, h2] at this
    simp at this
  · intro h x hx
    have hv : (fun i => τ (W.frame.repr x i)) ≠ 0 := by
      intro h
      apply hx
      apply W.frame.repr.injective
      ext i
      simpa using congrFun h i
    rw [emb_form hst]
    exact h.re_dotProduct_pos hv

def withPosSig (W : HSpace E) : HSpace E := { W with sig := fun _ => (W.rank, 0) }

end Field

end GlobalTheory.Proof.GenusMassSignature
