import Development.AbelianVarietyTheory.Definitions.Divisors.GlRes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic GlobalTheory.HCAlpha
open scoped ContDiff
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace GlobalTheory

theorem glBasis_sum_sq : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (glL E a)), ∀ (A : Type) [Ring A] [Algebra ℝ A] (ρ : glL E a →ₗ[ℝ] A), ∑ k, ρ (b k) * ρ (b k) = ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a, (ρ ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 + ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2) := by
  intro E _ _ _ a
  classical
  let b0 : Module.Basis (Σ _ : InfinitePlace E, Fin 2) ℝ (Cinf E) := Pi.basis fun _ => Complex.basisOneI
  have hb0 : ∀ w s, b0 ⟨w, s⟩ = Pi.single w (Complex.basisOneI s) := by
    intro w s; simp [b0]
  let b1 := b0.matrix (Fin a) (Fin a)
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 two_pos
  have hu : ∀ _ : Fin a × Fin a × (Σ _ : InfinitePlace E, Fin 2), IsUnit (Real.sqrt 2) :=
    fun _ => IsUnit.mk0 _ hs.ne'
  let b2 := (b1.isUnitSMul hu).map (Submodule.topEquiv (R := ℝ) (M := Matrix (Fin a) (Fin a) (Cinf E))).symm
  let e := Fintype.equivFin (Fin a × Fin a × (Σ _ : InfinitePlace E, Fin 2))
  refine ⟨_, b2.reindex e, ?_⟩
  intro A _ _ ρ
  let F : InfinitePlace E → Fin a → Fin a → A := fun w i j =>
    ρ ⟨Matrix.single i j (Pi.single w 1), Submodule.mem_top⟩ ^ 2 +
      ρ ⟨Matrix.single i j (Pi.single w Complex.I), Submodule.mem_top⟩ ^ 2
  let G : InfinitePlace E → A := fun w => ∑ i, ∑ j, F w i j
  have hsm : ∀ (r : ℝ) (X : Matrix (Fin a) (Fin a) (Cinf E)),
      ρ ⟨r • X, Submodule.mem_top⟩ = r • ρ ⟨X, Submodule.mem_top⟩ := by
    intro r X
    rw [← map_smul]; rfl
  have hb2 : ∀ i j w s, ρ (b2 (i, j, ⟨w, s⟩)) * ρ (b2 (i, j, ⟨w, s⟩)) =
      ρ ⟨Matrix.single i j (Pi.single w (Complex.basisOneI s)), Submodule.mem_top⟩ ^ 2 +
      ρ ⟨Matrix.single i j (Pi.single w (Complex.basisOneI s)), Submodule.mem_top⟩ ^ 2 := by
    intro i j w s
    have : b2 (i, j, ⟨w, s⟩) = ⟨Real.sqrt 2 • Matrix.single i j (Pi.single w (Complex.basisOneI s)), Submodule.mem_top⟩ := by
      apply Subtype.ext
      simp [b2, b1, Module.Basis.isUnitSMul_apply, hb0]
    rw [this, hsm, smul_mul_smul, Real.mul_self_sqrt (by norm_num), two_smul, sq]
  have hL : ∑ k, ρ (b2.reindex e k) * ρ (b2.reindex e k) = ∑ w, (G w + G w) := by
    simp only [Module.Basis.reindex_apply]
    rw [Equiv.sum_comp e.symm (fun x => ρ (b2 x) * ρ (b2 x))]
    simp only [Fintype.sum_prod_type, Fintype.sum_sigma, Fin.sum_univ_two, hb2, Complex.coe_basisOneI,
      Matrix.cons_val_zero, Matrix.cons_val_one, G, F]
    simp only [← Finset.sum_add_distrib]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
    abel
  have hτ : ∀ τ : E →+* ℂ, ∀ i j,
      ρ ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 +
        ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2 = F (InfinitePlace.mk τ) i j := by
    intro τ i j
    have hA1 : atEmb τ 1 = Pi.single (InfinitePlace.mk τ) 1 := by
      unfold atEmb; split_ifs <;> simp
    have hAI : ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2 =
        ρ ⟨Matrix.single i j (Pi.single (InfinitePlace.mk τ) Complex.I), Submodule.mem_top⟩ ^ 2 := by
      unfold atEmb
      split_ifs with h
      · rfl
      · have h1 : (⟨Matrix.single i j (Pi.single (InfinitePlace.mk τ) (starRingEnd ℂ Complex.I)), Submodule.mem_top⟩ : glL E a) =
            -⟨Matrix.single i j (Pi.single (InfinitePlace.mk τ) Complex.I), Submodule.mem_top⟩ := by
          apply Subtype.ext
          simp [Pi.single_neg, Matrix.single_neg]
        rw [h1, map_neg, neg_sq]
    simp only [F, hAI, hA1]
  have hR : ∑ τ : E →+* ℂ, ∑ i : Fin a, ∑ j : Fin a,
      (ρ ⟨Matrix.single i j (atEmb τ 1), Submodule.mem_top⟩ ^ 2 +
        ρ ⟨Matrix.single i j (atEmb τ Complex.I), Submodule.mem_top⟩ ^ 2) = ∑ w, (G w + G w) := by
    simp only [hτ]
    change ∑ τ : E →+* ℂ, G (InfinitePlace.mk τ) = _
    rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun τ => G (InfinitePlace.mk τ))]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => G w) (fun τ hτ' => by rw [(Finset.mem_filter.1 hτ').2]),
      Finset.sum_const, InfinitePlace.card_filter_mk_eq]
    have : w.mult = 2 := by
      simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)]
    rw [this, two_smul]
  rw [hL, hR]

end GlobalTheory
