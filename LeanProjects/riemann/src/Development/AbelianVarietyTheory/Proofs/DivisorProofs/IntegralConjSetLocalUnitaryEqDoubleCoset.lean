import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSquareOneAddFourMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintIffMatrixImageStandardLatticeEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFullRankLatticeImageStandardLatticeGLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualImageStandardLatticeUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixImageAdjointMulEqOfSelfDualLatticesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitEqOfStableLatticesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryAdjoinLatticeImageEqStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.OrbitT

open GlobalTheory.LatOrb

theorem stable_of_conj {O K : Type} [CommRing O] [Field K] [Algebra O K] {n : ℕ} (g : GL (Fin n) K)
    (γ : Matrix (Fin n) (Fin n) K)
    (h : matLat O ((g⁻¹ : GL (Fin n) K).val * γ * g.val) (stdLat O n) = stdLat O n) :
    ∀ v ∈ matLat O g.val (stdLat O n), γ *ᵥ v ∈ matLat O g.val (stdLat O n) := by
  intro v hv
  have e : γ * g.val = g.val * ((g⁻¹ : GL (Fin n) K).val * γ * g.val) := by
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  have h2 : matLat O γ (matLat O g.val (stdLat O n)) = matLat O g.val (stdLat O n) := by
    rw [← matLat_mul, e, matLat_mul, h]
  rw [← h2]
  exact (mem_matLat _ _ _).2 ⟨v, hv, rfl⟩

theorem orbit_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, cj w (cj w x) = x) → (∀ x, Valued.v (cj w x) = Valued.v x) →
    ∀ P₀ : (w.adicCompletionIntegers E)[X], IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∀ g₁ g₂ : UL n w, g₁⁻¹ * γ * g₁ ∈ KL n w → g₂⁻¹ * γ * g₂ ∈ KL n w →
    ∃ t ∈ twCent (MonoidHom.id (UL n w)) γ, ∃ k ∈ KL n w, g₂ = t * g₁ * k := by
  intro E _ _ _ n w hcc hcv P₀ hcop γ hγ g₁ g₂ h₁ h₂
  haveI := GlobalTheory.HenselSquare.isAdicComplete_integers E w
  have hσO : ∀ a : w.adicCompletionIntegers E, ∃ b : w.adicCompletionIntegers E,
      cj w (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) a) =
        algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E) b := by
    intro a
    refine ⟨⟨cj w a, ?_⟩, rfl⟩
    have ha := a.2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at ha ⊢
    rw [hcv]; exact ha
  have hK : ∀ h : UL n w, h ∈ KL n w ↔ matLat (w.adicCompletionIntegers E) h.1.val
      (stdLat (w.adicCompletionIntegers E) n) = stdLat (w.adicCompletionIntegers E) n := by
    intro h
    exact (Subgroup.mem_subgroupOf).trans (GlobalTheory.T.mem_GLint_iff_matrixImage_standardLattice_eq (w.adicCompletionIntegers E) n h.1)
  have st : ∀ g : UL n w, g⁻¹ * γ * g ∈ KL n w → ∀ v ∈ matLat (w.adicCompletionIntegers E) g.1.val
      (stdLat (w.adicCompletionIntegers E) n), γ.1.val *ᵥ v ∈ matLat (w.adicCompletionIntegers E) g.1.val
      (stdLat (w.adicCompletionIntegers E) n) := by
    intro g hg
    have h := (hK _).1 hg
    have e : ((g⁻¹ * γ * g : UL n w).1.val) = (g.1⁻¹ : GLw n w).val * γ.1.val * g.1.val := by simp
    rw [e] at h
    exact stable_of_conj g.1 γ.1.val h
  obtain ⟨t, htU, htc, htM⟩ : ∃ t : GLw n w, t ∈ UL n w ∧ t * γ.1 = γ.1 * t ∧
      matLat (w.adicCompletionIntegers E) t.val (matLat (w.adicCompletionIntegers E) g₁.1.val
        (stdLat (w.adicCompletionIntegers E) n)) = matLat (w.adicCompletionIntegers E) g₂.1.val
        (stdLat (w.adicCompletionIntegers E) n) := by
    obtain ⟨p, hpu, hp⟩ := GlobalTheory.T.exists_unit_eq_of_stable_lattices n P₀ hcop γ.1.val hγ _ _ (GlobalTheory.T.isFullRankLattice_image_standardLattice_GL n g₁.1) (GlobalTheory.T.isFullRankLattice_image_standardLattice_GL n g₂.1) (st g₁ h₁) (st g₂ h₂)
    by_cases hs : IsSplitAt w
    · refine ⟨hpu.unit, by simp [UL, hs], ?_, hp.symm⟩
      ext : 1
      simp only [Units.val_mul, IsUnit.unit_spec]
      have e1 : aeval γ.1.val p * γ.1.val = aeval γ.1.val (p * X) := by rw [map_mul, aeval_X]
      have e2 : γ.1.val * aeval γ.1.val p = aeval γ.1.val (X * p) := by rw [map_mul, aeval_X]
      rw [e1, e2, mul_comm]
    · have hUL : ∀ h : UL n w, ((h.1.val).map (cj w))ᵀ * h.1.val = 1 := by
        intro h
        have := h.2
        simp only [UL, hs, if_false] at this
        simpa [UJ, cT] using this
      have sd : ∀ g : UL n w, SelfDual (w.adicCompletionIntegers E) (cj w)
          (matLat (w.adicCompletionIntegers E) g.1.val (stdLat (w.adicCompletionIntegers E) n)) :=
        fun g => GlobalTheory.T.isSelfDual_image_standardLattice_unitary (cj w) hcc hσO n _ (hUL g)
      have hc := GlobalTheory.T.matrixImage_adjoint_mul_eq_of_selfDual_lattices (cj w) hcc n (aeval γ.1.val p) hpu _ (sd g₁) (hp ▸ sd g₂)
      obtain ⟨t, ht1, htc, htM⟩ := GlobalTheory.T.exists_unitary_adjoin_lattice_image_eq n P₀ hcop γ.1.val hγ (cj w) hcc hσO (hUL γ) _ (GlobalTheory.T.isFullRankLattice_image_standardLattice_GL n g₁.1)
        (st g₁ h₁) p hpu hc
      have htu : IsUnit t := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse ht1)
      refine ⟨htu.unit, ?_, ?_, by rw [hp]; exact htM⟩
      · show _ ∈ UL n w
        simp only [UL, hs, if_false]
        show cT (cj w) _ * 1 * _ = 1
        simpa [cT] using ht1
      · ext : 1
        simpa using htc
  refine ⟨⟨t, htU⟩, ?_, (⟨t, htU⟩ * g₁)⁻¹ * g₂, ?_, by group⟩
  · show (⟨t, htU⟩ : UL n w) * γ = γ * (⟨t, htU⟩ : UL n w)
    exact Subtype.ext htc
  · rw [hK]
    have e : (((⟨t, htU⟩ : UL n w) * g₁)⁻¹ * g₂ : UL n w).1.val =
        (g₁.1⁻¹ : GLw n w).val * ((t⁻¹ : GLw n w).val * g₂.1.val) := by simp [mul_assoc]
    rw [e, matLat_mul, matLat_mul, ← htM, ← matLat_mul (a := ((t⁻¹ : GLw n w).val)), Units.inv_mul, matLat_one,
      ← matLat_mul, Units.inv_mul, matLat_one]

end GlobalTheory.BCT.OrbitT
