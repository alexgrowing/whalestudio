import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.LocalMatchingOfAssemblyHypotheses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTwistedOrbitLocalFiniteness
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDiagUnit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagTMemIwGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryIwahoriOrbitalSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactElementEigenvaluesUnits

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.TwSide

section Generic

variable {G : Type} [Group G]

end Generic

section Diag

variable {L : Type} [Field L]

theorem thetaGL_diagT (c : L →+* L) {n : ℕ} (u : Fin n → Lˣ) :
    thetaGL n c (GlobalTheory.SmGL.diagT L (Fin n) u) =
      GlobalTheory.SmGL.diagT L (Fin n) fun i => Units.map (c : L →* L) (u i.rev)⁻¹ := by
  apply Units.ext
  ext i j
  rw [GlobalTheory.ThetaPull.thetaGL_apply, ← map_inv, GlobalTheory.SmGL.val_diagT, GlobalTheory.SmGL.val_diagT]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Even.neg_one_pow ⟨_, rfl⟩, one_mul]
    rfl
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (fun e => h (Fin.rev_injective e).symm), map_zero,
      mul_zero]

theorem exists_diagT {n : ℕ} (g : GL (Fin n) L) (h : ∀ i j : Fin n, i ≠ j → g.val i j = 0) :
    ∃ s : Fin n → Lˣ, g = GlobalTheory.SmGL.diagT L (Fin n) s := by
  have hne : ∀ i, g.val i i ≠ 0 := by
    intro i h0
    have h1 : (g.val * (g⁻¹).val) i i = 1 := by
      rw [← Units.val_mul, mul_inv_cancel]
      simp
    rw [Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      by_cases hk : i = k
      · subst hk
        rw [h0, zero_mul]
      · rw [h i k hk, zero_mul]
  refine ⟨fun i => Units.mk0 _ (hne i), ?_⟩
  apply Units.ext
  rw [GlobalTheory.SmGL.val_diagT]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    rfl
  · rw [Matrix.diagonal_apply_ne _ hij, h i j hij]

end Diag

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_diagT_of_mem_TO {n : ℕ} {w : Pl E} {τ : GLw n w} (hτ : τ ∈ TO n w) :
    ∃ v : Fin n → (w.adicCompletion E)ˣ, (∀ i, Valued.v (v i : w.adicCompletion E) = 1) ∧
      τ = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) v := by
  obtain ⟨v, hv⟩ := exists_diagT τ hτ.1
  refine ⟨v, fun i => ?_, hv⟩
  have h := hτ.2 i
  rw [hv, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_eq] at h
  exact h

theorem nrmL_diagT {n : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w) (u : Fin n → (w.adicCompletion E)ˣ) :
    nrmL n w (GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) u) =
      GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n)
        fun i => u i * Units.map (cj w : w.adicCompletion E →* w.adicCompletion E) (u i.rev)⁻¹ := by
  rw [nrmL, if_neg hw, thetaGL_diagT, ← map_mul]
  rfl

theorem ordL_norm_entry (hU : Unr E) {n : ℕ} {w : Pl E} (u : Fin n → (w.adicCompletion E)ˣ) (y : Fin n → ℤ)
    (hu : ∀ i, ordL (u i : w.adicCompletion E) = y i) (i : Fin n) :
    ordL ((u i * Units.map (cj w : w.adicCompletion E →* w.adicCompletion E) (u i.rev)⁻¹ :
      (w.adicCompletion E)ˣ) : w.adicCompletion E) = nv y i := by
  obtain ⟨-, -, hcv, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  have hinv : ordL (((u i.rev)⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = - y i.rev := by
    have h1 := GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_mul_of_ne (u i.rev).ne_zero ((u i.rev)⁻¹).ne_zero
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_one, hu] at h1
    omega
  have hmap : ordL ((Units.map (cj w : w.adicCompletion E →* w.adicCompletion E) (u i.rev)⁻¹ :
      (w.adicCompletion E)ˣ) : w.adicCompletion E) = - y i.rev := by
    rw [← hinv]
    exact GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_congr (hcv _)
  rw [Units.val_mul, GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_mul_of_ne (u i).ne_zero (Units.ne_zero _), hu, hmap]
  simp only [nv]
  omega

end GlobalTheory.CompanionTheory.TwSide
