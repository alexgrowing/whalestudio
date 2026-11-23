import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingLinearEquivUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterAndTranslationCoordsSurjectiv
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

noncomputable section

namespace GlobalTheory.DoubledFlatDiag

theorem flatOf_diag : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ → 1 ≤ d →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K →
    ∀ φ₀ ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K χX (((n : ℂ) - (d : ℂ)) / 2),
    (∀ s : ℂ, (d : ℝ) / 2 < s.re →
        GlobalTheory.AutomorphicL2Unitary.LeftInv ((siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) ⊓ ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) ∧
        ∀ g, GlobalTheory.Eis.CosetConv (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) g) →
    ∀ μ : Measure (UA σ W.J), μ.IsHaarMeasure →
    ∀ (s : ℂ) (h : UA σ W.J) (y : UA σ W₂.J),
      (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) (i (h, h) * y) = ((χX (Matrix.GeneralLinearGroup.det h.1) : Circle) : ℂ) * (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) y := by
  intro _ F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP _ W₂ _ _ _ i hi K _ hIw φ₀ hφ₀ _ μ _ s h y
  have hJ : W.J.det ≠ 0 := GlobalTheory.FlipOnto.det_ne_zero_of_isSkew hP.skew
  have hiP : ∀ h : UA σ W.J, i (h, h) ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype := fun h => by
    rw [mem_siegelOf]
    change KeepsDiag finSumFinEquiv (mat (i (h, h)))
    rw [hi]
    exact (keepsDiag_blkMat finSumFinEquiv).2 rfl
  have haOf : ∀ h : UA σ W.J, aOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype ⟨i (h, h), hiP h⟩ =
      Matrix.GeneralLinearGroup.det h.1 := fun h => by
    apply Units.ext
    rw [val_aOf]
    change (leviMat finSumFinEquiv (mat (i (h, h)))).det = _
    rw [hi, leviMat_blkMat]
    rfl
  have hδ1 : ∀ h : UA σ W.J,
      absAOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) ⟨i (h, h), hiP h⟩ = 1 := fun h => by
    change absE F E (aOf _ _ _) = 1
    rw [haOf]
    exact GlobalTheory.LeviModulus.CharVec.absE_det_eq_one σ hJ h
  have hl : IndLaw (absAOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E))
      (χX.comp (aOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype))
      (((n : ℂ) - (d : ℂ)) / 2 + (Fintype.card (Fin d) : ℂ) / 2) φ₀ := ((mem_degPSOf).1 hφ₀).1
  have := (IsIwasawa.indLaw_flatSec hIw hl s) ⟨i (h, h), hiP h⟩ y
  rw [hδ1, GlobalTheory.Doubling.npow, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, mul_one] at this
  change flatSec _ _ _ _ _ _ = _ * flatSec _ _ _ _ _ _
  rw [this, MonoidHom.comp_apply, haOf]

end GlobalTheory.DoubledFlatDiag
