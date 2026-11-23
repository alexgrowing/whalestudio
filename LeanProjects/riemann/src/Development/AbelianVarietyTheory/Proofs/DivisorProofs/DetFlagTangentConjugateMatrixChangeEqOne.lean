import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockChangeOfBasisViaTwoFamiliesImplicit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieCombIffIsCombAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalRingPointDualNumberSndLinearDerivation
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.KSChgDet

theorem ksChg_single_eq_blockDiagonal' {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (K : Type) [Field K] (Φ : Finset (E →+* ℂ))
    (g : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K) (k l : HIx Dw Φ) :
    FlagTan.ksChg Φ g ((Pi.single l 1 : HIx Dw Φ → K)) k =
      Matrix.blockDiagonal' (fun τ : Φ => Matrix.kroneckerMap (· * ·)
        (g (conjEmb τ.1)).transpose (g τ.1).transpose) k l := by
  obtain ⟨τ, a, b⟩ := k
  obtain ⟨τ', a', b'⟩ := l
  rw [FlagTan.ksChg_apply]
  by_cases h : τ = τ'
  · subst h
    rw [Matrix.blockDiagonal'_apply_eq]
    simp [Matrix.kroneckerMap_apply, Pi.single_apply, Sigma.mk.inj_iff, ite_and]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    simp [Pi.single_apply, Sigma.mk.inj_iff, h]

theorem det_ksChg_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (K : Type) [Field K] (g : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) K),
    (∀ σ, (g σ).det = 1) → ∀ (o : Fin Dw.dim ≃ HIx Dw (psiSet H)),
    (Matrix.of fun i j => FlagTan.ksChg (psiSet H) g ((Pi.single (o j) 1 : HIx Dw (psiSet H) → K)) (o i)).det = 1 := by
  intro E _ _ _ H Dw K _ g hg o
  have hM : (Matrix.of fun i j => FlagTan.ksChg (psiSet H) g ((Pi.single (o j) 1 : HIx Dw (psiSet H) → K)) (o i)) =
      (Matrix.blockDiagonal' (fun τ : psiSet H => Matrix.kroneckerMap (· * ·)
        (g (conjEmb τ.1)).transpose (g τ.1).transpose)).submatrix o o := by
    ext i j
    exact ksChg_single_eq_blockDiagonal' K (psiSet H) g (o i) (o j)
  rw [hM, Matrix.det_submatrix_equiv_self, GlobalTheory.Div.BlockChangeDet.det_blockDiagonal'_eq_prod]
  simp [Matrix.det_kronecker, Matrix.det_transpose, hg]

end GlobalTheory.KSChgDet
