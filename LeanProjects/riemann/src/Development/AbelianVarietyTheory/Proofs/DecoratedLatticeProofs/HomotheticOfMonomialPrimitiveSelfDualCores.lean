import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastIsotropicLineHomothetyMatchesLatticesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrimitiveCharacterMatchesLinesDownFlagStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneMatchesIsotropicYOfMatchesIsotropicXStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

theorem homothetic_of_monomial_primitive_selfDual_cores : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (z : Fin S₀.rank → D.host.E) (L L' : Lat S) (M M' : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (c : AE D) (γ : GA D S₀), IsSelfDualC S L → IsSelfDualC S L' → IsSelfDualC S₀ M → z ≠ 0 → MonoAt d L M v → MonoAt d L' M' v → PrimAt ψ d L v → PrimAt ψ d L' v → LastAt ψ d z L M v → LastAt ψ d z L' M' v → NormOneAt v c → Formalism.L2.Theta.mt S₀ γ *ᵥ ratV z = ratV z → SMoves S₀ c γ M M' v → SMoves S c (d.emb0 γ) L L' v := by
  intro D ψ S S₀ ρ d z L L' M M' v c γ hL hL' hM hz hmL hmL' hpL hpL' hlL hlL' hc hγ hmv
  have hX : ∀ i : Fin ρ, ∀ a ∈ idAt D (· = v),
      (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v)) := by
    suffices h : ∀ k : ℕ, ∀ i : Fin ρ, i.1 + k + 1 = ρ → ∀ a ∈ idAt D (· = v),
        (colMul d.jX i a ∈ latV S L (· = v) ↔ colMul d.jX i (c * a) ∈ latV S L' (· = v)) by
      intro i
      exact h (ρ - 1 - i.1) i (by omega)
    intro k
    induction k with
    | zero =>
      intro i hi
      exact GlobalTheory.T.lastIsotropicLine_homothety_matches_lattices D ψ S S₀ ρ d z L L' M M' v c γ hM hz hlL hlL' hc hγ hmv i (by omega)
    | succ k ih =>
      intro i hi
      exact GlobalTheory.T.primitive_character_matches_lines_down_flag D ψ S S₀ ρ d L L' v c hL hpL hpL' hc i ⟨i.1 + 1, by omega⟩ rfl
        (ih ⟨i.1 + 1, by omega⟩ (by simp only; omega))
  have hY := GlobalTheory.T.normOne_matchesIsotropicY_of_matchesIsotropicX D S S₀ ρ d L L' M M' v c hL hL' hmL hmL' hc hX
  intro y hy
  have hpX : d.pX *ᵥ (c • (Formalism.L2.Theta.mt S (d.emb0 γ) *ᵥ y)) = c • (d.pX *ᵥ y) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding]
  have hpY : d.pY *ᵥ (c • (Formalism.L2.Theta.mt S (d.emb0 γ) *ᵥ y)) = c • (d.pY *ᵥ y) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, d.wittDecomp_projY_anisotropicEmbedding]
  have hp0 : d.p0 *ᵥ (c • (Formalism.L2.Theta.mt S (d.emb0 γ) *ᵥ y)) =
      c • (Formalism.L2.Theta.mt S₀ γ *ᵥ (d.p0 *ᵥ y)) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_anisotropicEmbedding, ← Matrix.mulVec_mulVec]
  rw [hmL y, hmL' _, hpX, hpY, hp0]
  refine and_congr (forall_congr' fun i => ?_) (and_congr (forall_congr' fun i => ?_) ?_)
  · rw [Pi.smul_apply, smul_eq_mul]
    exact hX i _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy i)
  · rw [Pi.smul_apply, smul_eq_mul]
    exact hY i _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy i)
  · exact hmv _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy)

end GlobalTheory.Core.Mi.LatMatch
