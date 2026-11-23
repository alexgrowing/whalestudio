import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ComplEquivEvW
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedLagrangianChartIntegralRowChange
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_maxCompact_eq_frame_gram_splitBasis :
    ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (β : GL (Fin S.rank) (Lev.EAf D)),
        IsSelfDualC S Λ → Formalism.L2.DIV.IsFrame β Λ → ∀ (v : Pl D.host.F) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
        (b : GL (Fin S.rank) (Fv D.host.F v)), IsSplitBasis τ (GlobalTheory.TripleSpaceW.conjSub Λ) b →
        ∃ g ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) (Fin S.rank),
          g.val = (β.val.map (GlobalTheory.BotMatch.evW τ))ᵀ * (S.gram.map τ)ᵀ * b.val := by
  intro D S Λ β hΛ hβ v τ b hb
  have hJ := GlobalTheory.Doubling.isHermND_gram S
  have hL := GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hΛ v
  have h1 := GlobalTheory.FlipMatch.RowChart.isSplitBasis_conj τ
    (GlobalTheory.FlipMatch.RowChart.isFrameAt_loc hβ (splitPrime τ))
  have e : ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F v,
      splitLat (t.comp D.sp.cm.sig) (GlobalTheory.TripleSpaceW.conjSub Λ) = splitLat t Λ := fun t => by
    refine le_antisymm (GlobalTheory.FlipMatch.RowChart.splitLat_le fun x hx => ⟨star x, hx, fun i => rfl⟩)
      (GlobalTheory.FlipMatch.RowChart.splitLat_le fun x hx => ⟨star x, ?_, fun i => ?_⟩)
    · rw [GlobalTheory.TripleSpaceW.mem_conjSub, star_star]; exact hx
    · change t (x i) = t (star (star (x i)))
      rw [star_star]
  have e2 := e (τ.comp D.sp.cm.sig)
  rw [comp_conj_conj (isCMExt_host D)] at e2
  set β' := GeneralLinearGroup.map (complEquiv τ (splitPrime_under τ)).symm.toRingHom (loc (splitPrime τ) β) with hβ'
  have hv : β'.val = β.val.map (GlobalTheory.BotMatch.evW τ) := rfl
  have h2 : IsSplitBasis τ Λ β' := fun u => by rw [← e τ]; exact h1 u
  have h3 : IsSplitBasis (τ.comp D.sp.cm.sig) Λ b := fun u => by rw [← e2]; exact hb u
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : GL (Fin S.rank) (Fv D.host.F v), g₀.val = b.valᵀ * S.gram.map τ * β'.val :=
    ⟨dualConj 1 b⁻¹ * splitGram hJ τ * β', by
      rw [Units.val_mul, Units.val_mul, dualConj_one_val, inv_inv, splitGram_val]⟩
  obtain ⟨k1, k2⟩ := GlobalTheory.FlipMatch.RowChart.pairing_int (isCMExt_host D) hJ hL h2 h3 hg₀
  refine ⟨dualConj 1 g₀⁻¹, ?_, ?_⟩
  · rw [← (GLint_eq_KO_and_princ_eq_KOne v S.rank).1, mem_GLint_iff, ← map_inv, dualConj_one_val, dualConj_one_val,
      inv_inv]
    exact ⟨fun i j => k1 j i, fun i j => k2 j i⟩
  · rw [dualConj_one_val, inv_inv, hg₀, hv, transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]
