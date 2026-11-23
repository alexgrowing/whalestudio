import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.StageGeoDefs
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AutomorphicArithmetic.DivisorFrames.ExistsMaxCompactEqFrameGramSplitBasis
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_splitBasis_conj_lattice_of_selfDual_frame :
    ∀ (D : D7) (S : HSp D) (Λ L : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (β : GL (Fin S.rank) (EAf D)),
        IsSelfDualC S Λ → Formalism.L2.DIV.IsFrame β Λ → (∀ y, y ∈ L ↔ star y ∈ Λ) →
        ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (t : D.host.E →ₐ[D.host.F] Fv D.host.F v), ∃ b : GL (Fin S.rank) (Fv D.host.F v),
          IsSplitBasis t L b ∧ IsSplitBasis t L (-b) ∧ (b⁻¹).1 = (S.gram.map t * β.1.map (evW t))ᵀ := by
  intro D S Λ L β hΛ hβ hL v t
  obtain rfl : L = GlobalTheory.TripleSpaceW.conjSub Λ := by
    ext y
    rw [hL, GlobalTheory.TripleSpaceW.mem_conjSub]
  haveI := GlobalTheory.TripleSpaceW.conjSub_isLattice hΛ.1
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.AdelicU.exists_isSplitBasis t (GlobalTheory.TripleSpaceW.conjSub Λ) (GlobalTheory.AdelicU.isCMExt_host D)
  obtain ⟨g, hg, hgv⟩ := UpperTheory.exists_maxCompact_eq_frame_gram_splitBasis D S Λ β hΛ hβ v t b₀ hb₀
  rw [← (GlobalTheory.AdelicU.GLint_eq_KO_and_princ_eq_KOne v S.rank).1] at hg
  have h1 : IsSplitBasis t (GlobalTheory.TripleSpaceW.conjSub Λ) (b₀ * g⁻¹) := by
    rw [hb₀.iff_mem_GLint, inv_mul_cancel_left]
    exact inv_mem hg
  refine ⟨b₀ * g⁻¹, h1, fun u => ?_, ?_⟩
  · have := h1 (-u)
    simp only [Pi.neg_apply, neg_mem_iff, Matrix.mulVec_neg] at this
    rw [Units.val_neg, Matrix.neg_mulVec, neg_mem_iff]
    exact this
  · rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, hgv, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one,
      Matrix.transpose_mul]
