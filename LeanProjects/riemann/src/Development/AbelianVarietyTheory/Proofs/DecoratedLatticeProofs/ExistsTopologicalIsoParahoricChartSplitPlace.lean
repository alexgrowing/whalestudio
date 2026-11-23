import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnrOffOne
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

namespace GlobalTheory.ChartSplitIso

variable {D : D7}

def projEmb {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) : D.host.E →ₐ[D.host.F] Fv D.host.F v :=
  (φ.restrictScalars D.host.F).comp Algebra.TensorProduct.includeRight

theorem splitProj_projEmb {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v)
    (x : Fv D.host.F v ⊗[D.host.F] D.host.E) : GlobalTheory.AdelicU.splitProj (projEmb φ) x = φ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    have e : (a ⊗ₜ[D.host.F] x : Fv D.host.F v ⊗[D.host.F] D.host.E) = a • ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [GlobalTheory.AdelicU.splitProj_tmul, e, map_smul, smul_eq_mul]
    rfl

def reindexGL {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (K : Type) [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] (ε : ι ≃ κ) : GL κ K ≃ₜ* GL ι K where
  toMulEquiv := Units.mapEquiv (Matrix.reindexAlgEquiv K K ε.symm).toMulEquiv
  continuous_toFun := Units.continuous_iff.2
    ⟨(Units.continuous_val).matrix_submatrix _ _, (Units.continuous_coe_inv).matrix_submatrix _ _⟩
  continuous_invFun := Units.continuous_iff.2
    ⟨(Units.continuous_val).matrix_submatrix _ _, (Units.continuous_coe_inv).matrix_submatrix _ _⟩

theorem reindexGL_val {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (K : Type) [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] (ε : ι ≃ κ) (x : GL κ K) : (reindexGL K ε x).1 = x.1.submatrix ε ε := rfl

theorem grpCo_eq {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : SplitProj D v) (V : HSp D)
    (hJ : IsHermND D.sp.cm.sig V.gram) (B : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    grpCo φ V B g = GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) hJ (projEmb φ) B
      (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g) := by
  refine Units.ext ?_
  rw [GlobalTheory.AdelicU.splitEquivIn_apply]
  simp only [grpCo, Units.val_mul]
  congr 2
  exact Matrix.ext fun i j => (splitProj_projEmb φ _).symm

end GlobalTheory.ChartSplitIso

namespace GlobalTheory.ChartSplitIso

theorem exists_equiv_emb : ∀ (D : D7) (s : PiLocalization₂ D) (k : ℕ) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v)
    (ι : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) →* GA D s.V), IsSelfDualC s.V s.Λ → Formalism.L2.DIV.IsFrame s.β s.Λ →
    IsChart s k φ ι → ∃ e : GL (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v) ≃ₜ* GlobalTheory.FinZeta.Gv s.V v,
      ∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y) := by
  intro D s k v φ ι _ _ hι
  obtain ⟨ε, -, hε⟩ := hι
  have hJ : IsHermND D.sp.cm.sig s.V.gram := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 s.V
  let Ψ := GlobalTheory.AdelicU.splitEquivIn (GlobalTheory.AdelicU.isCMExt_host D) hJ (projEmb φ) (frCo φ s.β)
  refine ⟨(reindexGL (Fv D.host.F v) ε).symm.trans Ψ.symm, fun y => (hε y).1.symm.trans ?_⟩
  change GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v (ι y)) = _
  congr 1
  apply Ψ.injective
  apply (reindexGL (Fv D.host.F v) ε).injective
  refine Units.ext ?_
  rw [reindexGL_val, ContinuousMulEquiv.trans_apply, ContinuousMulEquiv.apply_symm_apply,
    ContinuousMulEquiv.apply_symm_apply, ← (hε y).2, grpCo_eq φ s.V hJ]

end GlobalTheory.ChartSplitIso

end
