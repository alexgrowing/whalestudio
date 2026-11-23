import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.TensCastR
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.principalLevelFrame GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.R3.RowFrameParts

theorem main : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A3.A Ks) (F : Face D A3.A) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R F X0), StdPsi Y.hF Y.PY ∧ ∀ σ, R.HE.e (Y.eE (D.what₂.onb σ)) ∈ isotE R.θ Y.PY (R.MY 0) (JR R F) (chiR R F) R.e0 (rowRepR R.θ (Y.eFT (D.what₂.ft σ))) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F X0 Y
  refine ⟨Y.stdPsi.1, fun σ => ?_⟩
  have h := Y.tied.sharp.ft σ
  have h1 := Y.prtE (D.what₂.ft σ)
  have h2 := Y.eE_read (D.what₂.onb σ)
  have h3 := h1 ▸ h
  obtain ⟨z, hz, hze⟩ := h3
  rw [h2] at hze
  have : z = R.HE.e (Y.eE (D.what₂.onb σ)) := LinearEquiv.injective _ hze
  rw [← this]
  exact hz

end GlobalTheory.Mem.R3.RowFrameParts
