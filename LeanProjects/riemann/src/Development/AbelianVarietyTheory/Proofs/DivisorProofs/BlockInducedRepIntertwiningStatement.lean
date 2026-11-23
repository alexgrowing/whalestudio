import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockInducedRepIntertwining
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_induced_rep_intertwining : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α β : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] [DecidableEq β]
    {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
    {c : β → α → Type} [∀ j i, Fintype (c j i)] [∀ j i, DecidableEq (c j i)]
    (g : ∀ j, (Σ i, c j i) ≃ m' j) {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (∀ j, GlobalTheory.SmGL.Levi k (c j)) W) (ψ : (∀ j, GlobalTheory.SmGL.Levi k (c j)) →* ℂˣ),
    (∀ z w, τ z w = (ψ z : ℂ) • w) → ∀ (j₀ : β) (ν : GlobalTheory.SmGL.Levi k m' →* ℂˣ)
    (s : GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind (GlobalTheory.SmGL.relParab k g)
      ((GlobalTheory.SmGL.twist τ (GlobalTheory.SmGL.relDeltaHalf k c)).comp (GlobalTheory.SmGL.relProj k g)))),
    ∃ (ι : Type) (_ : Fintype ι) (y : ι → ∀ j, GL (m' j) k) (l : ι → Module.Dual ℂ W)
      (R : Subrepresentation ((GlobalTheory.SmGL.twist (GlobalTheory.SmGL.relInd g τ) ν).comp (MonoidHom.mulSingle (fun j => GL (m' j) k) j₀))),
      s ∈ R.toSubmodule ∧ ∀ F ∈ R.toSubmodule,
        (∀ i x, l i (F.1.1 (Function.update (y i) j₀ x)) = 0) → F = 0 := by
  first | exact @GlobalTheory.ColumnSep.exists_sub_evals_injective | exact GlobalTheory.ColumnSep.exists_sub_evals_injective | (intros; apply GlobalTheory.ColumnSep.exists_sub_evals_injective <;> assumption)
