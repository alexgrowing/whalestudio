import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentationSigmaEquivReindex
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
theorem _root_.GlobalTheory.T.representation_sigma_equiv_reindex : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α β : Type} [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] [DecidableEq β]
    {m' : β → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
    {c : β → α → Type} [∀ j i, Fintype (c j i)] [∀ j i, DecidableEq (c j i)]
    (g : ∀ j, (Σ i, c j i) ≃ m' j) {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (∀ j, GlobalTheory.SmGL.Levi k (c j)) W) (ψ : (∀ j, GlobalTheory.SmGL.Levi k (c j)) →* ℂˣ),
    (∀ z w, τ z w = (ψ z : ℂ) • w) → ∀ (j₀ : β) (ν : GlobalTheory.SmGL.Levi k m' →* ℂˣ)
    {W' Vy : Type} [AddCommGroup W'] [Module ℂ W'] [AddCommGroup Vy] [Module ℂ Vy]
    (Q : Representation ℂ (GL (m' j₀) k) W') (Y : Representation ℂ (GL (m' j₀) k) Vy),
    GlobalTheory.SmGL.IsSubquotient Q
      ((GlobalTheory.SmGL.twist (GlobalTheory.SmGL.relInd g τ) ν).comp (MonoidHom.mulSingle (fun j => GL (m' j) k) j₀)) →
    ∀ F : Q.IntertwiningMap Y, F ≠ 0 →
    ∃ (V' : Type) (_ : AddCommGroup V') (_ : Module ℂ V') (Q' : Representation ℂ (GL (m' j₀) k) V'),
      GlobalTheory.SmGL.IsSubquotient Q' (GlobalTheory.SmGL.twist (GlobalTheory.SmGL.parInd (g j₀)
        (GlobalTheory.SmGL.ofChar (ψ.comp (MonoidHom.mulSingle (fun j => GlobalTheory.SmGL.Levi k (c j)) j₀))))
        (ν.comp (MonoidHom.mulSingle (fun j => GL (m' j) k) j₀))) ∧
      ∃ F' : Q'.IntertwiningMap Y, F' ≠ 0 := by
  first | exact @GlobalTheory.CellColumn.exists_subquotient_column | exact GlobalTheory.CellColumn.exists_subquotient_column | (intros; apply GlobalTheory.CellColumn.exists_subquotient_column <;> assumption)
