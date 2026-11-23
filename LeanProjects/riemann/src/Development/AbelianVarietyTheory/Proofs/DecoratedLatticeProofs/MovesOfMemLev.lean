import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGLEmbeddingUnitaryAdelicSplitPlaceBasis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizesSelfDualIffFrameMatrixStabilizesStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section
namespace GlobalTheory.SeeSaw.LevMoves

section
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mulVec_sec (q : SplitPt D k) {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)) (y : Fin n → k) :
    M *ᵥ (fun i => q.sec (y i)) = fun i => q.sec ((M.map q.pr *ᵥ y) i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := q.sec_pr (M i j * q.sec (y j))
  rw [RingHom.map_mul, q.pr_sec, mul_left_comm, ← GlobalTheory.FrameGlob.sec_eq_mul] at h
  exact h.symm

theorem isLat_moved (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP) (S : HSp D)
    (Λ L : Lat S) (β : GL (Fin S.rank) (Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β Λ) (t : GA D S)
    (ht : Moves S t Λ L (· = q.v)) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (bas : GL Y k)
    (σ : Fin S.rank ≃ Y) (hM : GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) S t β ((F.β * bas.val).submatrix id σ))
    (x : Y → k) : x ∈ GlobalTheory.StepData.latOf bas ↔ (fun i => q.sec ((F.β *ᵥ x) i)) ∈ latV S L (· = q.v) := by
  obtain ⟨B, hB, hl⟩ := GlobalTheory.LocMod.PinEx.exists_topFrame q hq S Λ β hβ
  have hs : Function.Surjective (toEAf D) := by
    refine (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).surjective.comp ?_
    exact Algebra.TensorProduct.map_surjective _ _ (fun α => ⟨pairA _ 0 α, rfl⟩) Function.surjective_id
  choose f hf using hs
  have e : (β.val.map f).map (toEAf D) = β.val := by ext i j; exact hf _
  have h1 := hB _ e
  have h2 := hM _ e
  rw [GlobalTheory.MixModel.mt_one, Matrix.one_mul] at h1
  rw [Matrix.map_mul, h1] at h2
  have h3 : (mt S t).map q.pr *ᵥ (B.val *ᵥ fun i => ((bas⁻¹).val *ᵥ x) (σ i)) = F.β *ᵥ x := by
    rw [Matrix.mulVec_mulVec]
    refine (congrArg (· *ᵥ _) h2).trans ?_
    have : (fun i => ((bas⁻¹).val *ᵥ x) (σ i)) = ((bas⁻¹).val *ᵥ x) ∘ σ := rfl
    rw [this, Matrix.submatrix_mulVec_equiv, Function.comp_id, Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [← h3, ← mulVec_sec, ← ht _ fun i => GlobalTheory.FrameGlob.sec_mem_idAt q _, hl, Matrix.mulVec_mulVec, Units.inv_mul,
    Matrix.one_mulVec, GlobalTheory.StepData.mem_latOf]
  exact ⟨fun h i => h _, fun h i => by simpa using h (σ.symm i)⟩

theorem smul_latOf {Y : Type} [Fintype Y] [DecidableEq Y] {bas g : GL Y k} (h : g ∈ GlobalTheory.StepData.stabLat bas) :
    g • GlobalTheory.StepData.latOf bas = GlobalTheory.StepData.latOf bas := by
  have h1 := GlobalTheory.StepData.mem_stabLat_iff.1 h
  ext y
  conv_rhs => rw [← h1]
  change (∃ x, x ∈ GlobalTheory.StepData.latOf bas ∧ g • x = y) ↔ _
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (GlobalTheory.StepData.mulVec_mem_latOf g).2 hx
  · intro hy
    refine ⟨g⁻¹ • y, (GlobalTheory.StepData.mulVec_mem_latOf g).1 ?_, smul_inv_smul _ _⟩
    have : g.val *ᵥ (g⁻¹ • y) = y := smul_inv_smul g y
    rwa [this]

end

end GlobalTheory.SeeSaw.LevMoves
end
