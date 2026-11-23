import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmulOfMemFlagSubOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl GlobalTheory.LatPair
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FinPl.CoreMat

theorem mt_emb_mulVec_ratV_vecB {D : D7} {ρ : ℕ} (B : BesLev D ρ) (κ : GA D B.A) :
    mt B.V₀ (B.o.emb (κ, 1)) *ᵥ ratV (vecB B.o B.ζ) = ratV (vecB B.o B.ζ) := by
  have hv : ratV (vecB B.o B.ζ) = B.o.jB *ᵥ ratV B.ζ :=
    funext fun i => RingHom.map_mulVec (incA D) B.o.iB B.ζ i
  have hB : mt B.V₀ (B.o.emb (κ, 1)) ⬝ B.o.jB = B.o.jB := by
    rw [B.o.emb_jB]
    have h1 : mt B.L (1 : GA D B.L) = 1 := by simp [Formalism.L2.Theta.mt]
    rw [h1, Matrix.mul_one]
  rw [hv, Matrix.mulVec_mulVec, hB]

theorem coreMat : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : GlobalTheory.FinPl.SplitPt D k} {n : Type} [Fintype n] [DecidableEq n] {ρ : ℕ} (B : BesLev D ρ) (β : GlobalTheory.FinPl.Frame p B.A n) (β₀ : GlobalTheory.FinPl.Frame p B.V₀ (n ⊕ Fin 1)), GlobalTheory.FinPl.IsSumFrame B.o B.ζ β β₀ → ∀ (κ : GA D B.A) (g : GL n k), (mt B.A κ).map p.pr = β.b * g.val * β.b' → (mt B.V₀ (B.o.emb (κ, 1))).map p.pr = β₀.b * (GlobalTheory.RootEx.embX 1 g).val * β₀.b' := by
  intro D k _ _ _ _ p n _ _ ρ B β β₀ hS κ g hg
  have hA : mt B.V₀ (B.o.emb (κ, 1)) ⬝ B.o.jA = B.o.jA ⬝ mt B.A κ := B.o.emb_jA κ 1
  have hv := mt_emb_mulVec_ratV_vecB B κ
  have key : (mt B.V₀ (B.o.emb (κ, 1))).map p.pr * β₀.b = β₀.b * (GlobalTheory.RootEx.embX 1 g).val := by
    rw [hS]
    have hX : ((GlobalTheory.RootEx.embX 1 g).val : Matrix (n ⊕ Fin 1) (n ⊕ Fin 1) k) = fromBlocks g.val 0 0 1 := rfl
    rw [hX]
    rw [Matrix.mul_fromCols, fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, Matrix.mul_zero, zero_add,
      Matrix.mul_one]
    congr 1
    · rw [← Matrix.mul_assoc, ← Matrix.map_mul, hA, Matrix.map_mul, Matrix.mul_assoc, hg, Matrix.mul_assoc,
        Matrix.mul_assoc, Matrix.mul_assoc, β.b'b, Matrix.mul_one]
    · ext i j
      have := congrFun hv i
      simp only [Matrix.mul_apply, replicateCol_apply, Matrix.map_apply, ← map_mul, ← map_sum]
      rw [← this]
      rfl
  calc (mt B.V₀ (B.o.emb (κ, 1))).map p.pr
      = (mt B.V₀ (B.o.emb (κ, 1))).map p.pr * β₀.b * β₀.b' := by rw [Matrix.mul_assoc, β₀.bb', Matrix.mul_one]
    _ = β₀.b * (GlobalTheory.RootEx.embX 1 g).val * β₀.b' := by rw [key]

end GlobalTheory.FinPl.CoreMat

end
