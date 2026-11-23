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

theorem GlobalTheory.MiStar.normLast_valuation : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (q : GlobalTheory.LatPair.Unif k) (S A L : HSp D) (o : OrthDec S A L), 0 < S.rank → S.gram = 1 → ∀ (ζ : Fin L.rank → D.host.E) (π : D.host.E), (∀ r : Fin S.rank, vecB o ζ r = if r.1 + 1 = S.rank then π else 0) → valuation k (p.pr (incA D π)) = valuation k ((q.1 : 𝒪[k]) : k) → valuation k (p.pr (incA D (star π))) = 1 → valuation k (p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ))) = valuation k ((q.1 : 𝒪[k]) : k) := by
  intro D k _ _ _ _ p q S A L o hpos hS ζ π hv h1 h2
  have key : star ζ ⬝ᵥ L.gram *ᵥ ζ = star π * π := by
    have hB := o.isoB
    rw [hS, Matrix.mul_one] at hB
    rw [← hB, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    have hfun : o.iB *ᵥ ζ = fun r : Fin S.rank => if r.1 + 1 = S.rank then π else 0 := by
      funext r; exact hv r
    rw [hfun]
    let r0 : Fin S.rank := ⟨S.rank - 1, by omega⟩
    have hr : ∀ r : Fin S.rank, (r.1 + 1 = S.rank) ↔ r = r0 := by
      intro r; constructor
      · intro h; ext; simp [r0]; omega
      · intro h; subst h; simp [r0]; omega
    simp only [dotProduct, Pi.star_apply, hr]
    simp [apply_ite star]
  rw [key, map_mul, map_mul, map_mul, h2, h1, one_mul]
