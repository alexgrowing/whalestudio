import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemCuspFormsIffAutomorphicCompact
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct nonZeroDivisors ComplexConjugate

namespace GlobalTheory.ReLatPf

variable {D : D7}

theorem theta_relat (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (r : ReLat A) (r' : ReLat B) (f : WO A B → ℂ) :
    IsThetaFunO ψ r.sp r'.sp f ↔ IsThetaFunO ψ A B f := ⟨fun h => ⟨h.1,h.2,h.3,h.4⟩, fun h => ⟨h.1,h.2,h.3,h.4⟩⟩

theorem aut_relat (V : HSp D) (r : ReLat V) (θ : InfFam D) (φ : GA D V → ℂ) : IsAutFunSm θ r.sp φ ↔ IsAutFunSm θ V φ :=
  ⟨fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩,
   fun h => ⟨⟨h.left, h.level, h.cont⟩, h.smooth, h.zfin, h.growth⟩⟩

theorem reLatLaw_holds : ∀ D : D7, ReLatLaw D := by
  intro D
  refine ⟨fun V Λ h => ⟨⟨_, GlobalTheory.Core.Rk.DownCompare.latIn_lat h, GlobalTheory.Core.Rk.DownCompare.latIn_unimod h⟩,
      GlobalTheory.Core.Rk.DownCompare.frameLat_reset V Λ h V.sig⟩,
    fun V r θ S M J => ⟨?_, rfl, rfl, rfl, fun _ => Iff.rfl⟩, fun ψ A B r r' => ⟨theta_relat ψ A B r r', fun χS χT ω => ?_⟩⟩
  · have e : (Mult θ (r.mod M) J 1 : Submodule ℂ (MMap M)) = Mult θ M J 1 := by
      unfold Mult
      congr 1
      ext T
      exact ⟨fun h => ⟨fun v => (aut_relat V r θ _).1 (h.1 v), h.2, h.3, h.4, h.5⟩,
        fun h => ⟨fun v => (aut_relat V r θ _).2 (h.1 v), h.2, h.3, h.4, h.5⟩⟩
    exact congrArg (Submodule.map (PiTensorProduct.lift : MMap M ≃ₗ[ℂ] _).toLinearMap) e
  · have t := theta_relat ψ A B r r'
    exact ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, fun p f hf => (t _).1 (h.6 p f ((t _).2 hf)),
        fun g k w f hf => h.7 g k w f ((t _).2 hf), fun γ a γ' b f hf => h.8 γ a γ' b f ((t _).2 hf),
        fun f hf => h.9 f ((t _).2 hf), fun μ X a b p f hf => h.10 μ X a b p f ((t _).2 hf),
        fun e he g k a b x y c d => (h.11 e he g k a b x y c d).imp fun _ hr => ⟨hr.1, fun l hl f hf =>
          hr.2 l (fun u hu f hf => hl u hu f ((t _).1 hf)) f ((t _).2 hf)⟩⟩,
      fun h => ⟨h.1, h.2, h.3, h.4, h.5, fun p f hf => (t _).2 (h.6 p f ((t _).1 hf)),
        fun g k w f hf => h.7 g k w f ((t _).1 hf), fun γ a γ' b f hf => h.8 γ a γ' b f ((t _).1 hf),
        fun f hf => h.9 f ((t _).1 hf), fun μ X a b p f hf => h.10 μ X a b p f ((t _).1 hf),
        fun e he g k a b x y c d => (h.11 e he g k a b x y c d).imp fun _ hr => ⟨hr.1, fun l hl f hf =>
          hr.2 l (fun u hu f hf => hl u hu f ((t _).2 hf)) f ((t _).1 hf)⟩⟩⟩

end GlobalTheory.ReLatPf

end
