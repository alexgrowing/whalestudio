import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SphericalSectionOfMemCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKillingImpliesVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKillWittDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MajorantExistsAndWittDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilizeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaMajorantAverageIdentityStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section
namespace GlobalTheory.Core.Rk.ResKill

theorem dblInt_smul_left {D : D7} {V : HSp D} {μ : (AE D)ˣ →* Circle} {m : Measure (GA D V)} (c : ℂ)
    (E : GA D (dblSp V) → ℂ) (f : GA D V → ℂ) :
    GlobalTheory.Eis.dblInt V μ m (c • E) f f = c * GlobalTheory.Eis.dblInt V μ m E f f := by
  have h := GlobalTheory.Eis.dblInt_smul (V := V) (μ := μ) (m := m) (E := E) (f₁ := f) (f₂ := f) c 1 1
  simpa using h

theorem res_killed : GlobalTheory.Published.RegularisedSiegelWeilFirstTerm → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → (∀ v : FinPl D, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) → ∀ (B W : HSp D) (t : ℕ) (_ : HypDec B W t), HSpace.SigOK B → HSpace.SigOK W → 0 < W.rank → 0 < t → A.rank = W.rank + t → ∀ (χ : (AE D)ˣ →* Circle) (omB : WRep (dblSp A) B) (omW : WRep (dblSp A) W), IsWeilDatumO ψ (dblSp A) B 1 χ omB → IsWeilDatumO ψ (dblSp A) W 1 χ omW → ∀ ν 𝓕, IsCovolOne (ratL B A) ν 𝓕 → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) → Kills ψ χ omW m u → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → IsKFinVec omB (Khat A a) φ → GlobalTheory.Eis.EisPoleLE A (flat A a (swSec A B omB ν 𝓕 φ) (sZero A B)) (sZero A B) 1 ∧ ∃ E₁, GlobalTheory.Eis.EisCoeffAt A (flat A a (swSec A B omB ν 𝓕 φ) (sZero A B)) (sZero A B) (-1) E₁ ∧ GlobalTheory.Eis.dblInt A χ⁻¹ m E₁ (fun g => conj (u g)) (fun g => conj (u g)) = 0 := by
  intro hPr D ψ θ A cA a hDef h2 B W t d hsB hsW hW ht hA χ omB omW hWB hWW ν 𝓕 hcov m hm u hu hinv hK φ hφ hKφ
  obtain ⟨b, hb⟩ := GlobalTheory.RegSW.Model.exists_isMaj B
  obtain ⟨νK, hνH, hνP⟩ := GlobalTheory.RegSW.Model.exists_haar_Kmax B b
  obtain ⟨μ₁, 𝓕₁, hμ₁⟩ := GlobalTheory.MixModel.exists_isCovolOne D t (dblSp A).rank
  have hrk := d.rank_add
  have hIwA : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a hDef.maj
  have hIwB : HasIw d (Kmax B b) := GlobalTheory.T.adelic_iwasawa_decomposition_wittIsotropicStabilizer D B W t d b h2 hb
  obtain ⟨hP1, hP2, hP3, hP4⟩ := hPr D ψ A B W t d (by omega) (by omega) hW χ omB omW hWB hWW a b hDef.maj hb hIwA hIwB
    ν 𝓕 hcov μ₁ 𝓕₁ hμ₁ νK hνH hνP Measure.haar inferInstance
  have hproj : ∀ φ, IsThetaFunO ψ (dblSp A) B φ → IsThetaFunO ψ (dblSp A) B (projK omB νK φ) := fun φ h => (hP1 φ h).1
  have hφ' : IsThetaFunO ψ (dblSp A) W (ikeda ψ d μ₁ 𝓕₁ (projK omB νK φ)) := (hP1 _ (hproj φ hφ)).2
  have hKφ' : IsKFinVec omW (Khat A a) (ikeda ψ d μ₁ 𝓕₁ (projK omB νK φ)) :=
    (GlobalTheory.T.theta_majorant_average_identity D ψ (dblSp A) B W t d 1 χ omB omW hWB hWW b hb νK hνP μ₁ 𝓕₁ hμ₁ hproj).2 (Khat A a) φ hφ hKφ
  refine ⟨hP2 φ hφ hKφ, ?_⟩
  obtain ⟨-, hWitt⟩ := GlobalTheory.T.majorant_exists_and_witt_decomposition D W hsW
  rcases hWitt with hAn | ⟨W₀, r', d₀, hAn₀, hr'⟩
  · obtain ⟨hconv, κ, -, hE⟩ := hP3 hAn
    refine ⟨_, hE φ hφ hKφ, ?_⟩
    rw [dblInt_smul_left, GlobalTheory.T.theta_killing_implies_vanishing D ψ θ A cA a hDef W χ omW hWW m Measure.haar hm inferInstance u hu hinv hK hconv _ hφ'
      hKφ', mul_zero]
  · obtain ⟨b', hb'⟩ := GlobalTheory.RegSW.Model.exists_isMaj W
    have hIw₀ : HasIw d₀ (Kmax W b') := GlobalTheory.T.adelic_iwasawa_decomposition_wittIsotropicStabilizer D W W₀ r' d₀ b' h2 hb'
    obtain ⟨hAux, hReg, κ, -, hE⟩ := hP4 W₀ r' d₀ hAn₀ hr' b' hb' hIw₀ θ hDef.inf
    obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
    obtain ⟨zG, zH, P, hzP⟩ := hReg τ
    obtain ⟨hRI, hE'⟩ := hE τ zG zH P hzP
    refine ⟨_, hE' φ hφ hKφ, ?_⟩
    rw [dblInt_smul_left, GlobalTheory.T.theta_kill_witt_decomposition D ψ θ A cA a hDef W W₀ r' d₀ b' χ omW hWW m Measure.haar hm inferInstance u hu hinv hK
      hAux τ zH P hzP.2.2.2 hRI _ hφ' hKφ', mul_zero]

end GlobalTheory.Core.Rk.ResKill
