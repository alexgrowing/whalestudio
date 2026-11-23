import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FlatZetaIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryThetaInnerProductFormulaConvergentRangeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicMajorantFrameForCartanInvolutionsStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.IP

variable {D : D7}

theorem integrable_star_comp {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}
    (hf : Integrable f μ) : Integrable (fun x => conj (f x)) μ := by
  simpa using (Complex.conjCLE.toContinuousLinearMap).integrable_comp hf

theorem memL2_conj_comp (V : HSp D) (μ : Measure (GA D V)) {f : GA D V → ℂ}
    (hf : MemL2Quotient (GQ V) μ f) : MemL2Quotient (GQ V) μ (fun x => conj (f x)) := by
  refine ⟨fun γ hγ g => by simp only [hf.1 γ hγ g], ?_⟩
  have := (Complex.conjCLE.toContinuousLinearMap).comp_memLp' hf.2
  convert this using 1
  funext q
  simp [GlobalTheory.AutomorphicL2Unitary.descend]

theorem petersson_star_comp (V : HSp D) (μ : Measure (GA D V)) (f₁ f₂ : GA D V → ℂ) :
    petersson V μ (fun x => conj (f₁ x)) (fun x => conj (f₂ x)) = conj (petersson V μ f₁ f₂) := by
  simp only [petersson, pet]
  rw [← integral_conj]
  congr 1; funext q
  simp [GlobalTheory.AutomorphicL2Unitary.descend]

theorem innerProduct_convergent_conj : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelEisensteinContinuation → ∀ D : D7, ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (K₁ K₂ : GA D A → GA D B → ℂ) (c : GA D A → ℂ) (m : Measure (GA D A)) (ν : Measure (GA D B)) (f₁ f₂ : GA D A → ℂ), HidaSetting θ A B sA sB t cA → (wittIndex B = 0 ∨ wittIndex B < t) → A.rank < t → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsKernelPair ψ θ A B χA χB sA sB false (fun _ => True) (fun _ => True) K₁ K₂ c → m.IsHaarMeasure → ν.IsHaarMeasure → f₁ ∈ A0 θ A cA → f₂ ∈ A0 θ A cA → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv m ν K₁ f₁ ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv m ν K₂ f₂ ∧ Integrable (fun g => c g * conj (petersson A m (rTr A g f₁) f₂)) m ∧ petersson B ν (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m K₁ f₁) (GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m K₂ f₂) = volQ B ν * ∫ g, c g * conj (petersson A m (rTr A g f₁) f₂) ∂m := by
  intro hRD hWS hSE D ψ θ A B χA χB sA sB t cA K₁ K₂ c m ν f₁ f₂ hS hw ht hK hm hν hf₁ hf₂
  obtain ⟨om, Φ₁, Φ₂, hW, hF₁, hF₂, -, -, hK₁, hK₂, μ, 𝓕, hcov, hc⟩ := hK
  obtain ⟨a, ha, ha'⟩ := GlobalTheory.T.exists_adelicMajorantFrame_for_cartanInvolutions D θ A sA hS.2.2.2.1 hS.2.2.2.2.2.2.1
  have hP : Pair ψ θ A B χA χB sA sB t cA a om μ 𝓕 := ⟨hS, ha, ha', hW, hcov⟩
  obtain ⟨hU₁, hU₂, hI, hE⟩ := GlobalTheory.T.unitary_theta_innerProduct_formula_convergent_range hRD hWS hSE D ψ θ A B χA χB sA sB t cA a om μ 𝓕 hP hw ht m ν hm hν
    Φ₁ Φ₂ hF₁ hF₂ f₁ hf₁ f₂ hf₂
  have hcg : ∀ g, c g = conj (wcoef om μ 𝓕 Φ₁ Φ₂ g) := by
    intro g
    have h1 : wcoef om μ 𝓕 Φ₁ Φ₂ g = conj (c g) := by
      have h2 := hc g
      simp only at h2
      rw [h2]; rfl
    rw [h1, Complex.conj_conj]
  have hlift : ∀ (K : GA D A → GA D B → ℂ) (Φ : WO A B → ℂ) (u : GA D A → ℂ),
      (∀ g h, K g h = conj (thetaKO om g h Φ)) →
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift m K u = fun h => conj (up om m Φ u h) := by
    intro K Φ u hK; funext h
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.lift, up, petersson, pet, hK]
    rw [← integral_conj]
    congr 1; funext q
    simp [GlobalTheory.AutomorphicL2Unitary.descend]
  have hconv : ∀ (K : GA D A → GA D B → ℂ) (Φ : WO A B → ℂ) (u : GA D A → ℂ),
      (∀ g h, K g h = conj (thetaKO om g h Φ)) → UpConv om m ν Φ u → GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.LiftConv m ν K u := by
    intro K Φ u hK hU
    refine ⟨fun h => ?_, ?_⟩
    · have := integrable_star_comp (hU.1 h)
      convert this using 2 with q
      simp [GlobalTheory.AutomorphicL2Unitary.descend, hK]
    · rw [hlift K Φ u hK]
      exact memL2_conj_comp B ν hU.2
  refine ⟨hconv K₁ Φ₁ f₁ hK₁ hU₁, hconv K₂ Φ₂ f₂ hK₂ hU₂, ?_, ?_⟩
  · have := integrable_star_comp hI
    convert this using 2 with g
    simp [hcg, rcoef]
  · rw [hlift K₁ Φ₁ f₁ hK₁, hlift K₂ Φ₂ f₂ hK₂, petersson_star_comp, hE, map_mul, ← integral_conj]
    simp [hcg, rcoef]

end GlobalTheory.Core.Rk.IP

end
