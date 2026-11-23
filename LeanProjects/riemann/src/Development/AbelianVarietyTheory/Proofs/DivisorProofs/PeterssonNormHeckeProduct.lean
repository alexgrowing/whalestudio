import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAniso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunOPosSigIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAnisotropicRallisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomThetaIntegralNormSqEqPeterssonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainUnitaryQuotientVolumeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInnerProductFormulaDataDefiniteBottomStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

namespace GlobalTheory.RallisBottom

theorem normBig_innerProduct : GlobalTheory.FunPr.Hypotheses₂ → GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X → ∀ t : T, ∃ (P : PolF D WW.rank A.rank) (ν : Measure (GA D WW)) (𝓕 : Set (GA D WW)) (c : ℂ), c ≠ 0 ∧ ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ WW) 𝓕 ν ∧ ∀ Λ : ℂ → ℂ, GlobalTheory.CMVal.IsHeckeL (nuH G t i j) Λ → ((∫ h in 𝓕, ‖X.I W.ψ W.θ t P h‖ ^ 2 ∂ν : ℝ) : ℂ) = c * ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s := by
  intro hPr
  obtain ⟨CF0, h⟩ := GlobalTheory.T.exists_innerProductFormula_data_definite_bottom
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := h ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ he hx hR T Lc μ₀ hμ G W i j A A' WW X hX t => ?_⟩

  have hX₁ := isBottomTri_posSig hX
  obtain ⟨χA, χB, sA, sB, cA, a, νW, 𝓕W, LA, LB, Sf, par, κ, P, hP, hw, hF, hU, h1, hpar, hsph, hκ, hdS, hL, hloc⟩ :=
    h C hC D large₂ he hx hR T Lc μ₀ hμ G W i j (posSig A) A' WW (Tri.posSig X) hX₁ (sigOK_posSig hX) t
  obtain ⟨ν, 𝓕, hν, h𝓕, hvol⟩ := GlobalTheory.T.exists_haar_fundamentalDomain_unitaryQuotientVolume_ne_zero W i j (posSig A) A' WW (Tri.posSig X) hX₁
  obtain ⟨m, hm, hdict⟩ := GlobalTheory.T.definiteBottom_thetaIntegral_normSq_eq_petersson W i j (posSig A) A' WW (Tri.posSig X) hX₁ t P ν 𝓕 hν h𝓕
  obtain ⟨hs₁, hZ⟩ := hloc m hm
  obtain ⟨-, -, -, hH⟩ := GlobalTheory.T.hecke_form_anisotropic_rallis hPr D W.ψ W.θ (GlobalTheory.Grid.neg (posSig A)) WW χA χB sA sB A'.rank cA a _ νW 𝓕W hP hw LA LB Sf _ _ hF hF hU
    m ν hm hν _ h1 _ h1 par hpar hsph hs₁
  refine ⟨P, ν, 𝓕, volQ WW ν * κ * _,
    mul_ne_zero (mul_ne_zero (by exact_mod_cast hvol) hκ) hZ, hν, h𝓕, fun Λ hΛ => ?_⟩
  show ((∫ h in 𝓕, ‖(Tri.posSig X).I W.ψ W.θ t P h‖ ^ 2 ∂ν : ℝ) : ℂ) = _
  rw [hdict, hH _ (hL Λ hΛ), mul_right_comm κ, mul_div_cancel_right₀ _ hdS]
  ring

end GlobalTheory.RallisBottom
