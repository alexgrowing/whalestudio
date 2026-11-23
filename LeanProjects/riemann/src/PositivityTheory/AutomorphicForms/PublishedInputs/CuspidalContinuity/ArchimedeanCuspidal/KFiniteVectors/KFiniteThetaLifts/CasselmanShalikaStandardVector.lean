import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.BaseChangeAssembly
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.PureTh

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3.R (G2 Jd md KA Set0 Coord LInv)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.K.QuadraticBaseChangeGL3

variable (K : Type) [Field K] [NumberField K]

def SPHB : Prop := Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl), Th.Unr c v → ∃ Wt, Th.StdTh c v Wt

def CasselmanShalikaStandardVector : Prop := Module.finrank ℚ K = 2 → ∀ (D : Dat) (DK : DatK K), IsBC D DK → ∀ (c : HeckeCharacter K) (v : Pl), v ∉ D.bad →
  Th.Unr c v → ∀ Wt, Th.StdTh c v Wt → ∀ s : ℂ, 0 < s.re →
    zU (GP.sph D v) Wt s = GP.sph D v 1 * lfV DK c v s ∧
    zU (GL2LocalData.dW3 (GP.sph D v)) (GL2LocalData.dW2 Wt) s = GP.sph D v 1 * lfV DK c⁻¹ v s

def THETAB : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (DK : DatK K) c n t S, AdmK DK c n t S →
  ∀ (Wtf : ∀ v : Pl, GL (Fin 2) (Qv v) → ℂ) (e : Pl → ℂ), (∀ v, InThE c v (Wtf v) (e v)) →
  (∃ S0 : Finset Pl, ∀ v ∉ S0, Th.Unr c v ∧ Th.StdTh c v (Wtf v)) → ∃ θ Cst : G2 → ℂ, ThX θ Cst (pw2 (thR n t) Wtf)

def FACB : Prop := Module.finrank ℚ K = 2 → ∀ (mK : Measure KA), mK.IsHaarMeasure → IsProbabilityMeasure mK →
  ∀ (D : Dat) (L : GP.Loc D), Explicit D L → ∀ (DK : DatK K) c n t S, AdmK DK c n t S →
  ∀ Wi Wf, GP.IsFac L Wi Wf → ∀ (Wtf : ∀ v : Pl, GL (Fin 2) (Qv v) → ℂ) (e : Pl → ℂ), (∀ v, InThE c v (Wtf v) (e v)) →
  ∀ S0 : Finset Pl, (∀ v ∉ S0, Wf v = GP.sph D v ∧ Th.Unr c v ∧ Th.StdTh c v (Wtf v)) →
  ∃ C' : ℂ, C' ≠ 0 ∧ ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
    JG mK (GP.pw Wi Wf) (pw2 (thR n t) Wtf) s = C' * GL2LocalData.realZetaIntegralGL3GL2 Wi (thR n t) s *
      (∏ v ∈ S0, GL2LocalData.zetaGL3GL2 (GP.psiF v) (Wf v) (Wtf v) s) * ∏' v : {v : Pl // v ∉ S0}, zU (Wf v.1) (Wtf v.1) s ∧
    JG mK (dualWhittakerAdelicGL3 (GP.pw Wi Wf)) (dualWhittakerAdelic (pw2 (thR n t) Wtf)) s = C' * GL2LocalData.realZetaIntegralGL3GL2 (GL2LocalData.dW3R Wi) (GL2LocalData.dW2R (thR n t)) s *
      (∏ v ∈ S0, GL2LocalData.zetaGL3GL2 (GP.psiF v) (GL2LocalData.dW3 (Wf v)) (GL2LocalData.dW2 (Wtf v)) s) *
        ∏' v : {v : Pl // v ∉ S0}, zU (GL2LocalData.dW3 (Wf v.1)) (GL2LocalData.dW2 (Wtf v.1)) s

def BaseChangeAssemblyStandard : Prop := BCEX K → BCOF K → RationalPrimesBelowPlaces K → REGRP K → SphericalWhittakerAtOne → SPHB K → Th.STDSPH K → CasselmanShalikaStandardVector K → TEST K → HOLV K → LFEV K →
  GLUE K → TSH → GAMB → THETAB K → DEC → ENT → GFE → UNF → FACB K → EULH K → TILI →
  GL2LocalData.LocalFunctionalEquationFinite → GL2LocalData.WeilJLF → GL2LocalData.WeilJLS → GL2LocalData.LocalFunctionalEquationReal → R.G0 → R.G2a → Out2 K

end Ad3.K.QuadraticBaseChangeGL3
