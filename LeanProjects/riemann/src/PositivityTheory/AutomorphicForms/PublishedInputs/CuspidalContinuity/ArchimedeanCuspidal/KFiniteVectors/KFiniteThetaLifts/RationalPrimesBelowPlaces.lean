import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.DualWhittakerAdelicGL3
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3.R (G2 Jd md KA Set0 Coord LInv)
open scoped NumberField.AdeleRing ValuativeRel

namespace Ad3.K.QuadraticBaseChangeGL3

variable (K : Type) [Field K] [NumberField K]

abbrev VFv (D : Dat) (v : Pl) : Submodule ℂ (GL (Fin 3) (Qv v) → ℂ) := LFS.VF (GP.psiF v) (V2 (GP.psiF v) (D.ν v) (D.ν v)⁻¹)

def BCEX : Prop := ∀ D : Dat, ∃ DK : DatK K, IsBC D DK

def BCOF : Prop := ∀ (D : Dat) (DK : DatK K), IsBC D DK → BCOf D DK

def RationalPrimesBelowPlaces : Prop := ∀ S : Finset (PlK K), ∃ S0 : Finset Pl, (∀ v, v ∈ S0 ↔ ∃ w ∈ S, w.asIdeal.LiesOver v.asIdeal) ∧
  (Satd S → ∀ w : PlK K, w ∈ S ↔ ∃ v ∈ S0, w.asIdeal.LiesOver v.asIdeal)

def REGRP : Prop := ∀ (DK : DatK K) (c : HeckeCharacter K) (S : Finset (PlK K)) (S0 : Finset Pl),
  (∀ w : PlK K, w ∈ S ↔ ∃ v ∈ S0, w.asIdeal.LiesOver v.asIdeal) →
  (∀ s, ∏ w ∈ S, gam3 (localAdelicChar K w) (DK.ν w) (localChar c w) s = ∏ v ∈ S0, gamV DK c v s) ∧
  ∀ s : ℂ, 1 < s.re → HasProd (fun v : {v : Pl // v ∉ S0} => lfV DK c v.1 s) (eulK DK c S s)

def SphericalWhittakerAtOne : Prop := ∀ (D : Dat) (v : Pl), v ∉ D.bad → GP.sph D v 1 = 1

def SPH : Prop := Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl),
  (∀ (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], IsUnramifiedChar (localChar c w) ∧ w.asIdeal.ramificationIdx (𝓞 ℚ) = 1) →
  ∃ Wt, InThE c v Wt 1 ∧ SphN Wt

def CasselmanShalikaGL3GL2 : Prop := Module.finrank ℚ K = 2 → ∀ (D : Dat) (DK : DatK K), IsBC D DK → ∀ (c : HeckeCharacter K) (v : Pl), v ∉ D.bad →
  (∀ (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], IsUnramifiedChar (localChar c w) ∧ w.asIdeal.ramificationIdx (𝓞 ℚ) = 1) →
  ∀ Wt e, InThE c v Wt e → SphN Wt → ∀ s : ℂ, 0 < s.re →
    zU (GP.sph D v) Wt s = GP.sph D v 1 * lfV DK c v s ∧
    zU (GL2LocalData.dW3 (GP.sph D v)) (GL2LocalData.dW2 Wt) s = GP.sph D v 1 * lfV DK c⁻¹ v s

def TEST : Prop := Module.finrank ℚ K = 2 → ∀ (D : Dat) (c : HeckeCharacter K) (v : Pl),
  ∃ W ∈ VFv D v, ∃ Wt e, InThE c v Wt e ∧ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ s : ℂ, 0 < s.re → GL2LocalData.zetaGL3GL2 (GP.psiF v) W Wt s = κ

def HOLV : Prop := Module.finrank ℚ K = 2 → ∀ (D : Dat) (c : HeckeCharacter K) (v : Pl), ∀ W ∈ VFv D v, ∀ Wt e, InThE c v Wt e →
  DifferentiableOn ℂ (fun u => GL2LocalData.zetaGL3GL2 (GP.psiF v) (GL2LocalData.dW3 W) (GL2LocalData.dW2 Wt) u) {u | 0 < u.re}

def LFEV : Prop := Module.finrank ℚ K = 2 → GL2LocalData.LocalFunctionalEquationFinite → GL2LocalData.WeilJLF → GL2LocalData.WeilJLS →
  ∀ (D : Dat) (DK : DatK K), IsBC D DK → ∀ (c : HeckeCharacter K) (v : Pl), ∀ W ∈ VFv D v, ∀ Wt e, InThE c v Wt e →
    ∀ s : ℂ, 0 < s.re → s.re < 1 →
      GL2LocalData.zetaGL3GL2 (GP.psiF v) (GL2LocalData.dW3 W) (GL2LocalData.dW2 Wt) (1 - s) = e * gamV DK c v s * GL2LocalData.zetaGL3GL2 (GP.psiF v) W Wt s

def GLUE : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (c : HeckeCharacter K) (S0 : Finset Pl) (e : Pl → ℂ),
  (∀ v, ∃ Wt, InThE c v Wt (e v)) →
  (∀ (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal], w.asIdeal.ramificationIdx (𝓞 ℚ) ≠ 1 → v ∈ S0) →
  ∏ v ∈ S0, e v = -Complex.I

def TSH : Prop := ∀ (W : GL (Fin 3) ℝ → ℂ) (n : ℤ) (t : ℝ) (s : ℂ),
  GL2LocalData.realZetaIntegralGL3GL2 W (thR n t) s = GL2LocalData.realZetaIntegralGL3GL2 W (GL2LocalData.WthR n) (s + Complex.I * t) ∧
  GL2LocalData.realZetaIntegralGL3GL2 (GL2LocalData.dW3R W) (GL2LocalData.dW2R (thR n t)) s = GL2LocalData.realZetaIntegralGL3GL2 (GL2LocalData.dW3R W) (GL2LocalData.dW2R (GL2LocalData.WthR n)) (s - Complex.I * t)

def GAMB : Prop := ∀ (k : ℕ) (n : ℤ) (t : ℝ),
  (∀ s : ℂ, 0 < s.re → GL2LocalData.archimedeanGammaFactorGL3GL2 k n (s + Complex.I * t) ≠ 0) ∧
  DifferentiableOn ℂ (fun s => (GL2LocalData.archimedeanGammaFactorGL3GL2 k n (s + Complex.I * t))⁻¹) {s | 1 / 4 < s.re} ∧
  Ord (fun s => (GL2LocalData.archimedeanGammaFactorGL3GL2 k n (s + Complex.I * t))⁻¹) (1 / 3) ∧
  DifferentiableOn ℂ (fun s => GL2LocalData.archimedeanGammaFactorGL3GL2 k n (s - Complex.I * t)) {s | 1 / 4 < s.re} ∧
  ∀ s : ℂ, 0 < s.re → s.re < 1 → GL2LocalData.eR k n * GL2LocalData.archimedeanGammaFactorGL3GL2 k n (1 - s) = Complex.I * complexGL3 k n s * GL2LocalData.archimedeanGammaFactorGL3GL2 k n s

def THETA : Prop := Module.finrank ℚ K = 2 → IsTotallyComplex K → ∀ (DK : DatK K) c n t S, AdmK DK c n t S →
  ∀ (Wtf : ∀ v : Pl, GL (Fin 2) (Qv v) → ℂ) (e : Pl → ℂ), (∀ v, InThE c v (Wtf v) (e v)) →
  (∃ S0 : Finset Pl, ∀ v ∉ S0, SphN (Wtf v)) → ∃ θ Cst : G2 → ℂ, ThX θ Cst (pw2 (thR n t) Wtf)

def EXP : Prop := ∀ (V : Submodule ℂ (G3 → ℂ)) (hV : WhA V) (U : V →ₗ[ℂ] archSmooth ℚ 3), IsLiftU V hV U → ∀ (W : V) (g : G3),
  Summable (fun q : GA.NQ => ‖(W : G3 → ℂ) (dia (GA.e1 q.out) * g)‖) ∧
  HasSum (fun q : GA.NQ => (W : G3 → ℂ) (dia (GA.e1 q.out) * g)) ((U W : G3 → ℂ) g)

def DEC : Prop := ∀ (V : Submodule ℂ (G3 → ℂ)) (hV : WhA V) (U : V →ₗ[ℂ] archSmooth ℚ 3), IsLiftU V hV U → ∀ W : V,
  Continuous (U W : G3 → ℂ) ∧ DecG (fun h => (U W : G3 → ℂ) (e3A h)) ∧ DecG (fun h => (U W : G3 → ℂ) (ti (e3A h)))

def ENT : Prop := ∀ μ 𝓕 mK 𝓓, Set0 μ 𝓕 mK 𝓓 → ∀ (φ : G3 → ℂ) (θ : G2 → ℂ), Continuous φ → IsLeftInvariant φ →
  DecG (fun h => φ (e3A h)) → Continuous θ → LInv θ → ModG θ →
  Differentiable ℂ (IG μ 𝓕 φ θ) ∧ Ord (IG μ 𝓕 φ θ) (1 / 3)

def GFE : Prop := ∀ μ 𝓕 mK 𝓓, Set0 μ 𝓕 mK 𝓓 → ∀ (φ : G3 → ℂ) (θ : G2 → ℂ), Continuous φ → Continuous θ →
  IsLeftInvariant φ → LInv θ → ∀ s : ℂ, IG μ 𝓕 φ θ s = IG μ 𝓕 (fun g => φ (ti g)) (fun h => θ (ti h)) (1 - s)

def UNF : Prop := ∀ μ 𝓕 mK 𝓓 (C : NNReal), Set0 μ 𝓕 mK 𝓓 → Coord μ mK C →
  ∀ (V : Submodule ℂ (G3 → ℂ)) (hV : WhA V) (U : V →ₗ[ℂ] archSmooth ℚ 3), IsLiftU V hV U → ∀ (W : V) (θ Cst Wt : G2 → ℂ),
  ThX θ Cst Wt → ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
    IG μ 𝓕 (U W) θ s = ((C : ℝ) : ℂ) * JG mK W Wt s ∧
    IG μ 𝓕 (fun g => (U W : G3 → ℂ) (ti g)) (fun h => θ (ti h)) s = ((C : ℝ) : ℂ) * JG mK (dualWhittakerAdelicGL3 W) (dualWhittakerAdelic Wt) s

def FAC : Prop := Module.finrank ℚ K = 2 → ∀ (mK : Measure KA), mK.IsHaarMeasure → IsProbabilityMeasure mK →
  ∀ (D : Dat) (L : GP.Loc D), Explicit D L → ∀ (DK : DatK K) c n t S, AdmK DK c n t S →
  ∀ Wi Wf, GP.IsFac L Wi Wf → ∀ (Wtf : ∀ v : Pl, GL (Fin 2) (Qv v) → ℂ) (e : Pl → ℂ), (∀ v, InThE c v (Wtf v) (e v)) →
  ∀ S0 : Finset Pl, (∀ v ∉ S0, Wf v = GP.sph D v ∧ SphN (Wtf v)) → ∃ C' : ℂ, C' ≠ 0 ∧ ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
    JG mK (GP.pw Wi Wf) (pw2 (thR n t) Wtf) s = C' * GL2LocalData.realZetaIntegralGL3GL2 Wi (thR n t) s *
      (∏ v ∈ S0, GL2LocalData.zetaGL3GL2 (GP.psiF v) (Wf v) (Wtf v) s) * ∏' v : {v : Pl // v ∉ S0}, zU (Wf v.1) (Wtf v.1) s ∧
    JG mK (dualWhittakerAdelicGL3 (GP.pw Wi Wf)) (dualWhittakerAdelic (pw2 (thR n t) Wtf)) s = C' * GL2LocalData.realZetaIntegralGL3GL2 (GL2LocalData.dW3R Wi) (GL2LocalData.dW2R (thR n t)) s *
      (∏ v ∈ S0, GL2LocalData.zetaGL3GL2 (GP.psiF v) (GL2LocalData.dW3 (Wf v)) (GL2LocalData.dW2 (Wtf v)) s) *
        ∏' v : {v : Pl // v ∉ S0}, zU (GL2LocalData.dW3 (Wf v.1)) (GL2LocalData.dW2 (Wtf v.1)) s

end Ad3.K.QuadraticBaseChangeGL3
