import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFunctionGreenBoundFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFunctionGreenBoundSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorHeightBoundNormalSchemeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

set_option autoImplicit false
noncomputable section

theorem GlobalTheory.FlatPullCurve.exists_isometric_pull_curve : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → ∀ (D : D7) (O : Setup D), O.Core → 2 < D.R.f * (O.N - 1) →
    ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H) (B : ℝ), 2 ≤ B → ∀ (τ : D.what₂.Tau) (c : O.s.Comp)
    (g : (T.M c).Fun), (T.M c).Smooth g →
    (∀ σ x, x ∉ (T.M c).Z σ → g σ x = (T.F c).ph (fun σ' _ => if σ' = τ then (-1 : ℝ) else 0) σ x) →
    ∀ (ε : (𝓞 D.what₂.LL →+* ℂ) → Fin ((T.M c).n + 1))
      (π : ∀ σ, GlobalTheory.CxPts (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p σ → (T.M c).X (ε σ)),
    (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.IsDown (h.man c) ε π →
    ∀ (hu : ∀ σ y, GlobalTheory.CxPts.CInfAt ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) σ) y)
      (hc : ∀ σ σ', (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) σ)).IsConj
        (GlobalTheory.Weight.ofFun ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun))) σ'))),
    ∃ (m : ℕ) (k' : Type) (_ : CommRing k') (_ : IsDomain k') (_ : Algebra (𝓞 D.what₂.LL) k')
      (ρ : (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.X ⟶ Sp k')
      (hρ : ρ ≫ spMap (algebraMap (𝓞 D.what₂.LL) k') = (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p)
      (M : HermLB (spMap (algebraMap (𝓞 D.what₂.LL) k'))),
      0 < m ∧ IsArithVar (spMap (algebraMap (𝓞 D.what₂.LL) k')) 0 ∧
      (comb (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => o.elim (fnB ((T.M c).pull ε π ((2 : ℝ) • (g - (fun _ _ => O.Y.htDetT B c τ : (T.M c).Fun)))) hu hc)
      ((h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).gens (GlobalTheory.FlagAr.setB O.Y B))) (fun o : Option (Option (D.what₂.Tau × Fin O.N)) => (m : ℤ) * o.elim (1 : ℤ) fun o' => o'.elim 0 fun x => if x.1 = τ then (-1 : ℤ) else 0)).Isometric (M.pull ρ hρ) := by
  intro hX P2 PH SW D O hO hf A T H h B hB τ c g hg hgz ε π hπ hu hc
  haveI : IsLocallyNoetherian (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.X :=
    (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.ar.isLocallyNoetherian
  obtain ⟨r, hr, hv, hn⟩ := GlobalTheory.T.smooth_function_green_bound_first P2 PH SW D O hO hf A T H h B hB τ c g hg hgz ε π hπ hu hc
  have hd := GlobalTheory.T.smooth_function_green_bound_second hX P2 PH SW D O hO hf A T H h B hB τ c g hg hgz ε π hπ hu hc
  obtain ⟨m, k', i₁, i₂, i₃, ρ, hρ, M, hm, hA, hI⟩ := GlobalTheory.T.cartier_divisor_height_bound_normal_scheme P2 D.what₂.LL (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.X
    (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.p _ (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.ar
    (h.mdl (GlobalTheory.FlagAr.setB O.Y B) c).V.normal _ r hr hv hn hd
  refine ⟨m, k', i₁, i₂, i₃, ρ, hρ, M, hm, hA, ?_⟩
  refine GlobalTheory.HermLB.Isometric.trans (GlobalTheory.HermLB.icls_eq_iff.1 ?_) hI
  rw [GlobalTheory.ArInt.icls_comb, GlobalTheory.HermLB.icls_pow, GlobalTheory.ArInt.icls_comb, Finset.smul_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [mul_smul, natCast_zsmul]
