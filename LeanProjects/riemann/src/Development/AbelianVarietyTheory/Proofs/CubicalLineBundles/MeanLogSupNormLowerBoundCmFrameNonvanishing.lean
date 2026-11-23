import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkNum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ArchimedeanHypothesisLowerBoundCmPointStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FramePolynomialEquivariantAndNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocalLowerBoundCmPointFramePolynomialEveryPrimeStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsFramePolynomialOfRuleNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodCmPointAtCmBasisFrameStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmPointLowerBoundFree
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LamDegStLogOm
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfPow
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem letters_lines {E : Type} [Field E] [NumberField E] [IsCMField E] [StarRing (𝓞 E)] {H : Host E} {l : Level H}
    {c : Coeff l} {nΨ n' f : ℕ} {o : LamF.LamObj c nΨ n'} {La t : ℝ} (hG : LamF.LamObjGood o f La)
    (L : LamF.LamLetters o) (hL : L.IsGood)
    (hdeg : (∀ k, (o.ℓΨ k).ndeg = t / 2) ∧ ∀ k, (o.ℓ' k).ndeg = t / 2) :
    (∀ k, (L.ℓ k).Good) ∧ ∀ k, (L.ℓ k).ndeg = t / 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hvΨ, hv', -⟩ := hG
  obtain ⟨-, -, -, hℓ⟩ := hL
  refine ⟨fun k => ?_, fun k => ?_⟩
  · have := hℓ k
    revert this
    cases L.src k with
    | inl q => intro h1; rw [h1]; exact (hvΨ q.2).1
    | inr q => intro h1; rw [h1]; exact (hv' q.2).1
  · have := hℓ k
    revert this
    cases L.src k with
    | inl q => intro h1; rw [h1]; exact hdeg.1 q.2
    | inr q => intro h1; rw [h1]; exact hdeg.2 q.2

theorem meanLogSup_lowerBound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ) → 1 ≤ Dw.p + Dw.q → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ a n, Dom a n → ∀ F ∈ cusp Xo c U a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → (∀ σ, 0 < supC Xo c U ξ (goodOf c σ) a n F) → ∀ (k : (U c.F.val.toRingHom).Comp) (x₀ : ((U c.F.val.toRingHom).X k).dom) (Xx : FD.DataX E r) (hX : Xx.toData = (U c.F.val.toRingHom).X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → ∀ (La : ℝ) (lam : Fin r → Fin r → E), 1 ≤ La → FD.LamBasis Xx La (hX ▸ x₀.1) lam → rdU (U c.F.val.toRingHom) F k x₀.1 ≠ 0 → -((pDeg (logOm E χ).re + (1 / 2) * Real.log La) * (((∑ b : E →+* ℂ, ∑ i : Fin (Dw.mult b), a (b, i) : ℕ) : ℝ) + ((Module.finrank ℚ E / 2 * r : ℕ) : ℝ) * n)) - ((∑ b : E →+* ℂ, ∑ i : Fin (Dw.mult b), a (b, i) : ℕ) : ℝ) * Real.log ((r : ℝ) * La) ≤ (∑ σ : c.F →+* ℂ, Real.log (supC Xo c U ξ (goodOf c σ) a n F)) / (Module.finrank ℚ c.F : ℝ) := by
  intro E _ _ _ H Dw l Xo c r U ξ hU hξ hpq _ χ hχ a n hd F hF hint hpos k x₀ Xx hX 𝔄 h𝔄 hΛ La lam hLa hB hne
  classical
  letI := H.starRing
  have hstar : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  have hgood : GoodEmb c c.F.val.toRingHom := rfl
  have hU0 := hU _ hgood
  have hr : r = Dw.p + Dw.q := hU0.1
  have hFs : F ∈ sec Xo c a n := cusp_le_sec Xo c U a n hF
  obtain ⟨z, σ₁, hz, hx⟩ := GlobalTheory.T.exists_good_cmPoint_at_cmBasis_frame E H Dw l Xo c hstar r _ hU0 (by omega) k x₀ Xx hX 𝔄 h𝔄 hΛ La lam hB
  obtain ⟨G, hG⟩ := GlobalTheory.T.exists_isFramePolynomialOfRule_numberField E H Dw l Xo c z.K z.y a n F hFs
  have hev : evR Xo c F ((U c.F.val.toRingHom).un k x₀) ≠ 0 := by
    intro h0
    apply hne
    change (if h : x₀.1 ∈ ((U c.F.val.toRingHom).X k).dom then
      toC (evR Xo c F ((U c.F.val.toRingHom).un k ⟨x₀.1, h⟩)) else 0) = 0
    rw [dif_pos x₀.2]
    exact h0
  have hG0 : G ≠ 0 := (GlobalTheory.T.framePolynomial_equivariant_and_ne_zero E H Dw l Xo c z.K z.y a n F hFs G hG).2 _ σ₁ _ hx hev
  have hloc := GlobalTheory.T.localLowerBound_cmPoint_framePolynomial_every_prime E H Dw l Xo c z _ La hz a n F hFs hint G hG
  have harch := GlobalTheory.T.archimedeanHypothesis_lowerBound_cmPoint E H Dw l Xo c r U ξ hU hξ hpq z _ La hz a n hd F hF G hG
  obtain ⟨hGood, hL, -⟩ := hz
  have hdeg := LamF.lamDegSt_logOm GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1 E H χ hχ l c hstar _ _ _ z.obj La hGood
  have hdet := LamF.Ind.lamInd E H l c hstar _ _ _ z.obj La hGood z.letters hL
  obtain ⟨hlg, hnd⟩ := letters_lines hGood z.letters hL hdeg
  obtain ⟨-, -, -, -, -, -, -, -, hgB, -, -, -, -, -, -, -, -, -, hTg, hLg, hkl, hka, -⟩ := hGood
  have hmr : ∀ b, Dw.mult b ≤ r := by
    intro b
    unfold Datum.mult
    split_ifs <;> omega
  have h5 := GlobalTheory.cmPoint_lowerBound_free z.K z.Φ.key z.Tl z.LamL (E →+* ℂ) Dw.mult z.e z.ℓ z.U G
    (fun b i => a (b, i)) n r La (logOm E χ).re
    (fun σ => supC Xo c U ξ (goodOf c (σ.comp (algebraMap c.F z.K))) a n F) hTg hLg hkl hka hlg hnd hdet hG0 hLa
    (by omega) hmr (fun σ => hpos _) hloc harch
  have h2 := Formalism.L2.Pj.abelian₂.mean_restrict (K := c.F) (L := z.K)
    (fun τ => Real.log (supC Xo c U ξ (goodOf c τ) a n F))
  beta_reduce at h5 h2
  rw [h2] at h5
  have hg : z.Φ.key.P.g = Module.finrank ℚ E / 2 * r := by rw [hr]; exact hgB
  rw [hg] at h5
  exact h5

end GlobalTheory.LamT
