import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.FamParts
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PowTwist
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CarryLift
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExTwist
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocIff
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursIff
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursBasics

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.T Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.CBC

private theorem occ_basic {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (V : Submodule ℂ (LL μ)) (hV : IsSummand μ V) (w : Pl K) :
    (∃ σ, Occurs μ V w σ) ∧ (∀ σ σ', Occurs μ V w σ → Occurs μ V w σ' → Nonempty (σ.ρ.Equiv σ'.ρ)) := by
  letI : MeasurableSpace (Gw n w) := borel _
  haveI : BorelSpace (Gw n w) := ⟨rfl⟩
  have h := occursBasics K n μ V w Measure.haar hV
  exact ⟨h.1, h.2.1⟩

private theorem loc_iff {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {n : ℕ} (μ : Measure (normOneGL E n))
    [μ.IsHaarMeasure] (π : CuspSub E n) (V : Submodule ℂ (LL μ)) (h : Dp.Carries μ π V) (w : Pl E) (σ : SmIrr (Gw n w)) :
    (Cusp.cx π).locComp w σ ↔ Occurs μ V w σ :=
  (Dp.locIff E n μ π V h w σ).trans (occursIff E n μ V h.summand w σ).symm

private theorem locIso_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {v : Pl F} (w : PlacesOver E v) {τ τ₁ : SmIrr (Gw n v)} {τ' τ₁' : SmIrr (Gw n w.1)} (a : τ₁.ρ.Equiv τ.ρ)
    (b : τ'.ρ.Equiv τ₁'.ρ) (h : LocIso w τ τ') : LocIso w τ₁ τ₁' := by
  obtain ⟨e, he⟩ := h
  refine ⟨a.toLinearEquiv.trans (e.trans b.toLinearEquiv), fun g x => ?_⟩
  have ha : a.toLinearEquiv (τ₁.ρ g x) = τ.ρ g (a.toLinearEquiv x) :=
    Representation.IntertwiningMap.isIntertwining _ _ a.toIntertwiningMap g x
  have hb : ∀ g y, b.toLinearEquiv (τ'.ρ g y) = τ₁'.ρ g (b.toLinearEquiv y) := fun g y =>
    Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap g y
  simp only [LinearEquiv.trans_apply]
  rw [ha, he, hb]

theorem UpperTheory.ConvolutionTheory.T.descStep :
    UpperTheory.ConvolutionTheory.T.CoreDesc → UpperTheory.ConvolutionTheory.T.LiftAll → UpperTheory.ConvolutionTheory.T.DescStep := by
  intro hD hL F E _ _ _ _ _ _ _ _ σ hσ hp n hn P hP v w hv
  let μE : Measure (normOneGL E n) := Measure.haar
  let μF : Measure (normOneGL F n) := Measure.haar
  obtain ⟨χ', ⟨s, hs'⟩, V, hV⟩ := Dp.exTwist E n μE P hn
  obtain ⟨hex, htw⟩ := powTwist F E
  obtain ⟨χ, hs⟩ := (hex s).1
  obtain ⟨hi, hi', h1⟩ := htw s χ χ' hs hs'
  obtain ⟨-, hPP, -, hconj, -⟩ := h1 n hn
  obtain ⟨-, -, h2⟩ := htw (-s) χ⁻¹ χ'⁻¹ hi hi'
  obtain ⟨-, -, hlift, -, hloc⟩ := h2 n hn
  obtain ⟨-, hAt, hcl, -, hnp, θ, hθ, hst⟩ := carryLift F E σ hσ hp n hn μE μF
  obtain ⟨Λ, t, hΛ⟩ := hAt V hV.summand
  have hstab := (hst _ V hV).1 fun g => hconj P _ (hP g)
  have hoff : OffAll F n Λ t := by
    by_contra hc
    exact hnp _ V Λ t hV hΛ (famParts F E σ hσ hp n hn (fun m hm _ => hL F E σ hσ hp m hm) Λ t hc)
  obtain ⟨⟨τ', hτ'⟩, huE⟩ := occ_basic μE V hV.summand w.1
  obtain ⟨V₀, Λ₀, t₀, hV₀, hAt₀, hΛ₀, ht₀, τ, hτ, hiso⟩ :=
    hD F E σ hσ hp n hn μE μF θ hθ V Λ t hV.summand hstab hΛ hoff v w hv τ' hτ'
  obtain ⟨π, hπ, -⟩ := Dp.exCusp F n μF V₀ hV₀
  obtain ⟨-, huF⟩ := occ_basic μF V₀ hV₀ v
  have hl := hlift π _ (hcl π _ V₀ V Λ₀ t₀ Λ t hπ hV hAt₀ hΛ hΛ₀ ht₀)
  have hl2 := hloc π (P.twist χ') v w (hv w) fun τ₁ τ₁' h₁ h₁' => by
    obtain ⟨a⟩ := huF τ₁ τ ((loc_iff μF π V₀ hπ v τ₁).1 h₁) hτ
    obtain ⟨b⟩ := huE τ' τ₁' hτ' ((loc_iff μE _ V hV w.1 τ₁').1 h₁')
    exact locIso_congr w a b hiso
  rw [hPP] at hl hl2
  exact ⟨π.twist χ⁻¹, hl, hl2⟩
