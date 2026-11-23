import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SphConj
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.LiftAll
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.DescAt
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SameSat
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.PowSat
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.NormUnr
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SphConjAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CarryLift
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.PowTwist
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatIff
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.SSatEx
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExCusp
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.IsoEq
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.T GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual
open UpperTheory.V.Published UpperTheory.CBC PositivityTheory.RgJS

theorem UpperTheory.ConvolutionTheory.Sph.down :
    UpperTheory.ConvolutionTheory.Sph.Down := by
  classical
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn π P hW v hv ⟨w, hwv, B', hB'⟩
  let μE : Measure (normOneGL E n) := Measure.haar
  let μF : Measure (normOneGL F n) := Measure.haar
  obtain ⟨s, χ, χ', V, V', θ, hχ, hχ', hV, hV', hθ, hst, hW', -, hOff⟩ := Sph.norm F E σ hσ hp n hn μE μF π P hW
  obtain ⟨-, htw⟩ := powTwist F E
  obtain ⟨hi, -, h1⟩ := htw s χ χ' hχ hχ'
  obtain ⟨hback, -⟩ := h1 n hn
  obtain ⟨-, hAtE, hcl, -⟩ := carryLift F E σ hσ hp n hn μE μF
  have hsat : ∃ B, (Cusp.cx (P.twist χ')).sat w B := by
    have := satake_twist_holds E n (CG.mk P) χ' w B' (Sph.powSat E χ' s hχ' w).1 hB'
    rw [CG.twist_mk] at this
    exact ⟨_, this⟩
  obtain ⟨B₁, hB₁⟩ := hsat
  have hS1 : SSat μE V' w (B₁.map fun b : ℂˣ => (b : ℂ)) := (Dp.sSatIff E n μE _ V' hV' w _).2 ⟨B₁, rfl, hB₁⟩
  have hsph : ∀ u : Pl E, u.under (𝓞 F) = v → ∃ B, SSat μE V' u B := fun u hu =>
    Dp.sSatEx E n μE V' hV'.summand u (Sph.sphConj F E σ hσ hp n hn μE θ hθ V' hst w u (hwv.trans hu.symm) hS1.2.1)
  choose! b hb using hsph
  obtain ⟨Λ, t, S, hS, hAt⟩ := hAtE V' hV'.summand
  let t₁ : Pl E → Multiset ℂ := fun u => if u.under (𝓞 F) = v then b u else t u
  let S₀ : Set (Pl E) := S \ {u | u.under (𝓞 F) = v}
  have hS₀ : S₀.Finite := hS.subset Set.diff_subset
  have hAt₁ : At μE S₀ V' Λ t₁ := by
    refine ⟨hAt.1, fun u hu => ?_⟩
    by_cases h : u.under (𝓞 F) = v
    · simp only [t₁, if_pos h]
      exact hb u h
    · simp only [t₁, if_neg h]
      exact hAt.2 u fun h' => hu ⟨h', h⟩
  have hAE₁ : AtAE μE V' Λ t₁ := ⟨S₀, hS₀, hAt₁⟩
  obtain ⟨V₀, Λ₀, t₀, hV₀, hAt₀, hΛ, ht, hv₀, -⟩ := Sph.descAt ci Sph.gm F E σ hσ hp n hn μE μF θ hθ V' Λ t₁ S₀
    hV'.summand hst hS₀ hAt₁ (hOff _ _ hAE₁) v hv (fun u hu h => h.2 hu)
  obtain ⟨π₀, hπ₀, -⟩ := Dp.exCusp F n μF V₀ hV₀
  have hl := hcl π₀ _ V₀ V' Λ₀ t₀ Λ t₁ hπ₀ hV' hAt₀ hAE₁ hΛ ht
  obtain ⟨η, hη, hiso⟩ := (R.fibre_holds F E hp n hn (.cx π₀) (.cx (P.twist χ')) hl.1).2 (.cx (π.twist χ)) hW'
  have he : π₀.twist η = π.twist χ := (Dp.isoEq F n _ _).1 hiso
  obtain ⟨B₀, -, hB₀⟩ := (Dp.sSatIff F n μF π₀ V₀ hπ₀ v _).1 hv₀
  have hηu : η.UnrAt v := by
    rcases hη with rfl | hη
    · intro x _
      rfl
    · exact Sph.normUnr F E η hη v hv
  have h2 := satake_twist_holds F n (CG.mk π₀) η v B₀ hηu hB₀
  rw [CG.twist_mk, he] at h2
  have h3 := satake_twist_holds F n (CG.mk (π.twist χ)) χ⁻¹ v _ (Sph.powSat F χ⁻¹ (-s) hi v).1 h2
  rw [CG.twist_mk, hback] at h3
  exact ⟨_, h3⟩
