import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralEqMongeAmpereIntegralCompactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralPullbackGenericallyFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogResolutionProjectiveOfPrincipalisationStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixFin

theorem finite_and_intg : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∀ (L : Fin D → MLine p σ), (∀ ε : ℤˣ, IsFiniteMeasure (part L ε)) ∧ ∀ f : CxPts p σ → ℝ, Continuous f → Intg L f := by
  intro hP F _ X _ _ p σ D hX hdim L
  haveI : CharZero F := RingHom.charZero σ
  obtain ⟨Y, hY, π, hsm, hproj, -, hgen, hdeg, -⟩ :=
    GlobalTheory.T.exists_logResolution_projective_of_principalisation hP F X p D hX hdim ⊥ (fun h => by rwa [← SetLike.mem_coe, Closeds.coe_bot] at h)
  haveI := hY
  haveI : SmoothOfRelativeDimension D (π ≫ p) := hsm
  haveI := CxPts.compactSpace (p := π ≫ p) σ hproj
  haveI := CxPts.t2Space_cxPts_of_isProjOver (p := π ≫ p) σ hproj
  haveI := CxPts.secondCountableTopology_of_isProjOver (p := π ≫ p) σ hproj
  let R := AnRead.all (π ≫ p) σ D
  have key : ∀ f : CxPts p σ → ℝ, Continuous f → Intg L f := by
    intro f hf
    have hf' : Continuous (fun y => f (ptMap π rfl σ y)) := hf.comp (PtsOver.continuous_map _ _ _)
    have h1 := (GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F Y (π ≫ p) σ D R.finAtlas R.isAlgAtlas_finAtlas
      (fun i => (L i).pull π rfl) _ hf'.measurable).1
    have hI := h1.2 (mIntegrableCont _ _ (fun i => Weight.isPotential_locPot
      ((Weight.isCInf_iff_isSmooth R).1 ((L i).pull π rfl).cInf)) _ hf')
    exact ((GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F X Y p (π ≫ p) σ D hX hdim hproj π rfl hgen
      (by rw [hdeg]; exact one_ne_zero) L f hf.measurable).1).1 hI
  refine ⟨fun ε => ?_, key⟩
  have h := key (fun _ => (1 : ℝ)) continuous_const
  rcases Int.units_eq_one_or ε with rfl | rfl
  · exact (integrable_const_iff.1 h.1).resolve_left one_ne_zero
  · exact (integrable_const_iff.1 h.2).resolve_left one_ne_zero

end GlobalTheory.MixFin
