import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearRelationMixedDensitiesIntegralsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureComplOpenGenericPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationTopChernDensityEqFactorialMixedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableLogNormSectionArithmeticVarietyStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixPolar

theorem injective_emb {k : Type} [CommRing k] [IsDomain k] [Module.Finite ℤ k] (σ : k →+* ℂ) :
    Function.Injective σ := by
  refine (RingHom.injective_iff_ker_eq_bot σ).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_)
  rw [RingHom.comap_ker, (RingHom.ext_int _ (Int.castRingHom ℂ) : σ.comp (algebraMap ℤ k) = _)]
  exact (RingHom.injective_iff_ker_eq_bot _).1 Int.cast_injective

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem chernInt_eq (h : IsArithVar p D) (N M : HermLB p) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s)
    (σ : k →+* ℂ) :
    (N.φ σ).chernInt D (offSupp p σ (M.div (isRatSec_ratOfSec s hs))) (logNorm (M.φ σ) (ratOfSec s hs)) =
      Mix.int (fun _ : Fin D => MLine.ofHerm N σ) ((MLine.ofHerm M σ).logSec s) := by
  have := h.isDomain
  have := h.finite
  have hnull (ε : ℤˣ) : (N.φ σ).chernPart D ε (ptsIn p σ (nonzeroLocus s))ᶜ = 0 := by
    have := GlobalTheory.T.mixedChernFormSignedPartMeasure_compl_open_genericPoint_eq_zero k X p σ (injective_emb σ) h.isProjOver D (fun _ => MLine.ofHerm N σ) ε (nonzeroLocus s) hs
    rwa [part_const] at this
  have key (ε : ℤˣ) : ∫ y in offSupp p σ (M.div (isRatSec_ratOfSec s hs)), logNorm (M.φ σ) (ratOfSec s hs) y
      ∂(N.φ σ).chernPart D ε = ∫ y, (MLine.ofHerm M σ).logSec s y ∂(N.φ σ).chernPart D ε := by
    have hae : ∀ᵐ y ∂(N.φ σ).chernPart D ε, y ∈ ptsIn p σ (nonzeroLocus s) := ae_iff.2 (hnull ε)
    have e : offSupp p σ (M.div (isRatSec_ratOfSec s hs)) = ptsIn p σ (nonzeroLocus s) := offSupp_divOfSec
    rw [e, Measure.restrict_eq_self_of_ae_mem hae]
    exact integral_congr_ae (hae.mono fun y hy => logNorm_ratOfSec _ hy)
  rw [Weight.chernInt, key, key, Mix.int, part_const, part_const]
  rfl

end GlobalTheory.MixPolar

namespace GlobalTheory.MixPolar

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {p : X ⟶ Sp k} {D : ℕ}

theorem pol_int (hP : GlobalTheory.Published.Principalisation) (h : IsArithVar p D) (L : Fin D → HermLB p) (M : HermLB p)
    (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (σ : k →+* ℂ) :
    FibreProj.pol (fun n => Mix.int (fun _ : Fin D => MLine.ofHerm (ArInt.comb L n) σ) ((MLine.ofHerm M σ).logSec s)) =
      D.factorial * Mix.int (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm M σ).logSec s) := by
  haveI := CxPts.secondCountableTopology_of_isProjOver σ h.isProjOver
  have e : ∀ F : (Fin D → ℤ) → ℝ,
      ∑ S : Finset (Fin D), (-1 : ℝ) ^ S.card * F (fun i => if i ∈ S then -1 else 0) = FibreProj.pol F := fun F => by
    unfold FibreProj.pol
    congr!
  let Lj : Option (Finset (Fin D)) → Fin D → MLine p σ := fun j =>
    j.elim (fun i => MLine.ofHerm (L i) σ) (fun S _ => MLine.ofHerm (ArInt.comb L (fun i => if i ∈ S then -1 else 0)) σ)
  let a : Option (Finset (Fin D)) → ℝ := fun j => j.elim (-(D.factorial : ℝ)) (fun S => (-1) ^ S.card)
  have hd : ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, ∑ j, a j * dens (Lj j) c y = 0 := by
    intro c y hy
    have := GlobalTheory.T.polarisation_topChernDensity_eq_factorial_mixed k X p σ D L c y hy
    rw [← e] at this
    simp only [Fintype.sum_option, a, Lj, Option.elim, dens_const]
    beta_reduce at this
    simp only [MLine.ofHerm] at this ⊢
    linarith
  have hi : ∀ j, Intg (Lj j) ((MLine.ofHerm M σ).logSec s) := fun j =>
    GlobalTheory.T.integrable_logNormSection_arithmeticVariety hP k X p D h σ (Lj j) (MLine.ofHerm M σ) s hs
  have := GlobalTheory.T.linear_relation_mixed_densities_integrals k X p σ D _ a Lj hd _ hi
  simp only [Fintype.sum_option, a, Lj, Option.elim] at this
  rw [← e]
  beta_reduce
  linarith

end GlobalTheory.MixPolar

open GlobalTheory.MixPolar in

theorem GlobalTheory.MixPolar.mixArch_eq_sum : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : Fin D → HermLB p) (M : HermLB p) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s), MixHt.mixArch L M (isRatSec_ratOfSec s hs) = ∑ᶠ σ : k →+* ℂ, Mix.int (fun i => MLine.ofHerm (L i) σ) ((MLine.ofHerm M σ).logSec s) := by
  intro hP k _ X _ _ p D h L M s hs
  have := h.finite_emb
  haveI := Fintype.ofFinite (k →+* ℂ)
  simp only [MixHt.mixArch, HermLB.archInt, finsum_eq_sum_of_fintype, chernInt_eq h]
  rw [FibreProj.pol_sum]
  simp only [pol_int hP h L M s hs]
  rw [← Finset.mul_sum, mul_div_cancel_left₀ _ (by positivity)]
