import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorProductSectionsZerosMultiplicitiesNormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralAdditiveInFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormFiniteIntegrablePointClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSectionIntegrableMixedChernProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightEqOneIffClosureDimProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureComplOpenGenericPStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DefectAdd

theorem compactSpace_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem int_eq_add_of_ae {k : Type} [CommRing k] {Y : Scheme.{0}} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine q σ) {f g h : CxPts q σ → ℝ} (hf : Intg L f) (hg : Intg L g)
    (hh : ∀ ε : ℤˣ, ∀ᵐ y ∂part L ε, h y = f y + g y) :
    Mix.int L h = Mix.int L f + Mix.int L g := by
  simp only [Mix.int]
  rw [integral_congr_ae (hh 1), integral_congr_ae (hh (-1)), integral_add hf.1 hg.1, integral_add hf.2 hg.2]
  ring

theorem defect_add : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M A N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (a : A.B.Sec) (ha : genericPoint X ∈ nonzeroLocus a) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ⊓ nonzeroLocus a ∨ z ∈ nonzeroLocus t) → ∃ (s₁ : (M.tens A).B.Sec) (h₁ : genericPoint X ∈ nonzeroLocus s₁), nonzeroLocus s₁ = nonzeroLocus s ⊓ nonzeroLocus a ∧ side N L ((M.tens A).logSec s₁) (N.logSec t) (divOfSec (M.tens A).φ.isLB s₁ h₁) - side (M.tens A) L (N.logSec t) ((M.tens A).logSec s₁) (divOfSec N.φ.isLB t ht) = (side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) - side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht)) + (side N L (A.logSec a) (N.logSec t) (divOfSec A.φ.isLB a ha) - side A L (N.logSec t) (A.logSec a) (divOfSec N.φ.isLB t ht)) := by
  intro hP F _ X _ _ p σ e hproj hdim L M A N s hs a ha t ht hcod
  obtain ⟨s₁, h₁, hloc, hmult, hlog⟩ := GlobalTheory.T.tensor_product_sections_zeros_multiplicities_norms F X p σ M A s hs a ha
  refine ⟨s₁, h₁, hloc, ?_⟩
  have hσ : Function.Injective σ := σ.injective
  haveI : CompactSpace X := compactSpace_of_projOver hproj
  have iM := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons N L) M s hs
  have iA := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons N L) A a ha
  have iMh := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons M L) N t ht
  have iAh := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons A L) N t ht
  have e1 : Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) ((M.tens A).logSec s₁) =
      Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s) +
        Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (A.logSec a) := by
    refine int_eq_add_of_ae _ iM iA fun ε => ?_
    have h0 := GlobalTheory.T.mixedChernFormSignedPartMeasure_compl_open_genericPoint_eq_zero F X p σ hσ hproj (e + 1) (Fin.cons N L) ε (nonzeroLocus s₁) h₁
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with y hy
    exact hlog y (by simpa using hy)
  have e2 : Mix.int (Fin.cons (M.tens A) L : Fin (e + 1) → MLine p σ) (N.logSec t) =
      Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t) +
        Mix.int (Fin.cons A L : Fin (e + 1) → MLine p σ) (N.logSec t) := by
    have key := GlobalTheory.T.mixedChernIntegral_additive_in_factor F X p σ hproj (e + 1) (Fin.cons M L) 0 M A (N.logSec t)
      (by simpa only [Fin.update_cons_zero] using iMh) (by simpa only [Fin.update_cons_zero] using iAh)
    simpa only [Fin.update_cons_zero] using key.2
  have e3 : ∑ᶠ z, ((divOfSec (M.tens A).φ.isLB s₁ h₁).mult z : ℝ) * cycInt L (N.logSec t) z =
      ∑ᶠ z, ((divOfSec M.φ.isLB s hs).mult z : ℝ) * cycInt L (N.logSec t) z +
        ∑ᶠ z, ((divOfSec A.φ.isLB a ha).mult z : ℝ) * cycInt L (N.logSec t) z := by
    rw [← finsum_add_distrib]
    · refine finsum_congr fun z => ?_
      rw [hmult z]
      push_cast
      ring
    · exact (divOfSec M.φ.isLB s hs).finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
    · exact (divOfSec A.φ.isLB a ha).finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  have e4 : ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L ((M.tens A).logSec s₁) z =
      ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (M.logSec s) z +
        ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (A.logSec a) z := by
    rw [← finsum_add_distrib]
    · refine finsum_congr fun z => ?_
      by_cases hz : (divOfSec N.φ.isLB t ht).mult z = 0
      · simp [hz]
      · rw [← mul_add]
        congr 1
        have hco := CartierDiv.coheight_eq_one_of_mult_ne_zero hz
        have hzt : z ∉ nonzeroLocus t := fun h =>
          (notMem_supp_divOfSec.2 h) (CartierDiv.mem_supp_of_mult_ne_zero hz)
        have hz1 : z ∈ nonzeroLocus s ⊓ nonzeroLocus a := (hcod z hco).resolve_right hzt
        have hz1' := TopologicalSpace.Opens.mem_inf.1 hz1
        have hzs₁ : z ∈ nonzeroLocus s₁ := hloc ▸ hz1
        have hdimz := (GlobalTheory.T.coheight_eq_one_iff_closure_dim_projective F X p e hproj hdim z).1 hco
        obtain ⟨-, -, hnull, hint⟩ := GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure hP F X p σ hproj e L z hdimz
        refine int_eq_add_of_ae _ (hint M s hz1'.1) (hint A a hz1'.2) fun ε => ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hnull _ hzs₁ ε)] with y hy
        exact hlog _ (by simpa using hy)
    · exact (divOfSec N.φ.isLB t ht).finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
    · exact (divOfSec N.φ.isLB t ht).finite_support_mult.subset fun z hz h0 => hz (by simp [h0])
  simp only [side]
  rw [e1, e2, e3, e4]
  ring

end GlobalTheory.DefectAdd
