import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLelongFormulaSectionProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralAdditiveInFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleLogSectionNormProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSectionIntegrableMixedChernProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormFiniteIntegrablePointClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureEqOfIsometricProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureComplOpenGenericP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureFiniteIntegrableProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightEqOneIffClosureDimProjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MetricIndep

theorem compactSpace_of_projOver {R : Type} [CommRing R] {X : Scheme.{0}} {f : X ⟶ Sp R}
    (h : IsProjOver f) : CompactSpace X := by
  obtain ⟨m, i, hi, rfl⟩ := h
  have := isProper_str R m
  have : IsProper (i ≫ PSpace.str R m) := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str R m)

theorem int_sub_half {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (L : Fin D → MLine p σ) {f v : CxPts p σ → ℝ} (hf : Intg L f) (hv : Intg L v) :
    Mix.int L (fun y => f y - v y / 2) = Mix.int L f - Mix.int L v / 2 := by
  unfold Mix.int
  rw [integral_sub hf.1 (hv.1.div_const 2), integral_sub hf.2 (hv.2.div_const 2),
    integral_div, integral_div]
  ring

theorem upd_cons {α : Type*} {n : ℕ} (a b : α) (L : Fin n → α) :
    Function.update (Fin.cons a L : Fin (n + 1) → α) 0 b = Fin.cons b L :=
  Fin.update_cons_zero (α := fun _ => α) a L b

theorem side_sub_side_addFn : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), side N L ((M.addFn u hu).logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) - side (M.addFn u hu) L (N.logSec t) ((M.addFn u hu).logSec s) (divOfSec N.φ.isLB t ht) = side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) - side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP F _ X _ _ p σ e hproj hdim L M N s hs t ht hcod u hu
  have hσ : Function.Injective σ := σ.injective
  have hcont : Continuous u := continuous_iff_continuousAt.2 fun y => (hu y).continuousAt
  have hcomp : CompactSpace X := compactSpace_of_projOver hproj
  obtain ⟨-, -, -, hlog⟩ := GlobalTheory.Mix.SecNorm.logSec_basic F X p σ M s

  have hA : Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) ((M.addFn u hu).logSec s) =
      Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) (M.logSec s) -
        Mix.int (Fin.cons N L : Fin (e + 1) → MLine p σ) u / 2 := by
    have hae : ∀ ε : ℤˣ, (M.addFn u hu).logSec s =ᵐ[part (Fin.cons N L : Fin (e + 1) → MLine p σ) ε]
        fun y => M.logSec s y - u y / 2 := by
      intro ε
      refine ae_iff.2 (measure_mono_null (fun y hy => ?_)
        (GlobalTheory.MixNull.part_compl_null F X p σ hσ hproj (e + 1) (Fin.cons N L) ε (nonzeroLocus s) hs))
      exact fun hy' => hy (hlog u hu y hy')
    have hf := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons N L) M s hs
    have hv := (GlobalTheory.T.mixedChernMeasure_finite_integrable_projective hP F X p σ (e + 1) hproj hdim (Fin.cons N L)).2 u hcont
    rw [← int_sub_half _ hf hv]
    unfold Mix.int
    rw [integral_congr_ae (hae 1), integral_congr_ae (hae (-1))]

  have hB : Mix.int (Fin.cons (M.addFn u hu) L : Fin (e + 1) → MLine p σ) (N.logSec t) =
      Mix.int (Fin.cons M L : Fin (e + 1) → MLine p σ) (N.logSec t) +
        Mix.int (Fin.cons (MLine.ofFun u hu) L : Fin (e + 1) → MLine p σ) (N.logSec t) := by
    obtain ⟨hrefl, -, -, -, haddFn, -⟩ := GlobalTheory.Mix.isom_calculus F X X p p σ (𝟙 X) (Category.id_comp p)
    have hpart : ∀ ε : ℤˣ, part (Fin.cons (M.addFn u hu) L : Fin (e + 1) → MLine p σ) ε =
        part (Fin.cons (M.tens (MLine.ofFun u hu)) L : Fin (e + 1) → MLine p σ) ε :=
      GlobalTheory.Mix.part_eq_of_isom F X p σ hproj (e + 1) _ _ fun i => Fin.cases (haddFn M u hu) (fun j => hrefl (L j)) i
    have h1 := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons M L) N t ht
    have h2 := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP F X p σ (e + 1) hproj hdim (Fin.cons (MLine.ofFun u hu) L) N t ht
    have hadd := GlobalTheory.T.mixedChernIntegral_additive_in_factor F X p σ hproj (e + 1) (Fin.cons M L : Fin (e + 1) → MLine p σ) 0 M
      (MLine.ofFun u hu) (N.logSec t)
    rw [upd_cons, upd_cons, upd_cons] at hadd
    replace hadd := hadd h1 h2
    rw [← hadd.2]
    unfold Mix.int
    rw [hpart, hpart]

  have hC : ∀ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L ((M.addFn u hu).logSec s) z =
      ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (M.logSec s) z -
        ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L u z / 2 := by
    intro z
    by_cases h : (divOfSec N.φ.isLB t ht).mult z = 0
    · simp [h]
    have hz1 := CartierDiv.coheight_eq_one_of_mult_ne_zero h
    have hzs : z ∈ nonzeroLocus s := (hcod z hz1).resolve_right fun hzt =>
      (notMem_supp_divOfSec.2 hzt) (CartierDiv.mem_supp_of_mult_ne_zero h)
    have hdz := (GlobalTheory.FieldDimCoheight.coheight_eq_one_iff F X p e hproj hdim z).1 hz1
    obtain ⟨-, hcc, hnull, hlc⟩ := GlobalTheory.T.mixedChernForm_finite_integrable_pointClosure hP F X p σ hproj e L z hdz
    have hae : ∀ ε : ℤˣ, (fun y => (M.addFn u hu).logSec s (ptMap (closι z) rfl σ y)) =ᵐ[part (fun i => (L i).pull (closι z) rfl) ε]
        fun y => M.logSec s (ptMap (closι z) rfl σ y) - u (ptMap (closι z) rfl σ y) / 2 := by
      intro ε
      refine ae_iff.2 (measure_mono_null (fun y hy => ?_) (hnull (nonzeroLocus s) hzs ε))
      exact fun hy' => hy (hlog u hu _ hy')
    have hcyc : cycInt L ((M.addFn u hu).logSec s) z = cycInt L (M.logSec s) z - cycInt L u z / 2 := by
      have e2 := int_sub_half (fun i => (L i).pull (closι z) rfl) (hlc M s hzs) (hcc u hcont)
      unfold cycInt
      rw [← e2]
      unfold Mix.int
      rw [integral_congr_ae (hae 1), integral_congr_ae (hae (-1))]
    rw [hcyc]
    ring
  have hfs := CartierDiv.finite_support_mult (divOfSec N.φ.isLB t ht)
  have hsub : ∀ g : X → ℝ, (Function.support fun z => ((divOfSec N.φ.isLB t ht).mult z : ℝ) * g z).Finite :=
    fun g => hfs.subset fun z hz h0 => hz (by simp [h0])
  have hsum : ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L ((M.addFn u hu).logSec s) z =
      ∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L (M.logSec s) z -
        (∑ᶠ z, ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L u z) / 2 := by
    simp only [hC]
    rw [div_eq_mul_inv, finsum_mul]
    exact finsum_sub_distrib (hsub _) ((hsub (fun z => cycInt L u z)).subset fun z hz h0 => hz (by
      have h1 : ((divOfSec N.φ.isLB t ht).mult z : ℝ) * cycInt L u z = 0 := h0
      simp only [h1, zero_div]))
  have hPL := GlobalTheory.T.poincareLelong_formula_section_projective hP F X p σ e hproj hdim L N t ht u hu
  simp only [side]
  rw [hA, hB, hsum]
  linarith

end GlobalTheory.MetricIndep
