import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRestrictedProdFinAwayIffIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrProdInt

theorem integral_indicator_smul_of_measurePreserving {X Y Z E : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [NormedAddCommGroup E] [NormedSpace ℂ E] {μ : Measure X} {m : Measure Y} {ν : Measure Z}
    [SigmaFinite m] [SigmaFinite ν] (e : X ≃ᵐ Y × Z) (he : MeasurePreserving e μ (m.prod ν)) {B : Set Z}
    (hB : MeasurableSet B) (hBf : ν B ≠ ⊤) {a : Y → E} (ha : Integrable a m) :
    Integrable (fun x => B.indicator (fun _ => (1 : ℂ)) (e x).2 • a (e x).1) μ ∧
      ∫ x, B.indicator (fun _ => (1 : ℂ)) (e x).2 • a (e x).1 ∂μ = (ν B).toReal • ∫ y, a y ∂m := by
  set Φ : Y × Z → E := (univ ×ˢ B).indicator (fun p => a p.1) with hΦdef
  have hΦ : (fun x => B.indicator (fun _ => (1 : ℂ)) (e x).2 • a (e x).1) = Φ ∘ e := by
    funext x
    rw [Function.comp_apply, hΦdef]
    by_cases h : (e x).2 ∈ B
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_prod.2 ⟨Set.mem_univ _, h⟩), one_smul]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hm => h (Set.mem_prod.1 hm).2), zero_smul]
  have hmeasS : MeasurableSet (univ ×ˢ B : Set (Y × Z)) := MeasurableSet.univ.prod hB
  have hres : (m.prod ν).restrict (univ ×ˢ B) = m.prod (ν.restrict B) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  haveI : IsFiniteMeasure (ν.restrict B) := ⟨by simpa using hBf.lt_top⟩
  have hint : Integrable Φ (m.prod ν) := by
    rw [hΦdef, integrable_indicator_iff hmeasS, IntegrableOn, hres]
    exact ha.comp_fst _
  have hval : ∫ p, Φ p ∂(m.prod ν) = (ν B).toReal • ∫ y, a y ∂m := by
    rw [hΦdef, integral_indicator hmeasS, hres, integral_fun_fst]
    simp [Measure.real]
  rw [hΦ]
  refine ⟨(he.integrable_comp_emb e.measurableEmbedding).2 hint, ?_⟩
  rw [show (∫ x, (Φ ∘ e) x ∂μ) = ∫ x, Φ (e x) ∂μ from rfl, he.integral_comp' Φ]
  exact hval

theorem integral_indicatorFin_smul_arch : ∀ (D : D7) (V : HSp D) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)), IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ → ∀ (νF : Measure (GFin D.sp.cm.sig V.gram)), IsRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf νF → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (B : Set (GFin D.sp.cm.sig V.gram)), MeasurableSet B → νF B ≠ ⊤ → ∀ (a : (∀ w, GArch D.sp.cm.sig V.gram w) → E), Integrable a (Measure.pi μa) → Integrable (fun g : GA D V => B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) • a fun w => projArch D.sp.cm.sig V.gram w g) μ ∧ ∫ g, B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) • a (fun w => projArch D.sp.cm.sig V.gram w g) ∂μ = (νF B).toReal • ∫ x, a x ∂Measure.pi μa := by
  intro D V μa μf μ hμ νF hF E _ _ _ B hB hBf a ha
  haveI := SelfDual.isLattice_frameLat V
  have hmap := hμ.map_archFin hF
  haveI : ∀ w, (μa w).IsHaarMeasure := hμ.1
  haveI : νF.IsHaarMeasure := hF.2.2.1
  haveI : ∀ w, SigmaFinite (μa w) := fun w => inferInstance
  haveI : SigmaFinite (Measure.pi μa) := Measure.pi.sigmaFinite _
  haveI : SigmaFinite νF := inferInstance
  exact integral_indicator_smul_of_measurePreserving
    (archFinEquiv D.sp.cm.sig V.gram).toHomeomorph.toMeasurableEquiv
    ⟨(archFinEquiv D.sp.cm.sig V.gram).toHomeomorph.toMeasurableEquiv.measurable, hmap⟩ hB hBf ha

end GlobalTheory.TrProdInt
