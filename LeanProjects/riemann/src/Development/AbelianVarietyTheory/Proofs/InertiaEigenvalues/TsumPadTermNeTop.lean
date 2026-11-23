import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdeles
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsuppVanishingOnEquivComplProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasProdLocalRankinSelbergFactorSelfOfEulerProduc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumSchurSquareCellProductEqEulerProduct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdTsumEqTsumIndicatorEnnreal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerProductRankinSelbergGLnGLmDirichletSeries
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

noncomputable section
namespace GlobalTheory.RSCellEul

open GlobalTheory.RSnmEul GlobalTheory.RSnmUnf

theorem term_le_locFac {m k : ℕ} (h : m + 1 ≤ k) (q : ℕ) (a : Fin k → ℂ) (x : ℝ) (v : Fin (m + 1) → ℤ) :
    (if (∀ i, 0 ≤ v i) ∧ Antitone v then
          ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => (v i).toNat) a‖ ^ 2 *
            (q : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))) else 0) ≤
      GlobalTheory.RSCell.locFac q a x (padInt h v) := by
  split_ifs with hv
  · have hv' := padInt_valid h hv
    rw [GlobalTheory.RSCell.locFac, if_pos ⟨hv'.2, hv'.1⟩, toNat_padInt h v, sum_padNat h]
  · exact bot_le

theorem term_zero {m k : ℕ} (q : ℕ) (a : Fin k → ℂ) (x : ℝ) :
    (if (∀ i, 0 ≤ (0 : Fin (m + 1) → ℤ) i) ∧ Antitone (0 : Fin (m + 1) → ℤ) then
          ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => ((0 : Fin (m + 1) → ℤ) i).toNat) a‖ ^ 2 *
            (q : ℝ) ^ (-(((∑ i, ((0 : Fin (m + 1) → ℤ) i).toNat : ℕ) : ℝ) * x))) else 0) = 1 := by
  have h0 : (fun i : Fin (m + 1) => ((0 : Fin (m + 1) → ℤ) i).toNat) = 0 := funext fun _ => rfl
  rw [if_pos ⟨fun _ => le_rfl, fun _ _ _ => le_rfl⟩, h0, padNat_zero]
  rw [show (0 : Fin k → ℕ) = fun _ => 0 from rfl, GlobalTheory.RSPole.EulerPole.schurAt_const_zero]
  simp

theorem tprod_le_of_one_le {I : Type} (f g : I → ℝ≥0∞) (hf : ∀ i, 1 ≤ f i) (hfg : ∀ i, f i ≤ g i) :
    ∏' i, f i ≤ ∏' i, g i := by
  have hg : ∀ i, 1 ≤ g i := fun i => (hf i).trans (hfg i)
  rw [(GlobalTheory.RSPole.EulerPole.hasProd_of_one_le f hf).tprod_eq, (GlobalTheory.RSPole.EulerPole.hasProd_of_one_le g hg).tprod_eq]
  exact iSup_mono fun s => Finset.prod_le_prod' fun i _ => hfg i

theorem tsum_padTerm_ne_top : ∀ (E : Type) [Field E] [NumberField E] (m k : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), m + 1 ≤ k →
    ∀ (α : HeightOneSpectrum (𝓞 E) → Fin k → ℂ) (x : ℝ),
    GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal) (fun w i => α w.1 i) x ≠ ⊤ →
    ∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, (l.1.prod fun w v => if (∀ i, 0 ≤ v i) ∧ Antitone v then
          ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => (v i).toNat) (α w)‖ ^ 2 *
            (Ideal.absNorm w.asIdeal : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))) else 0) ≠ ⊤ := by
  intro E _ _ m k S hmk α x hfin
  classical
  let g : HeightOneSpectrum (𝓞 E) → (Fin (m + 1) → ℤ) → ℝ≥0∞ := fun w v =>
    if (∀ i, 0 ≤ v i) ∧ Antitone v then
      ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (GlobalTheory.RSnmUnf.padNat (n := k) fun i => (v i).toNat) (α w)‖ ^ 2 *
        (Ideal.absNorm w.asIdeal : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))) else 0
  show ∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, l.1.prod g ≠ ⊤
  have hg0 : ∀ w, g w 0 = 1 := fun w => term_zero _ _ _
  obtain ⟨e, he⟩ := GlobalTheory.finsupp_vanishing_on_equiv_compl_prod S (m + 1)
  let f : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} → (Fin (m + 1) → ℤ) → ℝ≥0∞ := fun i v => g i.1 v
  have h1 : ∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, l.1.prod g = ∑' l' : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ), l'.prod f := by
    rw [← e.tsum_eq]; exact tsum_congr fun l => (he ℝ≥0∞ g hg0 l).symm
  rw [h1, (GlobalTheory.EulerSum.euler_product_intVec_ennreal (m + 1) f fun i => hg0 i.1).2]
  refine ne_top_of_le_ne_top hfin ?_
  rw [GlobalTheory.RSPole.eulD]
  refine tprod_le_of_one_le _ _ (fun i => ?_) (fun i => ?_)
  · exact le_of_eq_of_le (hg0 i.1).symm (ENNReal.le_tsum (f := f i) 0)
  · rw [GlobalTheory.RSCellSum.schurDir_eq_tsum_locFac]
    calc ∑' v, f i v ≤ ∑' v, GlobalTheory.RSCell.locFac (Ideal.absNorm i.1.asIdeal) (α i.1) x (padInt hmk v) :=
          ENNReal.tsum_le_tsum fun v => term_le_locFac hmk _ _ _ v
      _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (padInt_injective hmk) _

end GlobalTheory.RSCellEul
