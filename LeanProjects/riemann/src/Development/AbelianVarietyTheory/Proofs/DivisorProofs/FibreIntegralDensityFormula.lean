import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDensityPushforwardIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubsetPartitionNull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartOffClosedSubsetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFibreOverCellStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralDensityChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralPositiveNegativePartsStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical
namespace GlobalTheory.FubIdent

theorem ofReal_abs_eq_add (t : ℝ) : ENNReal.ofReal |t| = ENNReal.ofReal t + ENNReal.ofReal (-t) := by
  rcases le_total 0 t with h | h
  · simp [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (neg_nonpos.2 h)]
  · simp [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h]

theorem core {β α : Type} [MeasurableSpace β] [MeasurableSpace α] (μ : Measure β) (ν : Measure α)
    (K : Set β) (hK : MeasurableSet K) (a G : β → ℝ) (φ : β → α → ℝ)
    (hφ : ∀ u ∈ K, AEMeasurable (φ u) ν) (hint : ∀ u ∈ K, ∫ x, φ u x ∂ν = G u)
    (ha : AEMeasurable a (μ.restrict K)) (hG : AEMeasurable G (μ.restrict K))
    (hpp : AEMeasurable (fun u => ∫⁻ x, ENNReal.ofReal (a u) * ENNReal.ofReal (φ u x) ∂ν) (μ.restrict K))
    (hmp : AEMeasurable (fun u => ∫⁻ x, ENNReal.ofReal (-a u) * ENNReal.ofReal (φ u x) ∂ν) (μ.restrict K))
    (hapos : AEMeasurable (fun u => ∫⁻ x, ENNReal.ofReal |a u| * ENNReal.ofReal (φ u x) ∂ν) (μ.restrict K))
    (haneg : AEMeasurable (fun u => ∫⁻ x, ENNReal.ofReal |a u| * ENNReal.ofReal (-φ u x) ∂ν) (μ.restrict K))
    (hfp : (∫⁻ u in K, ∫⁻ x, ENNReal.ofReal |a u| * ENNReal.ofReal (φ u x) ∂ν ∂μ) ≠ ⊤)
    (hfn : (∫⁻ u in K, ∫⁻ x, ENNReal.ofReal |a u| * ENNReal.ofReal (-φ u x) ∂ν ∂μ) ≠ ⊤) :
    ((∫⁻ u in K, ∫⁻ x, ENNReal.ofReal (a u) * ENNReal.ofReal (φ u x) ∂ν ∂μ) +
        (∫⁻ u in K, ∫⁻ x, ENNReal.ofReal (-a u) * ENNReal.ofReal (-φ u x) ∂ν ∂μ) +
        ((∫⁻ u in K, ENNReal.ofReal (a u) * ENNReal.ofReal (-G u) ∂μ) +
          ∫⁻ u in K, ENNReal.ofReal (-a u) * ENNReal.ofReal (G u) ∂μ) =
      (∫⁻ u in K, ∫⁻ x, ENNReal.ofReal (a u) * ENNReal.ofReal (-φ u x) ∂ν ∂μ) +
        (∫⁻ u in K, ∫⁻ x, ENNReal.ofReal (-a u) * ENNReal.ofReal (φ u x) ∂ν ∂μ) +
        ((∫⁻ u in K, ENNReal.ofReal (a u) * ENNReal.ofReal (G u) ∂μ) +
          ∫⁻ u in K, ENNReal.ofReal (-a u) * ENNReal.ofReal (-G u) ∂μ)) ∧
    (∫⁻ u in K, ENNReal.ofReal |a u| * ENNReal.ofReal (G u) ∂μ) +
        (∫⁻ u in K, ENNReal.ofReal |a u| * ENNReal.ofReal (-G u) ∂μ) ≤
      (∫⁻ u in K, ∫⁻ x, ENNReal.ofReal |a u| * ENNReal.ofReal (φ u x) ∂ν ∂μ) +
        ∫⁻ u in K, ∫⁻ x, ENNReal.ofReal |a u| * ENNReal.ofReal (-φ u x) ∂ν ∂μ := by
  have habs : ∀ u ∈ K, (∫⁻ x, ENNReal.ofReal |a u| * ENNReal.ofReal |φ u x| ∂ν) =
      (∫⁻ x, ENNReal.ofReal |a u| * ENNReal.ofReal (φ u x) ∂ν) +
        ∫⁻ x, ENNReal.ofReal |a u| * ENNReal.ofReal (-φ u x) ∂ν := by
    intro u hu
    rw [← lintegral_add_left' (((hφ u hu).ennreal_ofReal).const_mul _)]
    refine lintegral_congr fun x => ?_
    rw [ofReal_abs_eq_add (φ u x), mul_add]
  have hsum : (∫⁻ u in K, (∫⁻ x, ENNReal.ofReal |a u| * ENNReal.ofReal (φ u x) ∂ν) +
      ∫⁻ x, ENNReal.ofReal |a u| * ENNReal.ofReal (-φ u x) ∂ν ∂μ) ≠ ⊤ := by
    rw [lintegral_add_left' hapos]
    exact ENNReal.add_ne_top.2 ⟨hfp, hfn⟩
  have hfin : ∀ᵐ u ∂μ, u ∈ K →
      (∫⁻ x, ENNReal.ofReal |a u| * ENNReal.ofReal |φ u x| ∂ν) ≠ ⊤ := by
    have h1 := ae_lt_top' (hapos.add haneg) hsum
    rw [ae_restrict_iff' hK] at h1
    filter_upwards [h1] with u hu huK
    rw [habs u huK]
    exact (hu huK).ne
  have hA : AEMeasurable (fun u => |a u|) (μ.restrict K) := continuous_abs.measurable.comp_aemeasurable ha
  have hc1 : AEMeasurable (fun u => ENNReal.ofReal (a u) * ENNReal.ofReal (-G u)) (μ.restrict K) :=
    ha.ennreal_ofReal.mul hG.neg.ennreal_ofReal
  have hc2 : AEMeasurable (fun u => ENNReal.ofReal (-a u) * ENNReal.ofReal (G u)) (μ.restrict K) :=
    ha.neg.ennreal_ofReal.mul hG.ennreal_ofReal
  have hc3 : AEMeasurable (fun u => ENNReal.ofReal (a u) * ENNReal.ofReal (G u)) (μ.restrict K) :=
    ha.ennreal_ofReal.mul hG.ennreal_ofReal
  have hc4 : AEMeasurable (fun u => ENNReal.ofReal (-a u) * ENNReal.ofReal (-G u)) (μ.restrict K) :=
    ha.neg.ennreal_ofReal.mul hG.neg.ennreal_ofReal
  have hc5 : AEMeasurable (fun u => ENNReal.ofReal |a u| * ENNReal.ofReal (G u)) (μ.restrict K) :=
    hA.ennreal_ofReal.mul hG.ennreal_ofReal
  refine ⟨?_, ?_⟩
  · have eL : ((∫⁻ u in K, ∫⁻ x, ENNReal.ofReal (a u) * ENNReal.ofReal (φ u x) ∂ν ∂μ) +
        (∫⁻ u in K, ∫⁻ x, ENNReal.ofReal (-a u) * ENNReal.ofReal (-φ u x) ∂ν ∂μ) +
        ((∫⁻ u in K, ENNReal.ofReal (a u) * ENNReal.ofReal (-G u) ∂μ) +
          ∫⁻ u in K, ENNReal.ofReal (-a u) * ENNReal.ofReal (G u) ∂μ)) =
        ∫⁻ u in K, ((∫⁻ x, ENNReal.ofReal (a u) * ENNReal.ofReal (φ u x) ∂ν) +
          (∫⁻ x, ENNReal.ofReal (-a u) * ENNReal.ofReal (-φ u x) ∂ν)) +
          (ENNReal.ofReal (a u) * ENNReal.ofReal (-G u) + ENNReal.ofReal (-a u) * ENNReal.ofReal (G u)) ∂μ := by
      have h12 : AEMeasurable (fun u => ENNReal.ofReal (a u) * ENNReal.ofReal (-G u) +
          ENNReal.ofReal (-a u) * ENNReal.ofReal (G u)) (μ.restrict K) := hc1.add hc2
      rw [lintegral_add_right' _ h12, lintegral_add_left' hpp, lintegral_add_left' hc1]
    have eR : ((∫⁻ u in K, ∫⁻ x, ENNReal.ofReal (a u) * ENNReal.ofReal (-φ u x) ∂ν ∂μ) +
        (∫⁻ u in K, ∫⁻ x, ENNReal.ofReal (-a u) * ENNReal.ofReal (φ u x) ∂ν ∂μ) +
        ((∫⁻ u in K, ENNReal.ofReal (a u) * ENNReal.ofReal (G u) ∂μ) +
          ∫⁻ u in K, ENNReal.ofReal (-a u) * ENNReal.ofReal (-G u) ∂μ)) =
        ∫⁻ u in K, ((∫⁻ x, ENNReal.ofReal (a u) * ENNReal.ofReal (-φ u x) ∂ν) +
          (∫⁻ x, ENNReal.ofReal (-a u) * ENNReal.ofReal (φ u x) ∂ν)) +
          (ENNReal.ofReal (a u) * ENNReal.ofReal (G u) + ENNReal.ofReal (-a u) * ENNReal.ofReal (-G u)) ∂μ := by
      have h34 : AEMeasurable (fun u => ENNReal.ofReal (a u) * ENNReal.ofReal (G u) +
          ENNReal.ofReal (-a u) * ENNReal.ofReal (-G u)) (μ.restrict K) := hc3.add hc4
      rw [lintegral_add_right' _ h34, lintegral_add_right' _ hmp, lintegral_add_left' hc3]
    rw [eL, eR]
    refine setLIntegral_congr_fun_ae hK ?_
    filter_upwards [hfin] with u hfu huK
    have F := GlobalTheory.T.lintegral_positive_negative_parts α ν (a u) (G u) (φ u) (hφ u huK) (hint u huK)
    have m1 : AEMeasurable (fun x => ENNReal.ofReal (a u) * ENNReal.ofReal (φ u x)) ν :=
      ((hφ u huK).ennreal_ofReal).const_mul _
    have m2 : AEMeasurable (fun x => ENNReal.ofReal (a u) * ENNReal.ofReal (-φ u x)) ν :=
      ((hφ u huK).neg.ennreal_ofReal).const_mul _
    rw [← lintegral_add_left' m1, ← lintegral_add_left' m2]
    exact F.2 (hfu huK)
  · have eA : (∫⁻ u in K, ENNReal.ofReal |a u| * ENNReal.ofReal (G u) ∂μ) +
        (∫⁻ u in K, ENNReal.ofReal |a u| * ENNReal.ofReal (-G u) ∂μ) =
        ∫⁻ u in K, ENNReal.ofReal |a u| * ENNReal.ofReal |G u| ∂μ := by
      rw [← lintegral_add_left' hc5]
      refine lintegral_congr fun u => ?_
      rw [ofReal_abs_eq_add (G u), mul_add]
    rw [eA, ← lintegral_add_left' hapos]
    refine setLIntegral_mono_ae (hapos.add haneg) ?_
    filter_upwards with u huK
    rw [← habs u huK]
    exact (GlobalTheory.T.lintegral_positive_negative_parts α ν (a u) (G u) (φ u) (hφ u huK) (hint u huK)).1

end GlobalTheory.FubIdent

namespace GlobalTheory.FubIdent

theorem cell_balance : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (n r D : ℕ) (ε : Fin D ≃ Fin n ⊕ Low r) (σ : k →+* ℂ) [IsIntegral Y] (c : AlgChart q σ n) (c' : AlgChart p σ D), IsArithVar q n → IsArithVar p D → IsCell ε π w c c' → ∀ (ρ : AlgChart p σ D → CxPts p σ → ℝ) (g : AlgChart q σ n → CxPts q σ → ℝ) (f : CxPts q σ → ℝ), IsDens ρ → IsDens g → Measurable f → (∀ u ∈ c.e.target, ∫ x : Low r → ℂ, ρ c' (c'.e.symm (pt ε u x)) = g c (c.e.symm u)) → ∀ A : Set (CxPts q σ), MeasurableSet A → A ⊆ c.e.source → (∫⁻ y in PtsOver.map π w (spMap σ) ⁻¹' A, ENNReal.ofReal |f (PtsOver.map π w (spMap σ) y)| ∂part ρ) ≠ ⊤ → (∫⁻ y in PtsOver.map π w (spMap σ) ⁻¹' A, ENNReal.ofReal |f (PtsOver.map π w (spMap σ) y)| ∂part fun c y => -ρ c y) ≠ ⊤ → ((∫⁻ y in PtsOver.map π w (spMap σ) ⁻¹' A, ENNReal.ofReal (f (PtsOver.map π w (spMap σ) y)) ∂part ρ) + (∫⁻ y in PtsOver.map π w (spMap σ) ⁻¹' A, ENNReal.ofReal (-f (PtsOver.map π w (spMap σ) y)) ∂part fun c y => -ρ c y) + ((∫⁻ u in A, ENNReal.ofReal (f u) ∂part fun c y => -g c y) + ∫⁻ u in A, ENNReal.ofReal (-f u) ∂part g) = (∫⁻ y in PtsOver.map π w (spMap σ) ⁻¹' A, ENNReal.ofReal (f (PtsOver.map π w (spMap σ) y)) ∂part fun c y => -ρ c y) + (∫⁻ y in PtsOver.map π w (spMap σ) ⁻¹' A, ENNReal.ofReal (-f (PtsOver.map π w (spMap σ) y)) ∂part ρ) + ((∫⁻ u in A, ENNReal.ofReal (f u) ∂part g) + ∫⁻ u in A, ENNReal.ofReal (-f u) ∂part fun c y => -g c y)) ∧ (∫⁻ u in A, ENNReal.ofReal |f u| ∂part g) + (∫⁻ u in A, ENNReal.ofReal |f u| ∂part fun c y => -g c y) ≤ (∫⁻ y in PtsOver.map π w (spMap σ) ⁻¹' A, ENNReal.ofReal |f (PtsOver.map π w (spMap σ) y)| ∂part ρ) + ∫⁻ y in PtsOver.map π w (spMap σ) ⁻¹' A, ENNReal.ofReal |f (PtsOver.map π w (spMap σ) y)| ∂part fun c y => -ρ c y := by
  intro k _ B Y q p π w n r D ε σ _ c c' hq hp hcell ρ g f hρ hg hf hint A hA hAs hfin1 hfin2
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hq.isProjOver
  have hρ' : IsDens (fun c y => -ρ c y) :=
    (GlobalTheory.MixDens.isDens_zero.sub hρ).congr (fun _ _ _ => by simp)
  have hg' : IsDens (fun c y => -g c y) :=
    (GlobalTheory.MixDens.isDens_zero.sub hg).congr (fun _ _ _ => by simp)
  have hKt : c.e '' A ⊆ c.e.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact c.e.map_source (hAs hy)
  have hK : MeasurableSet (c.e '' A) :=
    ReciprocityTheory.L2DbarEstimates.measurableSet_image_of_chart n c.e c.e (fun _ _ => rfl) A hA hAs
  have hpt : ∀ u ∈ c.e.target, ∀ x, pt ε u x ∈ c'.e.target := by
    intro u hu x
    rw [hcell.2.1]
    show base ε (pt ε u x) ∈ c.e.target
    rw [base_pt]
    exact hu
  have hcont : ∀ u ∈ c.e.target, Continuous (fun x : Low r → ℂ => ρ c' (c'.e.symm (pt ε u x))) := by
    intro u hu
    refine (hρ.2 c').comp_continuous ?_ (hpt u hu)
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    generalize ε j = s
    cases s <;> simp [continuous_const, continuous_apply]
  have mP : Measurable (fun u => ENNReal.ofReal (f u)) := hf.ennreal_ofReal
  have mN : Measurable (fun u => ENNReal.ofReal (-f u)) := hf.neg.ennreal_ofReal
  have mA : Measurable (fun u => ENNReal.ofReal |f u|) :=
    (continuous_abs.measurable.comp hf).ennreal_ofReal
  have C1 := GlobalTheory.T.lintegral_fibre_over_cell k B Y q p π w n r D ε σ c c' hp hcell ρ hρ A hA hAs _ mP
  have C2 := GlobalTheory.T.lintegral_fibre_over_cell k B Y q p π w n r D ε σ c c' hp hcell _ hρ' A hA hAs _ mN
  have C3 := GlobalTheory.T.lintegral_fibre_over_cell k B Y q p π w n r D ε σ c c' hp hcell _ hρ' A hA hAs _ mP
  have C4 := GlobalTheory.T.lintegral_fibre_over_cell k B Y q p π w n r D ε σ c c' hp hcell ρ hρ A hA hAs _ mN
  have C5 := GlobalTheory.T.lintegral_fibre_over_cell k B Y q p π w n r D ε σ c c' hp hcell ρ hρ A hA hAs _ mA
  have C6 := GlobalTheory.T.lintegral_fibre_over_cell k B Y q p π w n r D ε σ c c' hp hcell _ hρ' A hA hAs _ mA
  have H1 := GlobalTheory.T.lintegral_density_chart k B q σ n _ hg' c A hA hAs _ mP
  have H2 := GlobalTheory.T.lintegral_density_chart k B q σ n g hg c A hA hAs _ mN
  have H3 := GlobalTheory.T.lintegral_density_chart k B q σ n g hg c A hA hAs _ mP
  have H4 := GlobalTheory.T.lintegral_density_chart k B q σ n _ hg' c A hA hAs _ mN
  have H5 := GlobalTheory.T.lintegral_density_chart k B q σ n g hg c A hA hAs _ mA
  have H6 := GlobalTheory.T.lintegral_density_chart k B q σ n _ hg' c A hA hAs _ mA
  rw [C5.1] at hfin1
  rw [C6.1] at hfin2
  rw [C1.1, C2.1, C3.1, C4.1, C5.1, C6.1, H1, H2, H3, H4, H5, H6]
  exact core volume volume (c.e '' A) hK (fun u => f (c.e.symm u)) (fun u => g c (c.e.symm u))
    (fun u x => ρ c' (c'.e.symm (pt ε u x))) (fun u hu => (hcont u (hKt hu)).aemeasurable)
    (fun u hu => hint u (hKt hu))
    (hf.comp_aemeasurable ((c.e.continuousOn_symm.mono hKt).aemeasurable hK))
    (((hg.2 c).mono hKt).aemeasurable hK) C1.2 C4.2 C5.2 C6.2 hfin1 hfin2

end GlobalTheory.FubIdent
