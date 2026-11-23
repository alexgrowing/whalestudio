import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMirabolicWhittakerReductionCell
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mirabolic_whittaker_reduction_cell : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (F : GA E (m + 1) → ℂ)
    (U : Subgroup (GL (Fin (m + 1)) (Af E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g) →
    (∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g) →
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    (∀ y : Fin (m + 1) → Af E, y - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ κ ∈ U, (∀ w ∉ T, GeneralLinearGroup.map (pLoc E w) κ = 1) ∧
        ∀ w ∈ T, ∀ j, (GeneralLinearGroup.map (pLoc E w) κ : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) (Fin.last m) j =
          pLoc E w (y j)) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) T, IsUnit (pInf E (g.val (Fin.last m) (Fin.last m))) →
      (fun i => pFin E (g.val (Fin.last m) i)) - Pi.single (Fin.last m) 1 ∈ GlobalTheory.ThetaPoisson.latt (m + 1) J →
      ∃ p ∈ GlobalTheory.JSW.mirS E T m, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T,
        ‖GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g *
          (infGL E (m + 1) (GlobalTheory.RSTheta.rowGL (Fin.last m) (fun i => pInf E (g.val (Fin.last m) i))))⁻¹)‖ =
        ‖GlobalTheory.JSW.whit F (p * GlobalTheory.CellDec.tl (m + 1) ϖ l.1)‖ := by
  first | exact @GlobalTheory.WhitRed.exists_mirabolic | exact GlobalTheory.WhitRed.exists_mirabolic | (intros; apply GlobalTheory.WhitRed.exists_mirabolic <;> assumption)
