import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.ZEul

open Matrix

theorem decomp_lastRow : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ),
    (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) → ∀ N : ℕ,
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) →
    ∀ Φ : (Fin (m + 1) → Cinf E) → ℂ, tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
    GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
    ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), ∃ p ∈ GlobalTheory.JSW.mirS E S m, ∃ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J,
      g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = u * p * finGL E (m + 1) κ := by
  intro E _ _ _ m S J hJ N hN Φ hs g hg hΦ hind
  have hrow : ∀ h : GA E (m + 1), Pi.single (Fin.last m) 1 ᵥ* h.val = fun j => GlobalTheory.ZEul.lastRow h j := fun h => by
    rw [Matrix.single_one_vecMul]; rfl
  have hℓ : ∀ i : Fin (m + 1), i ≤ Fin.last m := Fin.le_last
  have hi : (fun i => pInf E ((Pi.single (Fin.last m) 1 ᵥ* g.val) i)) ∈ GlobalTheory.RSTheta.rowSet E (Fin.last m) := by
    rw [hrow]; exact hs (subset_tsupport _ hΦ)
  have hind' : ∀ i : Fin (m + 1), GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i) - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈
      GlobalTheory.RSJ.natLat E N := by
    by_contra hc
    exact hind (by rw [GlobalTheory.RSJ.indN, if_neg hc])
  have hf : ∀ v ∈ S, ∀ j, Valued.v ((pFin E ((Pi.single (Fin.last m) 1 ᵥ* g.val) j) -
      (Pi.single (Fin.last m) 1 : Fin (m + 1) → Af E) j) v) ≤
      WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) := by
    intro v hv j
    rw [hrow]
    have e : (Pi.single (Fin.last m) 1 : Fin (m + 1) → Af E) j = if (j : ℕ) + 1 = m + 1 then 1 else 0 := by
      rw [Pi.single_apply]
      congr 1
      simp [Fin.ext_iff]
    rw [e]
    exact hN _ (hind' j) v hv
  obtain ⟨u, hu, p, hp, κ, hκ, e⟩ := GlobalTheory.RSLocalPart.exists_decomp hℓ hJ hg hi hf
  refine ⟨u, (GlobalTheory.SmGL.mem_unipB _).1 hu, p, ⟨hp.2, hp.1⟩, κ, hκ, ?_⟩
  rw [← e, hrow]
  congr 1
  rw [hrow] at hi
  have hu' := GlobalTheory.RSTheta.isUnit_of_mem_rowSet hi
  rw [← map_inv]
  congr 1
  have hm : GlobalTheory.RSJ.secRow (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) =
      GlobalTheory.RSTheta.rowMat (Fin.last m) (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) := by
    ext i j
    simp only [GlobalTheory.RSJ.secRow, GlobalTheory.RSTheta.rowMat, Matrix.of_apply, Matrix.updateRow_apply]
    congr 1
    simp [Fin.ext_iff]
  have hd : IsUnit (GlobalTheory.RSJ.secRow (fun i => pInf E (GlobalTheory.ZEul.lastRow g i))).det := by
    rw [hm, GlobalTheory.RSTheta.det_rowMat]; exact hu'
  rw [GlobalTheory.RSJ.secInv, dif_pos hd]
  congr 1
  exact Units.ext (hm.trans (GlobalTheory.RSTheta.val_rowGL hu').symm)

end GlobalTheory.ZEul
