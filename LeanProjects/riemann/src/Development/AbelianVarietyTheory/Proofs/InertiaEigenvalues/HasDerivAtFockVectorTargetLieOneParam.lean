import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftInfinityTypesAtRealPlace

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

namespace GlobalTheory.FockDerivP

def frONB {D : D7} {V : HSp D} (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hB : ∀ τ, IsONBasis (gramAt D V τ) 1 (B τ) V.rank) : GlobalTheory.ChainFr.Fr V where
  ε _ _ := true
  fr τ := (B τ)⁻¹
  fr_unit τ := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _
    ((Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hB τ))))
  fr_gram τ := by
    have hu : IsUnit (B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hB τ))
    obtain ⟨ε, hε, hG, -⟩ := hB τ
    have h1 : (fun a => (ε a : ℂ)) = fun _ => 1 := by
      funext a
      rcases hε a with h | h
      · rw [h.1]; simp
      · exact absurd h.2 (not_le.2 a.2)
    rw [h1, Matrix.diagonal_one] at hG
    have hJ : Formalism.REAL.Jm (fun _ : Fin V.rank => true) = 1 := by
      simp [Formalism.REAL.Jm]
    have h2 : ((B τ)⁻¹)ᴴ * (B τ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one]
    calc ((B τ)⁻¹)ᴴ * Formalism.REAL.Jm (fun _ : Fin V.rank => true) * (B τ)⁻¹
        = ((B τ)⁻¹)ᴴ * ((B τ)ᴴ * gramAt D V τ * B τ) * (B τ)⁻¹ := by rw [hJ, hG]
      _ = (((B τ)⁻¹)ᴴ * (B τ)ᴴ) * gramAt D V τ * (B τ * (B τ)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = gramAt D V τ := by rw [h2, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]

theorem frONB_cart {D : D7} {V : HSp D} (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hB : ∀ τ, IsONBasis (gramAt D V τ) 1 (B τ) V.rank) : (frONB B hB).cart = fun _ => 1 := by
  funext τ
  have hu : IsUnit (B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hB τ))
  have hJ : Formalism.REAL.Jm (fun _ : Fin V.rank => true) = 1 := by
    simp [Formalism.REAL.Jm]
  show ((B τ)⁻¹)⁻¹ * Formalism.REAL.Jm (fun _ : Fin V.rank => true) * (B τ)⁻¹ = 1
  rw [hJ, Matrix.mul_one, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_nonsing_inv _ hu]

theorem frONB_onb {D : D7} {V : HSp D} (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hB : ∀ τ, IsONBasis (gramAt D V τ) 1 (B τ) V.rank) : (frONB B hB).onb = B := by
  funext τ
  have hu : IsUnit (B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hB τ))
  show ((B τ)⁻¹)⁻¹ = B τ
  rw [Matrix.nonsing_inv_nonsing_inv _ hu]

theorem hasDerivAt_ptP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∃ a : ℂ, ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (z : WO (Vc D i) (Wc D i)), HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t (fockT τ (fun _ : Fin (Vc D i).rank => true) (fun j : Fin (Wc D i).rank => decide ((j : ℕ) < pS D i τ)) ((R.MW i (sg0 D A)).fr τ * Y * ((R.MW i (sg0 D A)).fr τ)⁻¹) P + a • P) z) 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t τ Y hY
  have hC := hG.core
  have hB := hC.models.BV i
  set AV := frONB (R.BV i) hB with hAV
  set BW := GlobalTheory.ChainFr.Fr.ofModel (R.MW i (sg0 D A)) with hBW
  have hcA := frONB_cart (R.BV i) hB
  have hoA := frONB_onb (R.BV i) hB
  obtain ⟨hf, hv, -⟩ := GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t
  have hvac : GlobalTheory.ChainFr.IsVacF R.ψ R.θ AV BW (R.vP i t) := by
    refine ⟨hf, fun ρ => ?_⟩
    rw [hcA]
    exact hv ρ
  have hI := GlobalTheory.PairInfTypes.infTypesAt D T R.toLevCh A.μ0 hC.lev i t τ
  have hAll := GlobalTheory.LieScalar.lieFockAll D (Vc D i) (Wc D i) AV BW R.θ R.ψ _ _ (R.ωP i t) (R.vP i t) τ _ _
    hC.models.inf (hC.thP.ωP i t) hI.chiV hI.chiW hvac
  refine ⟨((-eS D i τ : ℚ) : ℂ) * Y.trace, fun P z => ?_⟩
  have hpt : GlobalTheory.ChainFr.ptF R.ψ R.θ AV BW (R.vP i t) = R.ptP i t := by
    unfold GlobalTheory.ChainFr.ptF RealDat.ptP
    rw [hcA, hoA]
    rfl
  have hε : BW.ε τ = fun j : Fin (Wc D i).rank => decide ((j : ℕ) < pS D i τ) := by
    funext j
    exact hC.models.order i τ j
  have h := hAll.2 Y hY P z
  rw [hpt, hε] at h
  exact h

end GlobalTheory.FockDerivP

end
