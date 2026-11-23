import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralBasisCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLatti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOffStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicator
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

noncomputable section

namespace GlobalTheory.ConjPlaceLat

set_option maxHeartbeats 1000000 in

theorem cA_mul_mem_latV_smul : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k) (w : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e w →
  ∀ (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (𝔪 : Ideal (𝓞 D.host.E)), (∃ m ∈ 𝔪, m ∉ (Formalism.DivisionValues.conjPl w).asIdeal) →
  ∀ z : Fin S.rank → AE D, z ∈ latV S L (· = p.v) → (fun i => cA D p.e * z i) ∈ latV S (𝔪 • L) (· = p.v) := by
  intro D k _ _ _ _ p w hw S L 𝔪 hm z hz
  obtain ⟨m, hm𝔪, hmw⟩ := hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hmw (Ideal.zero_mem _)
  have hmE : (m : D.host.E) ≠ 0 := by exact_mod_cast hm0
  have hc := GlobalTheory.SplitHeckeAdj.idem_conj S hw
  have hu : finPart D (cA D p.e * incA D ((m : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hmw ((hc.2 m hm0).2 h)
  have h1 : ∀ y ∈ latV S L (· = p.v), (fun i => incA D (m : D.host.E) * y i) ∈ latV S (𝔪 • L) (· = p.v) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hy
      rw [Set.mem_singleton_iff] at ha
      subst ha
      refine AddSubgroup.subset_closure ⟨α, hαi, hα, 1, rfl, m • x, Submodule.smul_mem_smul hm𝔪 hx, ?_⟩
      funext i
      show (1 : AF D.host.F) ⊗ₜ[D.host.F] (m : D.host.E) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, one_mul, Pi.smul_apply, Algebra.smul_def]
    | zero =>
      convert zero_mem (latV S (𝔪 • L) (· = p.v)) using 1
      funext i
      simp
    | add y y' _ _ h h' =>
      convert add_mem h h' using 1
      funext i
      simp [mul_add]
    | neg y _ h =>
      convert neg_mem h using 1
      funext i
      simp
  have key : (fun i => cA D p.e * z i) =
      fun i => cA D p.e * incA D ((m : D.host.E)⁻¹) * (incA D (m : D.host.E) * z i) := by
    funext i
    rw [mul_assoc, ← mul_assoc (incA D _), ← map_mul, inv_mul_cancel₀ hmE, map_one, one_mul]
  rw [key]
  exact GlobalTheory.FinPl.LatIndHalf.mul_mem_latV hu (h1 z hz)

end GlobalTheory.ConjPlaceLat
