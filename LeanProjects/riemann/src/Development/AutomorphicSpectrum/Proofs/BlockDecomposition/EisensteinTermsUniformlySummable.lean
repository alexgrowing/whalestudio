import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainFourierUnfolding
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BigCellCosetsHermitianParam
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinConvergent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowD
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf

theorem law_facts : ∀ {D : D7} {n : ℕ} {χ : (AE D)ˣ →* Circle} {s : ℂ} {f : G D n → ℂ}, IsHeckeChar D χ → Continuous f → IsLaw χ s f → (n : ℝ) / 2 < s.re →
    LeftInv (P D n ⊓ GF D n) f ∧
    (∀ q ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat q) = a.1 → Matrix.GeneralLinearGroup.det a = 1 → ∀ g, f (q * g) = f g) ∧
    ∀ C : Set (G D n), IsCompact C → ∃ u : Cosets (P D n) (GF D n) → ℝ, Summable u ∧ ∀ q, ∀ g ∈ C, ‖term (P D n) (GF D n) f g q‖ ≤ u q := by
  intro D n χ s f hχ hc hl hs
  haveI := t2Space_adeleRing' (F := D.host.F)
  refine ⟨fun γ hγ g => ?_, fun q hq a ha h1 g => ?_, fun C hC => ?_⟩
  · obtain ⟨hp, hr⟩ := Subgroup.mem_inf.1 hγ
    obtain ⟨a, ha⟩ := exists_blkA hp
    obtain ⟨u, hu⟩ := det_rat hr a ha
    have h1 : absA D (Matrix.GeneralLinearGroup.det a) = 1 := by
      rw [hu]; exact absE_inclR u
    have h2 : χ (Matrix.GeneralLinearGroup.det a) = 1 := by
      rw [hu]; exact hχ.2 u
    rw [hl γ hp a ha g, h1, h2]
    simp [npow]
  · rw [hl q hq a ha g, h1]
    simp [npow]
  · have hlaw : IndLaw (GlobalTheory.StdUnn.PolesModel.modP (D := D) (n := n))
        (χ.comp GlobalTheory.StdUnn.PolesModel.detP) (s + (n : ℂ) / 2) f := fun p g =>
      hl p p.2 (GlobalTheory.StdUnn.HeightExists.leviBlock (D := D) (n := n) p) rfl g
    have h1 : Continuous (iwAbs (PolesModel.modP (D := D) (n := n)) (K D n)) :=
      PolesModel.isIwasawa.continuous_iwAbs GlobalTheory.StdUnn.Model.isClosed_P PolesModel.continuous_modP GlobalTheory.StdUnn.Model.isCompact_K
    have h2 : Continuous fun g => Real.log (iwAbs (PolesModel.modP (D := D) (n := n)) (K D n) g) :=
      (NNReal.continuous_coe.comp h1).log fun g => (NNReal.coe_pos.2 (iwAbs_pos _ _ g)).ne'
    have hcf : Continuous fun x : ℂ × G D n => flatSec (PolesModel.modP (D := D) (n := n)) (K D n) f s x.1 x.2 := by
      simp only [flatSec, npow_eq_exp (iwAbs_pos _ _ _)]
      exact (hc.comp continuous_snd).mul (((Complex.continuous_ofReal.comp (h2.comp continuous_snd)).mul
        (continuous_fst.sub continuous_const)).cexp)
    obtain ⟨u, hu, hb⟩ := exists_majorant (Φ := fun z => flatSec (PolesModel.modP (D := D) (n := n)) (K D n) f s z)
      (χ := χ.comp PolesModel.detP) (ρ := (n : ℝ) / 2) (σ := (n : ℝ) / 2) PolesModel.isIwasawa GlobalTheory.StdUnn.Model.isCompact_K
      hcf.continuousOn
      (fun z _ => by
        have := (PolesModel.isIwasawa (D := D) (n := n)).indLaw_flatSec hlaw z
        push_cast
        exact this) PolesModel.summable_spherical (S := {s}) isCompact_singleton (Set.singleton_subset_iff.2 hs) hC
    have e : flatSec (PolesModel.modP (D := D) (n := n)) (K D n) f s s = f := funext fun x => by
      simp [flatSec, npow_eq_exp (iwAbs_pos _ _ _)]
    refine ⟨u, hu, fun q g hg => ?_⟩
    have := hb q s rfl g hg
    rwa [e] at this

end GlobalTheory.CompanionTheory.ZUnf
