import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPairThetaLowestStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtRows
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParLaws
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLiftOfReference
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
noncomputable section
namespace GlobalTheory.RefPair
end GlobalTheory.RefPair
namespace GlobalTheory.RefPair
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
set_option maxHeartbeats 1000000 in
theorem referencePair_split_of_mu_eq_zero_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf rep _ _ M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)), NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S → (∃ y ∈ D.what₂.isot j σ, ∃ F ∈ (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real, inner ℂ F (D.what₂.thetaT D.what₂.mu0 j y) ≠ 0) → ∀ (s : SplitPlace D.host.E) (π : GlobalTheory.SmGL.IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E))) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E))), IsLocS (n := D.R.nV) S s π → IsLocS (rep σ).S s τ → GlobalTheory.ThetaGL.ThetaPair ((cf.mu0 ⟨j - 1, by omega⟩).loc s.w) τ.ρ (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (cf.eta.loc s.w))) := by
  intro hN hL
  have hA := _root_.GlobalTheory.T.exists_theta_at_of_third_layer hN hL
  unfold _root_.GlobalTheory.LiftRef.ForallRowSideParameters at hA ⊢
  refine GlobalTheory.LiftRef.overRows_and_mono hA hA ?_
  intro K B f T w Z Wt hX z p0 Y hA1 _ Rw a M tup Q hMA hMI j h1 h2 σ S hS hPair s π τ hπ hτ
  obtain ⟨X, hXd⟩ := hA1 Rw a M tup Q hMA hMI j h1 h2
  obtain ⟨Bf, k1, k2, k3, k4⟩ := GlobalTheory.RowSphSmall.exists_form_rowRepR hN.hc hN.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins σ
  exact thetaPair_of_hasThetaAt hN.what₂.bz _ _ X _ _ hXd σ S hS hPair s π τ hπ hτ
    (GlobalTheory.RowSphSmall.isUnitarisable_of_isLocS _ Bf k1 k2 k3 k4 s τ hτ)
end GlobalTheory.RefPair
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.SplitRead GlobalTheory.NPin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_reference_pair_of_trivial_mu_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.LiftRef.ForallRowSideParameters hL fun D cf rep _ _ M => ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (σ : D.what₂.FT) (S : Submodule ℂ (Formalism.AUTREP.GAf D.host.E D.R.nV → (M D.what₂.mu0 j h1 h2).wt.W)), NG.IsIrrRep (M D.what₂.mu0 j h1 h2).wt.ρ S → (∃ y ∈ D.what₂.isot j σ, ∃ F ∈ (NG.isoTyp (M D.what₂.mu0 j h1 h2).wt.ρ S).comap (M D.what₂.mu0 j h1 h2).real, inner ℂ F (D.what₂.thetaT D.what₂.mu0 j y) ≠ 0) → ∀ (s : SplitPlace D.host.E) (π : GlobalTheory.SmGL.IrrRep (GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E))) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (s.w.adicCompletion D.host.E))), IsLocS (n := D.R.nV) S s π → IsLocS (rep σ).S s τ → GlobalTheory.ThetaGL.ThetaPair ((cf.mu0 ⟨j - 1, by omega⟩).loc s.w) τ.ρ (GlobalTheory.SmGL.twist π.ρ (GlobalTheory.SmGL.detChar (Fin (D.R.r + D.R.t)) (cf.eta.loc s.w))) := by
  first | exact @_root_.GlobalTheory.RefPair.referencePair_split_of_mu_eq_zero_alt | exact _root_.GlobalTheory.RefPair.referencePair_split_of_mu_eq_zero_alt | (intros; apply _root_.GlobalTheory.RefPair.referencePair_split_of_mu_eq_zero_alt <;> assumption)
end
end
