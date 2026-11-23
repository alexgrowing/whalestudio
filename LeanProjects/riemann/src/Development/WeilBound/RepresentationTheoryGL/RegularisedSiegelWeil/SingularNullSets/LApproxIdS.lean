import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdA
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanHaarScalingNormStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

abbrev fixE {F : Type} [Field F] [NumberField F] (ε : AF F) : AddSubgroup (AF F) := fixS (AddMonoidHom.mulLeft ε)

open Classical in

def IsIdF {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F) : Prop :=
  fstA F ε = 1 ∧ ∀ v, (sndA F ε) v = if v ∈ S then 1 else 0

def OneD : Prop := ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsIdF S ε → ∀ ν : Measure (fixE ε), ν.IsAddHaarMeasure →
  ∃ (g : ℕ → fixE ε → ℂ) (G : ℕ → AF F → ℝ) (Sp : ℕ → Set (AF F)),
    (∀ k, Integrable (g k) ν ∧ (∀ h, ‖g k h‖ ≤ 1) ∧ ∀ s, 0 ≤ G k s ∧ ∫ h, g k h * ψ (h.1 * s) ∂ν = G k s) ∧
    (∀ h, Tendsto (fun k => g k h) atTop (𝓝 1)) ∧
    (∀ k s, G k s ≠ 0 → -(ε * s) ∈ Sp k) ∧ Tendsto Sp atTop (𝓝 (0 : AF F)).smallSets

end PositivityTheory.Rg.Rsw.L.LApproxId

end
