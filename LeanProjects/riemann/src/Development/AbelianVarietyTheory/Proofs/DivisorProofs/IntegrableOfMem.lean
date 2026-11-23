import Development.AbelianVarietyTheory.Definitions.Divisors.AnisoClauseOfFirstTerm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaPartialFourierIntegralMemAdelicSchwartz
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SchwartzAInt

open GlobalTheory.RegSch.IkSchwartz GlobalTheory.PartialIntegral

set_option maxHeartbeats 800000 in

theorem integrable_pure {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (μ : Measure (Mx D m n))
    [μ.IsAddHaarMeasure] (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ) (g : (Fin m → Fin n → AEf D) → ℂ)
    (hg : g ∈ WeilM.SB (Fin m → Fin n → AEf D)) :
    Integrable (fun x => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))) μ := by
  haveI : IsModuleTopology (Af D.host.F) (AEf D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AEf D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  haveI : LocallyCompactSpace (AEf D) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AEf D) := e0.secondCountableTopology
  haveI : T2Space (AEf D) := e0.isEmbedding.t2Space
  letI : MeasurableSpace (Fin m → Fin n → AEf D) := borel _
  haveI : BorelSpace (Fin m → Fin n → AEf D) := ⟨rfl⟩
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI := (lattice_Mx D m n).1
  obtain ⟨e, he⟩ := exists_split hθ m n
  let μr : Measure (D.what₂.Tau → Fin m → Fin n → ℂ) := Measure.addHaar
  let ν : Measure (Fin m → Fin n → AEf D) := Measure.addHaar
  obtain ⟨c, hc⟩ := exists_integral_split e μ μr ν
  have hf : Integrable (fun x => f x) μr := f.integrable
  have hg' : Integrable g ν := hg.1.continuous.integrable_of_hasCompactSupport hg.2
  have := (hc _ _ hf hg').1
  convert this using 2 with x
  rw [he]

theorem integrable_of_mem : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (μ : Measure (Mx D m n)) (𝓕 : Set (Mx D m n)),
    IsCovolOne (ratMx D m n) μ 𝓕 → ∀ Φ ∈ schwartzA θ m n, Integrable Φ μ := by
  intro D θ hθ m n μ 𝓕 hμ Φ hΦ
  haveI := hμ.1
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact integrable_pure hθ μ f g hg
  | zero => exact integrable_zero _ _ _
  | add Φ Ψ _ _ h1 h2 => exact h1.add h2
  | smul c Φ _ h => exact h.smul c

end GlobalTheory.SchwartzAInt
