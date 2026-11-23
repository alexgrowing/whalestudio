import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermFD

theorem integrable_of_cover {A : Type*} [AddGroup A] [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [SecondCountableTopology A] [MeasurableAdd A] [ContinuousAdd A] (L : AddSubgroup A) [Countable L]
    (μ : Measure A) [μ.IsAddLeftInvariant] (𝓖 : Set A) (hFD : IsAddFundamentalDomain L 𝓖 μ) (h1 : μ 𝓖 = 1)
    (f : A → ℝ) (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) (hS : Summable (fun ζ : L => f ζ.1))
    (K : Set A) (hK : ∀ x, ∃ γ ∈ L, γ + x ∈ K) (κ : ℝ) (hκ : 0 ≤ κ)
    (hb : ∀ ζ ∈ L, ∀ z ∈ K, f (ζ + z) ≤ κ * f ζ) : Integrable f μ := by
  have hpt : ∀ z : A, ∑' ζ : L, ENNReal.ofReal (f (ζ.1 + z)) ≤ ENNReal.ofReal (κ * ∑' ζ : L, f ζ.1) := by
    intro z
    obtain ⟨γ, hγ, hz⟩ := hK z
    have h2 : ∀ ζ : L, ENNReal.ofReal (f (ζ.1 + z)) ≤
        ENNReal.ofReal (κ * f ((Equiv.subRight (⟨γ, hγ⟩ : L) ζ).1)) := by
      intro ζ
      apply ENNReal.ofReal_le_ofReal
      have e : ζ.1 + z = (ζ.1 - γ) + (γ + z) := by simp [sub_eq_add_neg, add_assoc]
      rw [e]
      exact hb _ (L.sub_mem ζ.2 hγ) _ hz
    refine (ENNReal.tsum_le_tsum h2).trans ?_
    rw [(Equiv.subRight (⟨γ, hγ⟩ : L)).tsum_eq (fun ζ : L => ENNReal.ofReal (κ * f ζ.1)),
      ← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun ζ => mul_nonneg hκ (hf0 _)) (hS.mul_left κ)]
  have hm : ∀ g : L, AEMeasurable (fun x : A => ENNReal.ofReal (f (g +ᵥ x))) (μ.restrict 𝓖) := fun g =>
    (ENNReal.measurable_ofReal.comp (hf.comp (continuous_const.add continuous_id)).measurable).aemeasurable
  have hI : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal (κ * ∑' ζ : L, f ζ.1) := by
    rw [hFD.lintegral_eq_tsum'', ← lintegral_tsum hm]
    calc _ ≤ ∫⁻ _ in 𝓖, ENNReal.ofReal (κ * ∑' ζ : L, f ζ.1) ∂μ :=
          lintegral_mono fun x => hpt x
      _ = _ := by simp [h1]
  exact ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (.of_forall hf0)).2 (hI.trans_lt ENNReal.ofReal_lt_top)⟩

set_option synthInstance.maxHeartbeats 400000 in

theorem integrable_of_periodisation_bound : ∀ (D : D7) (ρ : ℕ) (lz : Measure (hermA D ρ)) (𝓖 : Set (hermA D ρ)), IsCovolOneH lz 𝓖 →
  ∀ f : hermA D ρ → ℝ, Continuous f → (∀ z, 0 ≤ f z) → Summable (fun ζ : ratHerm D ρ => f ζ.1) →
  ∀ K : Set (hermA D ρ), (∀ x, ∃ γ ∈ ratHerm D ρ, γ + x ∈ K) → ∀ κ : ℝ, 0 ≤ κ →
    (∀ ζ ∈ ratHerm D ρ, ∀ z ∈ K, f (ζ + z) ≤ κ * f ζ) → Integrable f lz := by
  intro D ρ lz 𝓖 hC f hf hf0 hS K hK κ hκ hb
  obtain ⟨hlam, hFD, h1⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D ρ ρ
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : ContinuousAdd (hermA D ρ) := ⟨Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)) _⟩
  haveI : MeasurableAdd (hermA D ρ) := ContinuousAdd.measurableAdd
  haveI : DiscreteTopology (ratHerm D ρ) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  haveI : Countable (ratHerm D ρ) := by
    haveI : SecondCountableTopology (ratHerm D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
    exact (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
  exact integrable_of_cover (ratHerm D ρ) lz 𝓖 hFD h1 f hf hf0 hS K hK κ hκ hb

end GlobalTheory.CompanionTheory.HermFD
