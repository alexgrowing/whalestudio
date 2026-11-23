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

namespace GlobalTheory.CompanionTheory.PcAdd

theorem iterated_sub {Z X : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    [TopologicalSpace X] [FirstCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (l : Measure Z) (u : Measure X) [IsFiniteMeasure l] [IsFiniteMeasure u] (a b : X → Z → ℂ) (A B : ℝ)
    (ha : ∀ x, Continuous (a x)) (hb : ∀ x, Continuous (b x))
    (ha' : ∀ z, Continuous fun x => a x z) (hb' : ∀ z, Continuous fun x => b x z)
    (hA : ∀ x z, ‖a x z‖ ≤ A) (hB : ∀ x z, ‖b x z‖ ≤ B) :
    ∫ x, ∫ z, (a x z - b x z) ∂l ∂u = (∫ x, ∫ z, a x z ∂l ∂u) - ∫ x, ∫ z, b x z ∂l ∂u := by
  have key : ∀ c : X → Z → ℂ, ∀ C : ℝ, (∀ x, Continuous (c x)) → (∀ z, Continuous fun x => c x z) →
      (∀ x z, ‖c x z‖ ≤ C) → (∀ x, Integrable (c x) l) ∧ Integrable (fun x => ∫ z, c x z ∂l) u := by
    intro c C hc hc' hC
    have hi : ∀ x, Integrable (c x) l := fun x =>
      Integrable.of_bound (hc x).aestronglyMeasurable C (Eventually.of_forall (hC x))
    refine ⟨hi, ?_⟩
    have hcont : Continuous fun x => ∫ z, c x z ∂l :=
      continuous_of_dominated (bound := fun _ => C) (fun x => (hc x).aestronglyMeasurable)
        (fun x => Eventually.of_forall (hC x)) (integrable_const C) (Eventually.of_forall hc')
    refine Integrable.of_bound hcont.aestronglyMeasurable (C * l.real Set.univ)
      (Eventually.of_forall fun x => ?_)
    exact norm_integral_le_of_norm_le_const (Eventually.of_forall (hC x))
  obtain ⟨i1, j1⟩ := key a A ha ha' hA
  obtain ⟨i2, j2⟩ := key b B hb hb' hB
  rw [← integral_sub j1 j2]
  exact integral_congr_ae (Eventually.of_forall fun x => integral_sub (i1 x) (i2 x))

theorem firstCountable_of_second (X : Type*) [TopologicalSpace X] [SecondCountableTopology X] :
    FirstCountableTopology X := inferInstance

theorem pc_sub : PcBound → ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p)
    (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F F' : G D n → ℂ), Continuous F →
    LeftInv (GF D n) F → Continuous F' → LeftInv (GF D n) F' → ∀ (y : Mx D ρ p) (g : G D n),
    pc M m ψ b₀ (F - F') (M.sh y * g) = pc M m ψ b₀ F (M.sh y * g) - pc M m ψ b₀ F' (M.sh y * g) := by
  intro hP D n ρ p hn M m ψ hψ b₀ F F' hF hFi hF' hFi' y g
  obtain ⟨C, hC, hCm, -⟩ := (hP D n ρ p hn M m ψ hψ b₀).2 (g)
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (Mx D ρ p) := (GlobalTheory.MixModel.lattice_Mx D ρ p).2.2.1
  haveI : FirstCountableTopology (Mx D ρ p) := firstCountable_of_second _
  haveI h1 : IsFiniteMeasure (m.lz.restrict m.𝓖) :=
    ⟨by rw [Measure.restrict_apply_univ, m.hz.2.2]; exact ENNReal.one_lt_top⟩
  haveI h2 : IsFiniteMeasure (m.μ.restrict m.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, m.hμ.2.2]; exact ENNReal.one_lt_top⟩
  have hchz : Continuous fun z : hermA D ρ => conj (chz ψ b₀ z) :=
    Complex.continuous_conj.comp
      (hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr b₀.1).comp continuous_subtype_val))
  have hnorm : ∀ z, ‖conj (chz ψ b₀ z)‖ = 1 := fun z => by
    rw [RCLike.norm_conj]
    exact hψ.2.1 _
  have hz : ∀ x, Continuous fun z : hermA D ρ => M.nzx z 0 * (M.nzx 0 x * (M.sh y * g)) := fun x =>
    (M.nzx_cont.comp (continuous_id.prodMk continuous_const)).mul continuous_const
  have hx : ∀ z, Continuous fun x : Mx D ρ p => M.nzx z 0 * (M.nzx 0 x * (M.sh y * g)) := fun z =>
    continuous_const.mul ((M.nzx_cont.comp (continuous_const.prodMk continuous_id)).mul continuous_const)
  have bd : ∀ Φ : G D n → ℂ, Continuous Φ → LeftInv (GF D n) Φ →
      ∃ B : ℝ, ∀ x z, ‖Φ (M.nzx z 0 * (M.nzx 0 x * (M.sh y * g))) * conj (chz ψ b₀ z)‖ ≤ B := by
    intro Φ hΦ hi
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hΦ.continuousOn
    refine ⟨B, fun x z => ?_⟩
    obtain ⟨γ, hγ, hc⟩ := hCm z x y
    rw [norm_mul, hnorm, mul_one, ← hi γ hγ]
    exact hB _ hc
  obtain ⟨A, hA⟩ := bd F hF hFi
  obtain ⟨B, hB⟩ := bd F' hF' hFi'
  have key := iterated_sub (m.lz.restrict m.𝓖) (m.μ.restrict m.𝓕)
    (fun x z => F (M.nzx z 0 * (M.nzx 0 x * (M.sh y * g))) * conj (chz ψ b₀ z))
    (fun x z => F' (M.nzx z 0 * (M.nzx 0 x * (M.sh y * g))) * conj (chz ψ b₀ z)) A B
    (fun x => (hF.comp (hz x)).mul hchz) (fun x => (hF'.comp (hz x)).mul hchz)
    (fun z => (hF.comp (hx z)).mul continuous_const) (fun z => (hF'.comp (hx z)).mul continuous_const) hA hB
  simp only [PositivityTheory.Rg.Rsw.pc, PositivityTheory.Rg.Rsw.zc, Pi.sub_apply, sub_mul]
  exact key

end GlobalTheory.CompanionTheory.PcAdd

end
