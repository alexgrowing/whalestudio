import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterBilinearLawsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterIntegralVanishesStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem integral_mul_tsum_unimod {ι X : Type} [Countable ι] [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    {c : ι → X → ℂ} {h : X → ℂ} {a : ι → ℂ} (hc : ∀ i, AEStronglyMeasurable (c i) ν)
    (hc1 : ∀ i x, ‖c i x‖ = 1) (hh : AEStronglyMeasurable h ν) {B : ℝ} (hB : ∀ x, ‖h x‖ ≤ B)
    (ha : Summable fun i => ‖a i‖) :
    ∫ x, h x * ∑' i, c i x * a i ∂ν = ∑' i, (∫ x, h x * c i x ∂ν) * a i := by
  have hbd : ∀ i x, ‖h x * (c i x * a i)‖ ≤ B * ‖a i‖ := fun i x => by
    rw [norm_mul, norm_mul, hc1, one_mul]
    exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)
  have hint : ∀ i, Integrable (fun x => h x * (c i x * a i)) ν := fun i =>
    Integrable.of_bound (hh.mul ((hc i).mul aestronglyMeasurable_const)) (B * ‖a i‖)
      (Eventually.of_forall (hbd i))
  have hsum : Summable fun i => ∫ x, ‖h x * (c i x * a i)‖ ∂ν := by
    refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun x => norm_nonneg _) (fun i => ?_)
      ((ha.mul_left B).mul_left (ν.real Set.univ))
    calc ∫ x, ‖h x * (c i x * a i)‖ ∂ν ≤ ∫ _, B * ‖a i‖ ∂ν :=
          integral_mono (hint i).norm (integrable_const _) (hbd i)
      _ = ν.real Set.univ * (B * ‖a i‖) := by simp [integral_const]
  have key := hasSum_integral_of_summable_integral_norm hint hsum
  have e1 : ∀ x, ∑' i, h x * (c i x * a i) = h x * ∑' i, c i x * a i := fun x => tsum_mul_left
  have e2 : ∀ i, ∫ x, h x * (c i x * a i) ∂ν = (∫ x, h x * c i x ∂ν) * a i := fun i => by
    rw [← integral_mul_const]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [mul_assoc])
  simp only [e1, e2] at key
  exact key.tsum_eq.symm

theorem parseval {D : D7} {ρ p : ℕ} (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (b₀ : HermE D ρ) (hb₀ : b₀.1.det ≠ 0) (a b : Matrix (Fin ρ) (Fin p) D.host.E → ℂ)
    (ha : Summable (fun η => ‖a η‖)) (hb : Summable (fun η => ‖b η‖)) :
    ∫ x in m.𝓕, (∑' η : Matrix (Fin ρ) (Fin p) D.host.E, chv ψ b₀ x (rt η) * a η) *
        conj (∑' ξ : Matrix (Fin ρ) (Fin p) D.host.E, chv ψ b₀ x (rt ξ) * b ξ) ∂m.μ =
      ∑' η : Matrix (Fin ρ) (Fin p) D.host.E, a η * conj (b η) := by
  classical
  obtain ⟨-, hadd, hnorm, hneg, -, hcont⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws (p := p) ψ hψ b₀
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : Countable (Matrix (Fin ρ) (Fin p) D.host.E) :=
    inferInstanceAs (Countable (Fin ρ → Fin p → D.host.E))
  haveI : IsProbabilityMeasure (m.μ.restrict m.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact m.hμ.2.2⟩
  have hcm : ∀ η : Matrix (Fin ρ) (Fin p) D.host.E,
      StronglyMeasurable (fun x : Mx D ρ p => chv ψ b₀ x (rt η)) := fun η =>
    (hcont.comp (Continuous.prodMk continuous_id continuous_const)).stronglyMeasurable
  have hcm' : ∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E,
      StronglyMeasurable (fun x : Mx D ρ p => conj (chv ψ b₀ x (rt ξ))) := fun ξ =>
    Complex.continuous_conj.comp_stronglyMeasurable (hcm ξ)
  have hc1 : ∀ (η : Matrix (Fin ρ) (Fin p) D.host.E) (x : Mx D ρ p), ‖chv ψ b₀ x (rt η)‖ = 1 :=
    fun η x => hnorm x _
  have hc1' : ∀ (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (x : Mx D ρ p),
      ‖conj (chv ψ b₀ x (rt ξ))‖ = 1 := fun ξ x => by rw [RCLike.norm_conj]; exact hc1 ξ x
  have horth : ∀ ξ η : Matrix (Fin ρ) (Fin p) D.host.E,
      ∫ x in m.𝓕, conj (chv ψ b₀ x (rt ξ)) * chv ψ b₀ x (rt η) ∂m.μ = if η = ξ then 1 else 0 := by
    intro ξ η
    by_cases h : η = ξ
    · subst h
      have e : ∀ x : Mx D ρ p, conj (chv ψ b₀ x (rt η)) * chv ψ b₀ x (rt η) = 1 := fun x => by
        rw [Complex.conj_mul', hc1]; simp
      simp [e]
    · have e : ∀ x : Mx D ρ p, conj (chv ψ b₀ x (rt ξ)) * chv ψ b₀ x (rt η) =
          chv ψ b₀ x (rt (η - ξ)) := fun x => by
        have hr : (rt (η - ξ) : Mx D ρ p) = rt η + -rt ξ := by
          rw [← sub_eq_add_neg]; exact rat_sub η ξ
        rw [hr, hadd, hneg, mul_comm]
      simp only [e, if_neg h]
      exact GlobalTheory.T.heisenberg_character_integral_vanishes m ψ hψ b₀ hb₀ (η - ξ) (sub_ne_zero.2 h)
  have hs : ∀ x : Mx D ρ p, Summable fun η => chv ψ b₀ x (rt η) * a η := fun x =>
    Summable.of_norm (by simpa only [norm_mul, hc1, one_mul] using ha)
  have hfm : StronglyMeasurable fun x : Mx D ρ p => ∑' η, chv ψ b₀ x (rt η) * a η :=
    tsum_meas (fun η => (hcm η).mul_const _) hs
  have hfB : ∀ x : Mx D ρ p, ‖∑' η, chv ψ b₀ x (rt η) * a η‖ ≤ ∑' η, ‖a η‖ := fun x => by
    have h1 := norm_tsum_le_tsum_norm (f := fun η => chv ψ b₀ x (rt η) * a η)
      (by simpa only [norm_mul, hc1, one_mul] using ha)
    simpa only [norm_mul, hc1, one_mul] using h1
  have hcoef : ∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E,
      ∫ x in m.𝓕, (∑' η, chv ψ b₀ x (rt η) * a η) * conj (chv ψ b₀ x (rt ξ)) ∂m.μ = a ξ := by
    intro ξ
    have h1 := integral_mul_tsum_unimod (m.μ.restrict m.𝓕)
      (c := fun (η : Matrix (Fin ρ) (Fin p) D.host.E) (x : Mx D ρ p) => chv ψ b₀ x (rt η))
      (h := fun x => conj (chv ψ b₀ x (rt ξ))) (a := a) (B := 1)
      (fun η => (hcm η).aestronglyMeasurable) hc1 (hcm' ξ).aestronglyMeasurable
      (fun x => (hc1' ξ x).le) ha
    simp only [horth, ite_mul, one_mul, zero_mul, tsum_ite_eq] at h1
    rw [← h1]
    exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  have hconj : ∀ x : Mx D ρ p, conj (∑' ξ, chv ψ b₀ x (rt ξ) * b ξ) =
      ∑' ξ, conj (chv ψ b₀ x (rt ξ)) * conj (b ξ) := fun x => by
    rw [Complex.conj_tsum]; simp only [map_mul]
  have h2 := integral_mul_tsum_unimod (m.μ.restrict m.𝓕)
    (c := fun (ξ : Matrix (Fin ρ) (Fin p) D.host.E) (x : Mx D ρ p) => conj (chv ψ b₀ x (rt ξ)))
    (h := fun x => ∑' η, chv ψ b₀ x (rt η) * a η) (a := fun ξ => conj (b ξ))
    (fun ξ => (hcm' ξ).aestronglyMeasurable) hc1' hfm.aestronglyMeasurable hfB
    (by simpa only [RCLike.norm_conj] using hb)
  simp only [hconj, h2, hcoef]

end GlobalTheory.CompanionTheory.FJE
