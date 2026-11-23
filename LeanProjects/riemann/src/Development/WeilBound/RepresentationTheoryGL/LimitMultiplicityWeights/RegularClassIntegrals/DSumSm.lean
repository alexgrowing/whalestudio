import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.Variation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLocallyFiniteContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineContinuous

open MeasureTheory Set Filter NumberField IsDedekindDomain Matrix
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RapidDecay GlobalTheory.CompanionTheory.RegInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.TruncKer GlobalTheory.Cusp
open scoped ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace MainStatements.WeightKernel.Dec.DSumSm

lemma loc_fin {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {Γ : Subgroup G} [DiscreteTopology Γ] {f : G → ℂ} (hf : HasCompactSupport f) (z : G)
    [TopologicalSpace X] [WeaklyLocallyCompactSpace X] {φ : X → G} (hφ : Continuous φ) (x₀ : X) :
    ∃ S : Finset Γ, ∀ᶠ x in 𝓝 x₀, ∀ ν : Γ, ν ∉ S → f (z * ν * φ x) = 0 := by
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds x₀
  have hfin := GlobalTheory.AutomorphicL2KernelContinuous.finite_contributing (Γ := Γ) hf (isCompact_singleton (x := z⁻¹))
    (hK.image hφ)
  refine ⟨hfin.toFinset, Filter.mem_of_superset hKn fun x hx ν hν => ?_⟩
  by_contra h
  apply hν
  rw [Set.Finite.mem_toFinset]
  exact ⟨z⁻¹, rfl, φ x, ⟨x, hx, rfl⟩, by simpa using h⟩

lemma cont_prod {G : Type} [Monoid G] [TopologicalSpace G] [ContinuousMul G] :
    ∀ (k : ℕ) (γ : Fin k → ℝ → G), (∀ i, Continuous (γ i)) →
      Continuous fun t : Fin k → ℝ => (List.ofFn fun i => γ i (t i)).prod
  | 0, γ, _ => by simpa using continuous_const
  | k + 1, γ, h => by
    simp only [List.ofFn_succ, List.prod_cons]
    exact ((h 0).comp (continuous_apply 0)).mul
      ((cont_prod k (fun i => γ i.succ) (fun i => h i.succ)).comp
        (continuous_pi fun i => continuous_apply i.succ))

end MainStatements.WeightKernel.Dec.DSumSm

namespace MainStatements.WeightKernel.Dec

open DSumSm in
theorem sumSm : SmOf → SumSm := by
  intro hSm F E _ _ _ _ _ σ h n J hJ Γ hΓ f hf z
  have : DiscreteTopology Γ :=
    DiscreteTopology.of_subset (t := (Γ : Set (GAd σ J))) (s := (ratPts σ J : Set (GAd σ J)))
      (inferInstance : DiscreteTopology (ratPts σ J)) hΓ
  have hs : GlobalTheory.UAut.IsSm σ J f := hSm F E σ h n J hJ f hf
  have hcs : HasCompactSupport f := (continuous_of_mem_ccAd hf).2
  refine ⟨?_, ?_⟩
  · intro k γ hγ g
    rw [contDiff_iff_contDiffAt]
    intro t₀
    have hφ : Continuous fun t : Fin k → ℝ => g * (List.ofFn fun i => γ i (t i)).prod :=
      continuous_const.mul (cont_prod k γ fun i =>
        GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J (γ i) (hγ i))
    obtain ⟨S, hS⟩ := loc_fin (Γ := Γ) hcs z hφ t₀
    have hsum : ContDiffAt ℝ ∞ (fun t : Fin k → ℝ =>
        ∑ ν ∈ S, f (z * ν * (g * (List.ofFn fun i => γ i (t i)).prod))) t₀ := by
      refine ContDiff.contDiffAt (ContDiff.sum fun ν _ => ?_)
      have := hs k γ hγ (z * ν * g)
      simpa only [mul_assoc] using this
    refine hsum.congr_of_eventuallyEq (hS.mono fun t ht => ?_)
    exact tsum_eq_sum (s := S) (fun ν hν => ht ν hν)
  · intro b hb
    funext g
    have hbc := GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J b hb
    obtain ⟨S, hS⟩ := loc_fin (Γ := Γ) (φ := fun t : ℝ => g * b t) hcs z (continuous_const.mul hbc) 0
    have hline : ∀ x : GAd σ J, ContDiff ℝ ∞ fun t : ℝ => f (x * b t) := by
      intro x
      have := (hs 1 (fun _ => b) (fun _ => hb) x).comp
        (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun t : ℝ => fun _ : Fin 1 => t)
      convert this using 2
      simp [List.ofFn_succ]
    have e1 : (fun t => nsum Γ f z (g * b t)) =ᶠ[𝓝 0]
        fun t => ∑ ν ∈ S, f (z * ν * (g * b t)) :=
      hS.mono fun t ht => tsum_eq_sum (s := S) (fun ν hν => ht ν hν)
    have e2 : ∀ ν ∉ S, lineDer b f (z * ν * g) = 0 := by
      intro ν hν
      show deriv (fun t => f (z * ν * g * b t)) 0 = 0
      have : (fun t => f (z * ν * g * b t)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) :=
        hS.mono fun t ht => by simpa only [mul_assoc] using ht ν hν
      rw [this.deriv_eq, deriv_const]
    show deriv (fun t => nsum Γ f z (g * b t)) 0 = ∑' ν : Γ, lineDer b f (z * ν * g)
    rw [e1.deriv_eq, tsum_eq_sum (s := S) e2, deriv_fun_sum]
    · refine Finset.sum_congr rfl fun ν _ => ?_
      show _ = deriv (fun t => f (z * ν * g * b t)) 0
      simp only [mul_assoc]
    · intro ν _
      have := ((hline (z * ν * g)).differentiable (by simp)) 0
      simpa only [mul_assoc] using this

end MainStatements.WeightKernel.Dec

end
