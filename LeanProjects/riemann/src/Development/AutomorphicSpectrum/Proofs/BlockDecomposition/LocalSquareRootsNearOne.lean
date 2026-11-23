import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem map_sq_nhds_one_of_normed {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    (h2 : (2 : K) ≠ 0) : Filter.map (fun x : K => x ^ 2) (𝓝 1) = 𝓝 1 := by
  have hd : HasStrictDerivAt (fun x : K => x ^ 2) (2 : K) 1 := by
    simpa using hasStrictDerivAt_pow 2 (1 : K)
  simpa using hd.map_nhds_eq h2

theorem sq_fills_of_map {K : Type*} [Monoid K] [TopologicalSpace K]
    (h : Filter.map (fun x : K => x ^ 2) (𝓝 1) = 𝓝 1) (V : Set K) (hV : V ∈ 𝓝 (1 : K)) :
    ∀ᶠ x in 𝓝 (1 : K), ∃ μ ∈ V, μ ^ 2 = x := by
  have : (fun x : K => x ^ 2) '' V ∈ 𝓝 (1 : K) := by
    rw [← h]; exact Filter.image_mem_map hV
  filter_upwards [this] with x hx
  obtain ⟨μ, hμ, rfl⟩ := hx
  exact ⟨μ, hμ, rfl⟩

theorem sq_fills_nhds_one {F : Type} [Field F] [NumberField F] (u : Pl F) :
    ∀ V ∈ 𝓝 (1 : Kp u), ∀ᶠ x in 𝓝 (1 : Kp u), ∃ μ ∈ V, μ ^ 2 = x := by
  intro V hV
  cases u with
  | inl w =>
    have h2 : (2 : w.Completion) ≠ 0 := by
      have : CharZero w.Completion := charZero_of_injective_algebraMap (algebraMap F w.Completion).injective
      exact two_ne_zero
    have hn : ‖(2 : w.Completion)‖ ≠ 1 := by
      have e : ‖(2 : w.Completion)‖ = ‖InfinitePlace.Completion.extensionEmbedding w 2‖ :=
        ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
          (map_zero _) 2).symm
      rw [e, map_ofNat]
      norm_num
    letI : NontriviallyNormedField w.Completion :=
      NontriviallyNormedField.ofNormNeOne ⟨2, h2, hn⟩
    exact sq_fills_of_map (K := w.Completion) (map_sq_nhds_one_of_normed h2) V hV
  | inr v =>
    letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
    have h2 : (2 : v.adicCompletion F) ≠ 0 := by
      have : CharZero (v.adicCompletion F) := charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
      exact two_ne_zero
    exact sq_fills_of_map (K := v.adicCompletion F) (map_sq_nhds_one_of_normed h2) V hV

end GlobalTheory.CompanionTheory.PlaneSA
