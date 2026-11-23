import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenClosureSubset
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff
open scoped Manifold

namespace GlobalTheory

open Set Metric

theorem exists_cutoff_of_openPartialHomeomorph {X E : Type} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (e : OpenPartialHomeomorph X E) (C U : Set X) (hC : IsCompact C) (hU : IsOpen U)
    (hCU : C ⊆ U) (hUs : U ⊆ e.source) :
    ∃ ρ : X → ℝ, Continuous ρ ∧ ContDiffOn ℝ ∞ (ρ ∘ e.symm) e.target ∧
      (∀ y, 0 ≤ ρ y ∧ ρ y ≤ 1) ∧ (∀ y ∈ C, ρ y = 1) ∧ tsupport ρ ⊆ U := by
  classical
  haveI : ProperSpace E := FiniteDimensional.proper_real E
  set K := e '' C with hKdef
  set O := e '' U with hOdef
  have hK : IsCompact K := hC.image_of_continuousOn (e.continuousOn.mono (hCU.trans hUs))
  have hO : IsOpen O := e.isOpen_image_of_subset_source hU hUs
  have hKO : K ⊆ O := image_mono hCU
  have hOt : O ⊆ e.target := by
    rintro _ ⟨u, hu, rfl⟩; exact e.map_source (hUs hu)
  obtain ⟨δ0, hδ0, hδ0O⟩ := hK.exists_cthickening_subset_open hO hKO
  set δ := δ0 / 2 with hδdef
  have hδ : 0 < δ := by positivity
  set T := cthickening δ K with hTdef
  have hT : IsCompact T := hK.cthickening
  have hTO : T ⊆ O := (cthickening_mono (by linarith) K).trans hδ0O
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_contMDiffMap_zero_one_of_isClosed (𝓘(ℝ, E)) (n := (⊤ : ℕ∞))
    (isOpen_thickening (δ := δ) (E := K)).isClosed_compl hK.isClosed
    (disjoint_compl_left_iff_subset.2 (self_subset_thickening hδ K))
  set ψ : E → ℝ := ⇑f with hψdef
  have hψ : ContDiff ℝ ∞ ψ := by
    have := contMDiff_iff_contDiff.1 f.contMDiff
    exact_mod_cast this
  have hψT : tsupport ψ ⊆ T := by
    refine (closure_mono ?_).trans (closure_thickening_subset_cthickening δ K)
    intro x hx
    by_contra h
    exact hx (hf0 h)
  set ρ : X → ℝ := fun y => if y ∈ e.source then ψ (e y) else 0 with hρdef
  set S := e.symm '' T with hSdef
  have hS : IsCompact S := hT.image_of_continuousOn (e.continuousOn_symm.mono (hTO.trans hOt))
  have hSU : S ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hTO hx
    rw [e.left_inv (hUs hu)]; exact hu
  have hsupp : Function.support ρ ⊆ S := by
    intro y hy
    simp only [Function.mem_support, hρdef] at hy
    split_ifs at hy with hys
    · exact ⟨e y, hψT (subset_tsupport _ hy), e.left_inv hys⟩
    · exact absurd rfl hy
  have htsupp : tsupport ρ ⊆ S := closure_minimal hsupp hS.isClosed
  refine ⟨ρ, ?_, ?_, ?_, ?_, htsupp.trans hSU⟩
  · refine continuous_iff_continuousAt.2 fun y => ?_
    by_cases hy : y ∈ e.source
    · have h1 : ContinuousAt (ψ ∘ e) y := hψ.continuous.continuousAt.comp (e.continuousAt hy)
      refine h1.congr ?_
      filter_upwards [e.open_source.mem_nhds hy] with z hz
      simp [hρdef, hz]
    · have hyS : y ∉ S := fun h => hy (hUs (hSU h))
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hyS] with z hz
      exact (Function.notMem_support.1 fun h => hz (hsupp h)).symm
  · refine hψ.contDiffOn.congr fun x hx => ?_
    simp [hρdef, e.map_target hx, e.right_inv hx]
  · intro y
    simp only [hρdef]
    split_ifs
    · exact hf01 _
    · exact ⟨le_rfl, zero_le_one⟩
  · intro y hy
    simp only [hρdef, if_pos (hUs (hCU hy))]
    exact hf1 (mem_image_of_mem e hy)

theorem cutoff_chart : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [T2Space (CxPts p σ)] (c : AlgChart p σ d) (C U : Set (CxPts p σ)), IsCompact C → IsOpen U → C ⊆ U → U ⊆ c.e.source → ∃ ρ : CxPts p σ → ℝ, Continuous ρ ∧ ContDiffOn ℝ ∞ (ρ ∘ c.e.symm) c.e.target ∧ (∀ y, 0 ≤ ρ y ∧ ρ y ≤ 1) ∧ (∀ y ∈ C, ρ y = 1) ∧ tsupport ρ ⊆ U := by
  intro k _ Y p σ d _ c C U hC hU hCU hUs
  exact exists_cutoff_of_openPartialHomeomorph c.e C U hC hU hCU hUs

end GlobalTheory
