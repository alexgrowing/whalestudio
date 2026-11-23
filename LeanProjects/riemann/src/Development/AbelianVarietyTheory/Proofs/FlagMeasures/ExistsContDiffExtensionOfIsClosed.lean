import Mathlib
import Formalism.RealPlaceAnalysis.FinalF

open Formalism.REAL
open scoped ContDiff Manifold Topology

namespace GlobalTheory

open scoped ContDiff Manifold Topology in

theorem _root_.GlobalTheory.exists_contDiff_extension_of_isClosed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hS : IsClosed S) (f : E → ℂ)
    (hf : ∀ x ∈ S, ∃ (U : Set E) (F : E → ℂ), IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ y ∈ U, y ∈ S → f y = F y) :
    ∃ F : E → ℂ, ContDiff ℝ ∞ F ∧ ∀ y ∈ S, F y = f y := by
  classical
  let t : E → Set ℂ := fun y => if y ∈ S then {f y} else Set.univ
  have ht : ∀ y, Convex ℝ (t y) := by
    intro y
    by_cases hy : y ∈ S
    · simp only [t, if_pos hy]; exact convex_singleton _
    · simp only [t, if_neg hy]; exact convex_univ
  have hloc : ∀ x : E, ∃ U ∈ 𝓝 x, ∃ g : E → ℂ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) g U ∧ ∀ y ∈ U, g y ∈ t y := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨U, F, hU, hxU, hF, hfF⟩ := hf x hx
      refine ⟨U, hU.mem_nhds hxU, F, hF.contMDiffOn, fun y hy => ?_⟩
      by_cases hyS : y ∈ S
      · simp only [t, if_pos hyS, Set.mem_singleton_iff]; exact (hfF y hy hyS).symm
      · simp only [t, if_neg hyS, Set.mem_univ]
    · refine ⟨Sᶜ, hS.isOpen_compl.mem_nhds hx, fun _ => 0, contMDiffOn_const, fun y hy => ?_⟩
      simp only [t, if_neg (show y ∉ S from hy), Set.mem_univ]
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local 𝓘(ℝ, E) (n := ⊤) ht hloc
  refine ⟨g, g.contMDiff.contDiff, fun y hy => ?_⟩
  have hgy := hg y
  simpa only [t, if_pos hy, Set.mem_singleton_iff] using hgy

open scoped ContDiff Manifold Topology in

theorem _root_.GlobalTheory.smoothOnG_exists_contDiff_extension :
    ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ), _root_.Formalism.REAL.SmoothOnG ε f →
      ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧
        ∀ g : Matrix (Fin n) (Fin n) ℂ, _root_.Formalism.REAL.inUJ ε g → F (fun i j => g i j) = f g := by
  intro n ε f hf
  let S : Set (Fin n → Fin n → ℂ) := {x | _root_.Formalism.REAL.inUJ ε (Matrix.of x)}
  have hS : IsClosed S := by
    have h0 : Continuous (fun x : Fin n → Fin n → ℂ => Matrix.of x) := continuous_id
    have hc : Continuous
        (fun x : Fin n → Fin n → ℂ => Matrix.conjTranspose (Matrix.of x) * _root_.Formalism.REAL.Jm ε * Matrix.of x) :=
      (h0.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h0
    exact isClosed_eq hc continuous_const
  obtain ⟨F, hF, hFS⟩ := _root_.GlobalTheory.exists_contDiff_extension_of_isClosed hS
    (fun x => f (Matrix.of x)) (by
      intro x hx
      unfold _root_.Formalism.REAL.SmoothOnG at hf
      obtain ⟨U, G, hU, hxU, hG, hfG⟩ := hf (Matrix.of x) hx
      let U' : Set (Fin n → Fin n → ℂ) := U
      let G' : (Fin n → Fin n → ℂ) → ℂ := G
      have hU' : IsOpen U' := hU
      have hG' : ContDiffOn ℝ ∞ G' U' := hG
      exact ⟨U', G', hU', hxU, hG', fun y hy hyS => hfG (Matrix.of y) hy hyS⟩)
  exact ⟨F, hF, fun g hg => hFS (fun i j => g i j) hg⟩

end GlobalTheory
