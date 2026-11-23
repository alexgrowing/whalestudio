import Formalism.HermitianCurvature.StatementB
import Mathlib.Geometry.Manifold.PartitionOfUnity

open Matrix Set Filter Topology
open scoped Manifold ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

theorem isClosed_GVt (k r : ℕ) : IsClosed {x : Mt k r | Matrix.of x ∈ B.GV k r} := by
  have h0 : Continuous (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
    continuous_id
  have hc : Continuous (fun x : Mt k r => (Matrix.of x)ᴴ * Hpk k r * Matrix.of x) :=
    ((h0.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul h0
  exact isClosed_eq hc continuous_const

theorem exists_smoothExt {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : B.Mat k r → E) (hF : B.CkOn (⊤ : ℕ∞) (B.GV k r) F) :
    ∃ Ft : Mt k r → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ft ∧
      ∀ x : Mt k r, Matrix.of x ∈ B.GV k r → Ft x = F (Matrix.of x) := by
  set s : Set (Mt k r) := {x : Mt k r | Matrix.of x ∈ B.GV k r} with hs
  have hloc : ∀ i : s, ∃ (U : Set (Mt k r)) (f' : Mt k r → E), IsOpen U ∧ (i : Mt k r) ∈ U ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f' U ∧ ∀ x ∈ U, Matrix.of x ∈ B.GV k r → F (Matrix.of x) = f' x := by
    intro i
    obtain ⟨U, f', hU, hiU, hf', hfe⟩ := hF (Matrix.of (i : Mt k r)) i.2
    exact ⟨U, f', hU, hiU, hf', fun x hx hxG => hfe (Matrix.of x) hx hxG⟩
  choose U f' hU hiU hf' hfe using hloc
  have hcov : s ⊆ ⋃ i : s, U i := fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hiU ⟨x, hx⟩⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Mt k r) (isClosed_GVt k r) U hU hcov
  refine ⟨fun x => ∑ᶠ i, ρ i x • f' i x, ?_, ?_⟩
  · have h := ρ.contMDiff_finsum_smul (n := (⊤ : ℕ∞)) (g := f') fun i x hx => by
      have hxU : x ∈ U i := hρ i hx
      exact ((hf' i).contDiffAt ((hU i).mem_nhds hxU)).contMDiffAt
    exact contMDiff_iff_contDiff.1 h
  · intro x hx
    have hsum : ∑ᶠ i, ρ i x = 1 := ρ.sum_eq_one hx
    have heq : ∀ i, ρ i x • f' i x = ρ i x • F (Matrix.of x) := by
      intro i
      by_cases h0 : ρ i x = 0
      · simp [h0]
      · have hxU : x ∈ U i := hρ i (subset_tsupport _ h0)
        rw [hfe i x hxU hx]
    simp only [heq]
    rw [← finsum_smul, hsum, one_smul]

end Formalism.FourierDecayAlt.P.SmoothExtensionClosedSet
