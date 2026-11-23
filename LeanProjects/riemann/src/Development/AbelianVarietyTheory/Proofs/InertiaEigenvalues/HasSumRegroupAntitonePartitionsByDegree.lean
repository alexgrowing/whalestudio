import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEqJtDet

noncomputable section

namespace GlobalTheory.JSW

theorem tsum_fibre_entrySum_eq {m : ℕ} {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (F : (Fin m → ℕ) → E) (d : ℕ) :
    ∑' b : (fun l : {l : Fin m → ℕ // Antitone l} => ∑ i, l.1 i) ⁻¹' {d}, F b.1.1 =
      ∑ l ∈ antiParts m d, F l := by
  rw [← Finset.tsum_subtype (antiParts m d) F]
  let e : ((fun l : {l : Fin m → ℕ // Antitone l} => ∑ i, l.1 i) ⁻¹' {d}) ≃
      {x // x ∈ antiParts m d} :=
    { toFun := fun b => ⟨b.1.1, mem_antiParts.2 ⟨b.2, b.1.2⟩⟩
      invFun := fun x => ⟨⟨x.1, (mem_antiParts.1 x.2).2⟩, (mem_antiParts.1 x.2).1⟩
      left_inv := fun b => rfl
      right_inv := fun x => rfl }
  exact e.tsum_eq (fun x => F x.1)

theorem regroup_antiParts {m : ℕ} (G : (Fin m → ℕ) → ℂ)
    (hG : Summable fun l : {l : Fin m → ℕ // Antitone l} => ‖G l.1‖) :
    Summable (fun d => ‖∑ l ∈ antiParts m d, G l‖) ∧
    ∀ s, HasSum (fun d => ∑ l ∈ antiParts m d, G l) s →
      HasSum (fun l : {l : Fin m → ℕ // Antitone l} => G l.1) s := by
  set σ : {l : Fin m → ℕ // Antitone l} → ℕ := fun l => ∑ i, l.1 i with hσ
  have h1 := hG.hasSum.tsum_fiberwise σ
  have h1' : Summable (fun d => ∑ l ∈ antiParts m d, ‖G l‖) := by
    refine h1.summable.congr fun d => ?_
    exact tsum_fibre_entrySum_eq (fun l => ‖G l‖) d
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun d => norm_sum_le _ _) h1', ?_⟩
  intro s hs
  have hg : Summable fun l : {l : Fin m → ℕ // Antitone l} => G l.1 := hG.of_norm
  have h2 := hg.hasSum.tsum_fiberwise σ
  have h2' : HasSum (fun d => ∑ l ∈ antiParts m d, G l) (∑' l : {l : Fin m → ℕ // Antitone l}, G l.1) :=
    h2.congr_fun fun d => (tsum_fibre_entrySum_eq G d).symm
  rw [hs.unique h2']
  exact hg.hasSum

example : ∀ {m : ℕ} (G : (Fin m → ℕ) → ℂ),
    (Summable fun l : {l : Fin m → ℕ // Antitone l} => ‖G l.1‖) →
    Summable (fun d => ‖∑ l ∈ GlobalTheory.JSW.antiParts m d, G l‖) ∧
    ∀ s, HasSum (fun d => ∑ l ∈ GlobalTheory.JSW.antiParts m d, G l) s →
      HasSum (fun l : {l : Fin m → ℕ // Antitone l} => G l.1) s :=
  fun G hG => regroup_antiParts G hG

end GlobalTheory.JSW
