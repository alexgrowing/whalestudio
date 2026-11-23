import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem tensor_projective_dvd_of_coord_dvd :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (N : Type) [AddCommGroup N] [Module O N] [Module.Projective O M] [Module.Projective O N] (a : O) (z : M ⊗[O] N), (∀ (φ : Module.Dual O M) (ψ : Module.Dual O N), a ∣ TensorProduct.dualDistrib O M N (φ ⊗ₜ ψ) z) → ∃ y, z = a • y := by
  intro O M _ _ _ N _ _ _ _ a z h
  obtain ⟨s, hs⟩ := (Module.Projective.out : ∃ s : M →ₗ[O] M →₀ O,
    Function.LeftInverse (Finsupp.linearCombination O id) s)
  obtain ⟨s', hs'⟩ := (Module.Projective.out : ∃ s : N →ₗ[O] N →₀ O,
    Function.LeftInverse (Finsupp.linearCombination O id) s)
  have hf : ∀ (w : M ⊗[O] N) (p : M × N), finsuppTensorFinsupp' O M N (TensorProduct.map s s' w) p =
      TensorProduct.dualDistrib O M N ((Finsupp.lapply p.1 ∘ₗ s) ⊗ₜ (Finsupp.lapply p.2 ∘ₗ s')) w := by
    intro w ⟨i, j⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [finsuppTensorFinsupp'_apply_apply, dualDistrib_apply]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  set f := finsuppTensorFinsupp' O M N (TensorProduct.map s s' z) with hfdef
  have hdiv : ∀ p, a ∣ f p := fun p => by rw [hfdef, hf]; exact h _ _
  choose c hc using hdiv
  let g : M × N →₀ O := ∑ p ∈ f.support, Finsupp.single p (c p)
  have hg : f = a • g := by
    simp only [g, Finset.smul_sum, Finsupp.smul_single, smul_eq_mul, ← hc]
    exact (Finsupp.sum_single f).symm
  have hid : (Finsupp.linearCombination O id : (M →₀ O) →ₗ[O] M) ∘ₗ s = LinearMap.id :=
    LinearMap.ext hs
  have hid' : (Finsupp.linearCombination O id : (N →₀ O) →ₗ[O] N) ∘ₗ s' = LinearMap.id :=
    LinearMap.ext hs'
  refine ⟨TensorProduct.map (Finsupp.linearCombination O id) (Finsupp.linearCombination O id)
    ((finsuppTensorFinsupp' O M N).symm g), ?_⟩
  rw [← map_smul, ← map_smul, ← hg, hfdef, LinearEquiv.symm_apply_apply, ← LinearMap.comp_apply,
    ← TensorProduct.map_comp, hid, hid', TensorProduct.map_id, LinearMap.id_apply]

end GlobalTheory
