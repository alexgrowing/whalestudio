import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4
open CrystallineSemistableComparison.Onto

theorem single_mul_mem_span_tdeg_pos {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d))
    (m : (cone S : AddSubmonoid (Gam n d))) (a : K) (x : R0 K n d S)
    (hx : x ∈ Submodule.span K {y : R0 K n d S | ∃ (g : Gam n d) (hg : g ∈ (cone S : AddSubmonoid (Gam n d))),
      1 ≤ tdeg g ∧ y = mon K g hg}) :
    (AddMonoidAlgebra.single m a : R0 K n d S) * x ∈ Submodule.span K {y : R0 K n d S |
      ∃ (g : Gam n d) (hg : g ∈ (cone S : AddSubmonoid (Gam n d))), 1 ≤ tdeg g ∧ y = mon K g hg} := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, hg, h1, rfl⟩ := hy
    have e : (AddMonoidAlgebra.single m a : R0 K n d S) * mon K g hg =
        a • mon K (m.1 + g) ((cone S : AddSubmonoid (Gam n d)).add_mem m.2 hg) := by
      simp only [mon, AddMonoidAlgebra.single_mul_single, mul_one, AddMonoidAlgebra.smul_single, smul_eq_mul]
      rfl
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, ?_, rfl⟩)
    have h0 : 0 ≤ tdeg m.1 := m.2.2.2
    rw [tdeg_add]
    linarith
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem exceptional_ideal_le_span_pos_degree : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (x : R0 K n d S),
    x ∈ I0 n K S → x ∈ Submodule.span K {y : R0 K n d S |
      ∃ (g : Gam n d) (hg : g ∈ (cone S : AddSubmonoid (Gam n d))), 1 ≤ tdeg g ∧ y = mon K g hg} := by
  intro K _ n d S x hx
  unfold I0 Ideal.span at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, _, rfl⟩ := hy
    exact Submodule.subset_span ⟨_, _, by rw [tdeg_oneE_inr], rfl⟩
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul]
    induction c using AddMonoidAlgebra.induction_linear with
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add f g hf hg => rw [add_mul]; exact Submodule.add_mem _ hf hg
    | single m a => exact single_mul_mem_span_tdeg_pos S m a x hx

end GlobalTheory.CompanionTheory.SurjectionOntoH4
