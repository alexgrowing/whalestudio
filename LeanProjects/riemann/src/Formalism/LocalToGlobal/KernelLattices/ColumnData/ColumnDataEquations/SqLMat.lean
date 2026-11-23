import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLInput

noncomputable section
open NumberField Formalism.BasicNotions Classical Matrix

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

variable {D : Car}

theorem osmul {N : ℕ} (b : 𝓞 D.host.E) (v : Fin N → D.host.E) : b • v = (b : D.host.E) • v := rfl

theorem coe_ne {n : 𝓞 D.host.E} (hn : n ≠ 0) : (n : D.host.E) ≠ 0 := by
  intro h
  apply hn
  exact_mod_cast h

theorem mem_homL {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {A : Matrix (Fin N') (Fin N) D.host.E} :
    A ∈ TaylorLogMetric.homL D L L' ↔ ∀ x ∈ L, A *ᵥ x ∈ L' := by
  constructor
  · intro h
    unfold TaylorLogMetric.homL at h
    induction h using Submodule.span_induction with
    | mem B hB => exact hB
    | zero => intro x _; simp
    | add B C _ _ hB hC =>
      intro x hx
      rw [Matrix.add_mulVec]
      exact L'.add_mem (hB x hx) (hC x hx)
    | smul c B _ hB =>
      intro x hx
      rw [Matrix.smul_mulVec]
      exact L'.smul_mem c (hB x hx)
  · intro h
    exact Submodule.subset_span h

theorem homL_mul_pres {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {e : Matrix (Fin N') (Fin N') D.host.E}
    (he : ∀ y ∈ L', e *ᵥ y ∈ L') {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ TaylorLogMetric.homL D L L') :
    e * A ∈ TaylorLogMetric.homL D L L' :=
  mem_homL.2 fun x hx => by
    rw [← Matrix.mulVec_mulVec]
    exact he _ (mem_homL.1 hA x hx)

theorem homL_mul_min {N N' : ℕ} {La Lc : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {Lb Ld : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {M : Matrix (Fin N') (Fin N') D.host.E}
    {n : 𝓞 D.host.E} (hn0 : n ≠ 0) (hn : ∀ u ∈ Lc, (n : D.host.E) • u ∈ La)
    (hM : ∀ y ∈ Lb, ∃ m ∈ Ld, M *ᵥ y = (n : D.host.E) • m)
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : A ∈ TaylorLogMetric.homL D La Lb) : M * A ∈ TaylorLogMetric.homL D Lc Ld :=
  mem_homL.2 fun u hu => by
    obtain ⟨m, hm, hMm⟩ := hM _ (mem_homL.1 hA _ (hn u hu))
    have h1 : (n : D.host.E) • ((M * A) *ᵥ u) = (n : D.host.E) • m := by
      rw [← Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, hMm]
    rw [smul_right_injective _ (coe_ne hn0) h1]
    exact hm

theorem yy_mul {N N' : ℕ} {La Lc : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {Lb Ld : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {M : Matrix (Fin N') (Fin N') D.host.E}
    (h : ∀ A ∈ TaylorLogMetric.homL D La Lb, M * A ∈ TaylorLogMetric.homL D Lc Ld) :
    ∀ B ∈ TaylorLogMetric.YYl D La Lb, M * B ∈ TaylorLogMetric.YYl D Lc Ld := by
  intro B hB
  unfold TaylorLogMetric.YYl at hB ⊢
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    exact Submodule.subset_span ⟨a, ha, M * A, h A hA, by rw [Matrix.mul_smul]⟩
  | zero => simp
  | add B C _ _ hB hC =>
    rw [Matrix.mul_add]
    exact Submodule.add_mem _ hB hC
  | smul c B _ hB =>
    rw [Matrix.mul_smul]
    exact Submodule.smul_mem _ c hB

def phi {N N' : ℕ} (M : Matrix (Fin N') (Fin N') D.host.E) : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N' where
  toFun z := fun τ i j => ∑ k, TaylorLogMetric.embT D τ (M i k) * z τ k j
  map_zero' := by funext τ i j; simp
  map_add' := by intro z w; funext τ i j; simp [mul_add, Finset.sum_add_distrib]

theorem phi_apply {N N' : ℕ} (M : Matrix (Fin N') (Fin N') D.host.E) (z : TaylorLogMetric.VC D N N') (τ i j) :
    phi M z τ i j = ∑ k, TaylorLogMetric.embT D τ (M i k) * z τ k j := rfl

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem phi_embV {N N' : ℕ} (M : Matrix (Fin N') (Fin N') D.host.E) (w : ℂ) (A : Matrix (Fin N') (Fin N) D.host.E) :
    phi M (w • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) A) = w • TaylorLogMetric.embV D (TaylorLogMetric.tor0 D cc δ) (M * A) := by
  funext τ i j
  simp only [phi_apply, Pi.smul_apply, smul_eq_mul, TaylorLogMetric.embV, TaylorLogMetric.tor0, Matrix.mul_apply, map_sum, map_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem phi_La {N N' : ℕ} {La Lc : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {Lb Ld : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {M : Matrix (Fin N') (Fin N') D.host.E}
    (h : ∀ B ∈ TaylorLogMetric.YYl D La Lb, M * B ∈ TaylorLogMetric.YYl D Lc Ld) :
    ∀ z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) La Lb, phi M z ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) Lc Ld := by
  intro z hz
  unfold TaylorLogMetric.La at hz ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    rw [phi_embV]
    exact AddSubgroup.subset_closure ⟨w, hw, M * A, h A hA, rfl⟩
  | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx => rw [map_neg]; exact AddSubgroup.neg_mem _ hx

theorem phi_one {N N' : ℕ} (z : TaylorLogMetric.VC D N N') : phi (1 : Matrix (Fin N') (Fin N') D.host.E) z = z := by
  funext τ i j
  simp [phi_apply, Matrix.one_apply]

theorem phi_sub {N N' : ℕ} (M M' : Matrix (Fin N') (Fin N') D.host.E) (z : TaylorLogMetric.VC D N N') :
    phi (M - M') z = phi M z - phi M' z := by
  funext τ i j
  simp [phi_apply, sub_mul, Finset.sum_sub_distrib]

theorem phi_mul {N N' : ℕ} (M M' : Matrix (Fin N') (Fin N') D.host.E) (z : TaylorLogMetric.VC D N N') :
    phi (M * M') z = phi M (phi M' z) := by
  funext τ i j
  simp only [phi_apply, Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs
