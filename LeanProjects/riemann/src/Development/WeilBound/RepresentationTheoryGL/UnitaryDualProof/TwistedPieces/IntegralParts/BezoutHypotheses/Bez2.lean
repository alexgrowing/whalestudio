import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.NilpotentHypotheses.AevalProdLinearFactors

noncomputable section

open Polynomial PositivityTheory.RgUd.T.Nil.Asm

namespace PositivityTheory.RgUd.TP.Nil.Asm

theorem bez2 {M : Type*} [AddCommGroup M] [Module ℂ M] (K : Submodule ℂ M) (R R' : M →ₗ[ℂ] M)
    (hRR : R ∘ₗ R' = LinearMap.id) (hR'R : R' ∘ₗ R = LinearMap.id) (hK : ∀ m ∈ K, R m ∈ K) (c : ℝ) (hc : 1 < c)
    (d : ℝ) (a b : List ℝ) (hab : ∀ x ∈ a, ∀ y ∈ b, y + x ≠ d) (ζ : M)
    (h1 : ((b.map fun y => R - ((c ^ y : ℝ) : ℂ) • LinearMap.id).prod : Module.End ℂ M) ζ ∈ K)
    (h2 : ((a.map fun x => ((c ^ d : ℝ) : ℂ) • R' - ((c ^ x : ℝ) : ℂ) • LinearMap.id).prod : Module.End ℂ M) ζ ∈ K) :
    ζ ∈ K := by
  set β : ℂ := ((c ^ d : ℝ) : ℂ)
  set γ : ℝ → ℂ := fun x => ((c ^ x : ℝ) : ℂ)
  have hRR' : (R : Module.End ℂ M) * R' = 1 := hRR
  have hR'R' : (R' : Module.End ℂ M) * R = 1 := hR'R
  have hQ : ((a.map fun x => β • (1 : Module.End ℂ M) - γ x • R).prod : Module.End ℂ M) ζ ∈ K := by
    rw [← pow_mul_prod R R' hRR' hR'R' β γ a, Module.End.mul_apply]
    exact pow_mem K R hK _ _ h2
  have hc0 : 0 < c := by linarith
  have hcop : IsCoprime ((b.map fun y => X - C (γ y)).prod) ((a.map fun x => C β - C (γ x) * X).prod) := by
    refine isCoprime_list_prod_left _ _ b fun y hy => isCoprime_list_prod_right _ _ a fun x hx => ?_
    refine isCoprime_lin (γ y) β (γ x) ?_
    intro h0
    have h0' : β = γ x * γ y := sub_eq_zero.1 h0
    have : (c ^ d : ℝ) = c ^ x * c ^ y := by
      simp only [β, γ] at h0'
      exact_mod_cast h0'
    rw [← Real.rpow_add hc0] at this
    have hlog := congrArg Real.log this
    rw [Real.log_rpow hc0, Real.log_rpow hc0] at hlog
    have hl : 0 < Real.log c := Real.log_pos hc
    have hd : d = x + y := mul_right_cancel₀ hl.ne' hlog
    exact hab x hx y hy (by linarith)
  obtain ⟨u, v, huv⟩ := hcop
  have key := congrArg (fun p => (aeval (R : Module.End ℂ M) p) ζ) huv
  simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply] at key
  rw [← key]
  refine K.add_mem (aeval_mem K R hK u _ ?_) (aeval_mem K R hK v _ ?_)
  · rw [aeval_prod_lin R γ b]; exact h1
  · rw [aeval_prod_linear_factors R β γ a]
    convert hQ using 3
    refine List.map_congr_left fun x _ => ?_
    rfl

end PositivityTheory.RgUd.TP.Nil.Asm
