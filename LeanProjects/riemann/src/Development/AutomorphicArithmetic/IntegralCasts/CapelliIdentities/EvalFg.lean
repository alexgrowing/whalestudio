import Mathlib

theorem UpperTheory.Reformulated.B.Qn15.eval_fg :
    ∀ {R : Type} [inst : CommRing R] [inst_1 : Algebra R ℂ] {σ : Type} {M₀ : Submodule R ℂ},
    M₀.FG →
      ∀ (P : MvPolynomial σ ℂ),
        ∃ (M : Submodule R ℂ),
          M.FG ∧ ∀ (v : σ → ℂ), (∀ (i : σ), v i ∈ M₀) → (MvPolynomial.eval v : MvPolynomial σ ℂ → ℂ) P ∈ M := by
  intro R _ _ σ M₀ h₀ P
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨Submodule.span R {a}, Submodule.fg_span_singleton a, fun v _ => ?_⟩
    rw [MvPolynomial.eval_C]
    exact Submodule.mem_span_singleton_self a
  | add p q hp hq =>
    obtain ⟨M, hM, hp⟩ := hp
    obtain ⟨N, hN, hq⟩ := hq
    refine ⟨M ⊔ N, hM.sup hN, fun v hv => ?_⟩
    rw [map_add]
    exact Submodule.add_mem_sup (hp v hv) (hq v hv)
  | mul_X p i hp =>
    obtain ⟨M, hM, hp⟩ := hp
    refine ⟨M * M₀, hM.mul h₀, fun v hv => ?_⟩
    rw [map_mul, MvPolynomial.eval_X]
    exact Submodule.mul_mem_mul (hp v hv) (hv i)
