import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockRepEquivFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetPolynomialScalarEval
open GlobalTheory.PRep GlobalTheory.SmGL Matrix

noncomputable section

namespace GlobalTheory.JacLineFiltration

theorem sizeMatrix_cases {m : Type} [Fintype m] [DecidableEq m]
    (b : SizeMatrix (Two (Fin 1) m) (Two (Fin 1) m)) :
    (b.1 false false = 1 ∧ b.1 false true = 0 ∧ b.1 true false = 0 ∧ b.1 true true = Fintype.card m) ∨
    (b.1 false false = 0 ∧ b.1 false true = 1 ∧ b.1 true false = 1 ∧
      b.1 true true + 1 = Fintype.card m) := by
  obtain ⟨b, h1, h2⟩ := b
  have r0 : b false false + b false true = 1 := by
    have := h1 false; rw [Fintype.sum_bool] at this; rw [add_comm]; exact this.trans (Fintype.card_fin 1)
  have r1 : b true false + b true true = Fintype.card m := by
    have := h1 true; rw [Fintype.sum_bool] at this; rw [add_comm]; exact this
  have c0 : b false false + b true false = 1 := by
    have := h2 false; rw [Fintype.sum_bool] at this; rw [add_comm]; exact this.trans (Fintype.card_fin 1)
  have c1 : b false true + b true true = Fintype.card m := by
    have := h2 true; rw [Fintype.sum_bool] at this; rw [add_comm]; exact this
  change (b false false = 1 ∧ b false true = 0 ∧ b true false = 0 ∧ b true true = Fintype.card m) ∨
    (b false false = 0 ∧ b false true = 1 ∧ b true false = 1 ∧ b true true + 1 = Fintype.card m)
  omega

theorem comp_aeval {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) (A : Module.End R M) (B : Module.End R N) (h : φ ∘ₗ A = B ∘ₗ φ)
    (q : Polynomial R) : φ ∘ₗ Polynomial.aeval A q = Polynomial.aeval B q ∘ₗ φ := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      LinearMap.comp_smul, LinearMap.smul_comp]
    rw [Module.End.commute_pow_left_of_commute h.symm n]

end GlobalTheory.JacLineFiltration

namespace GlobalTheory.JacLineFiltration

theorem aeval_mem_of_subQuot {G V X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup X]
    [Module ℂ X] {π : Representation ℂ G V} (S T : Subrepresentation π)
    {σ : Representation ℂ G X} (ψ : (subQuot S T).Equiv σ) (g : G) (q : Polynomial ℂ)
    (hq : Polynomial.aeval (σ g) q = 0) :
    ∀ w ∈ S.toSubmodule, Polynomial.aeval (π g) q w ∈ T.toSubmodule := by
  intro w hw
  have h1 := comp_aeval S.toSubmodule.subtype (S.toRepresentation g) (π g) rfl q
  have h2 := comp_aeval (T.toSubmodule.comap S.toSubmodule.subtype).mkQ (S.toRepresentation g)
    (subQuot S T g) rfl q
  have h3 := comp_aeval ψ.toLinearMap (subQuot S T g) (σ g) (ψ.isIntertwining' g) q
  have e1 := LinearMap.congr_fun h1 ⟨w, hw⟩
  have e2 := LinearMap.congr_fun h2 ⟨w, hw⟩
  have e3 := LinearMap.congr_fun h3 ((T.toSubmodule.comap S.toSubmodule.subtype).mkQ ⟨w, hw⟩)
  simp only [LinearMap.comp_apply, Submodule.coe_subtype, hq, LinearMap.zero_apply] at e1 e2 e3
  rw [← e2] at e3
  have e4 : (T.toSubmodule.comap S.toSubmodule.subtype).mkQ
      (Polynomial.aeval (S.toRepresentation g) q ⟨w, hw⟩) = 0 :=
    (map_eq_zero_iff ψ.toLinearEquiv ψ.toLinearEquiv.injective).1 e3
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at e4
  rw [← e1]
  exact e4

end GlobalTheory.JacLineFiltration

namespace GlobalTheory.JacLineFiltration

set_option maxHeartbeats 2000000 in

theorem jacquet_line_filtration : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.GeometricLemmaFiltration → ∀ {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (e : Fin 1 ⊕ m ≃ n) {Y : Type} [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ (GL m k) Y),
    IsSmooth τ → ∀ (ξ : kˣ →* ℂˣ), IsSmoothChar ξ → ∀ (ϖ : kˣ),
    (∀ (m' : Type) [Fintype m'] [DecidableEq m'] (e' : Fin 1 ⊕ m' ≃ m), ∃ q : Polynomial ℂ,
      q.eval (ξ ϖ : ℂ) ≠ 0 ∧ Polynomial.aeval (jac₂ e' τ (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) q = 0) →
    ∃ (N : ℕ) (S : Fin (N + 1) → Subrepresentation (jac₂ e (ind₂ e (extTensor (detRep (Fin 1) ξ) τ)))),
      Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last N) = ⊤ ∧ ∃ t₀ : Fin N,
        Nonempty ((subQuot (S t₀.succ) (S t₀.castSucc)).Equiv (extTensor (detRep (Fin 1) ξ) τ)) ∧
        ∀ t, t ≠ t₀ → ∃ q : Polynomial ℂ, q.eval (ξ ϖ : ℂ) ≠ 0 ∧ ∀ w ∈ (S t.succ).toSubmodule,
          Polynomial.aeval (jac₂ e (ind₂ e (extTensor (detRep (Fin 1) ξ) τ))
            (GeneralLinearGroup.scalar (Fin 1) ϖ, 1)) q w ∈ (S t.castSucc).toSubmodule := by
  intro k _ _ _ _ hG n m _ _ _ _ e Y _ _ τ hτ ξ hξ ϖ hq
  have h1 : JacquetOfInducedFiltration k := hG k
  have h2 := h1 Bool Bool n (Two (Fin 1) m) (Two (Fin 1) m) (two e) (two e)
  obtain ⟨N, b, hb⟩ := h2
  have hρ : IsSmooth ((extTensor (detRep (Fin 1) ξ) τ).comp (leviTwo k (Fin 1) m).symm.toMonoidHom) :=
    isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff _).2 hξ.detChar) hτ) _
      ((continuous_apply false).prodMk (continuous_apply true))
  have h3 := hb (TensorProduct ℂ ℂ Y) ((extTensor (detRep (Fin 1) ξ) τ).comp (leviTwo k (Fin 1) m).symm.toMonoidHom) hρ
  obtain ⟨S, hmono, h0, hN, hcell⟩ := h3
  let S' : Fin (N + 1) → Subrepresentation (jac₂ e (ind₂ e (extTensor (detRep (Fin 1) ξ) τ))) :=
    fun t => ⟨(S t).toSubmodule, fun g _ hv => (S t).apply_mem_toSubmodule (leviTwo k (Fin 1) m g) hv⟩
  let b₀ : SizeMatrix (Two (Fin 1) m) (Two (Fin 1) m) :=
    ⟨fun i j => if i = j then Fintype.card (Two (Fin 1) m i) else 0, fun i => by
      rw [Fintype.sum_bool]; cases i <;> simp, fun j => by
      rw [Fintype.sum_bool]; cases j <;> simp⟩
  refine ⟨N, S', fun t u h => hmono h, ?_, ?_, b.symm b₀, ?_, ?_⟩
  · exact SetLike.ext fun x => by
      show x ∈ (S 0).toSubmodule ↔ _
      rw [h0]; rfl
  · exact SetLike.ext fun x => by
      show x ∈ (S (Fin.last N)).toSubmodule ↔ _
      rw [hN]; rfl
  · have hb0 : b (b.symm b₀) = b₀ := b.apply_symm_apply b₀
    have h01 : (b (b.symm b₀)).1 false true = 0 := by rw [hb0]; rfl
    have h10 : (b (b.symm b₀)).1 true false = 0 := by rw [hb0]; rfl
    have hc := GlobalTheory.T.levi_block_rep_equiv_first (k := k) (m := m) (b (b.symm b₀)) h01 h10 (W := TensorProduct ℂ ℂ Y)
      ((extTensor (detRep (Fin 1) ξ) τ).comp (leviTwo k (Fin 1) m).symm.toMonoidHom) hρ
    obtain ⟨f, g, hfg⟩ := hc
    have hc3 := hcell (b.symm b₀) f g
    refine hc3.elim fun ψ => hfg.elim fun χ => ?_
    exact ⟨Representation.Equiv.mk (ψ.toLinearEquiv.trans χ.toLinearEquiv) fun x =>
      (ψ.trans χ).isIntertwining' (leviTwo k (Fin 1) m x)⟩
  · intro t ht
    have hff : (b t).1 false false = 0 := by
      rcases sizeMatrix_cases (b t) with h | h
      · exfalso
        apply ht
        rw [Equiv.eq_symm_apply]
        apply Subtype.ext
        funext i j
        cases i <;> cases j
        · exact h.1
        · exact h.2.1
        · exact h.2.2.1
        · exact h.2.2.2
      · exact h.1
    have hc := GlobalTheory.T.jacquet_polynomial_scalar_eval (k := k) (m := m) (Y := Y) τ ξ ϖ hq (b t) hff
    obtain ⟨f, g, q, hq0, hqA⟩ := hc
    have hc3 := hcell t f g
    exact hc3.elim fun ψ => ⟨q, hq0, aeval_mem_of_subQuot (S t.succ) (S t.castSucc) ψ _ q hqA⟩

end GlobalTheory.JacLineFiltration
