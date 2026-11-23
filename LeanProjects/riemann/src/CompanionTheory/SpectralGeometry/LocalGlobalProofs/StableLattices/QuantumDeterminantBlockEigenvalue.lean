import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharSub
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantAntiHomomorphismStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CommutingLocallyNilpotentCommonKernelStatement

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgTransport

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL

theorem glRel_comp_inj {A : Type*} [Ring A] {m n : ℕ} {E : Fin n → Fin n → A} (hE : GlRel E)
    (e : Fin m → Fin n) (he : Function.Injective e) : GlRel (fun a b => E (e a) (e b)) := by
  intro a b c d
  have := hE (e a) (e b) (e c) (e d)
  simpa only [he.eq_iff] using this

theorem glRel_op_transpose {A : Type*} [Ring A] {n : ℕ} {E : Fin n → Fin n → A} (hE : GlRel E) :
    GlRel (fun a b => MulOpposite.op (E b a)) := by
  intro a b c d
  have h := congrArg MulOpposite.op (hE d c b a)
  simp only [MulOpposite.op_sub, MulOpposite.op_mul] at h
  rw [h]
  simp only [eq_comm (a := c) (b := b), eq_comm (a := a) (b := d)]
  by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2]

theorem qdet_eigen_of_killed {n : ℕ} (Q : GMod n) (d : Fin 3 → ℕ) (h : ∑ i, d i = n) (w : Q.V)
    (hw : ∀ a b, blk (stdBlocks d h) b < blk (stdBlocks d h) a → Q.E a b w = 0)
    (c : Fin 3 → ℂ → ℂ) (hc : ∀ i Y, Qd Q d h i Y w = c i Y • w) (Y : ℂ) :
    qdet Q.E (Y + ((n : ℂ) - 1) / 2) w = (∏ i, c i Y) • w := by
  let f : Module.End ℂ Q.V →ₗ[ℂ] (Module.End ℂ Q.V)ᵐᵒᵖ := (MulOpposite.opLinearEquiv ℂ).toLinearMap
  have f1 : f 1 = 1 := rfl
  have fm : ∀ x y, f (x * y) = f y * f x := fun _ _ => rfl
  let X : Fin n → Fin n → (Module.End ℂ Q.V)ᵐᵒᵖ := fun p q => MulOpposite.op (Q.E q p)
  have hX : GlRel X := glRel_op_transpose Q.gl
  have hq : ∀ u, qdet X u = f (qdet Q.E u) := fun u => GlobalTheory.T.quantum_determinant_anti_homomorphism f f1 fm Q.E Q.gl u
  have hb : ∀ i u, qdet (fun p q : Fin (d i) => X (stdBlocks d h ⟨i, p⟩) (stdBlocks d h ⟨i, q⟩)) u =
      f (qdet (bops Q d h i) u) := fun i u =>
    GlobalTheory.T.quantum_determinant_anti_homomorphism f f1 fm (bops Q d h i)
      (glRel_comp_inj Q.gl (fun p => stdBlocks d h ⟨i, p⟩)
        (fun p q e => by simpa using (stdBlocks d h).injective e)) u
  have hspan := GlobalTheory.T.capelliDet_block_levi_congr_mod_upperBlockIdeal (Module.End ℂ Q.V)ᵐᵒᵖ d h X hX Y
  let L : (Module.End ℂ Q.V)ᵐᵒᵖ →ₗ[ℂ] Q.V :=
    { toFun := fun a => a.unop w
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL : ∀ y ∈ Submodule.span ℂ {y : (Module.End ℂ Q.V)ᵐᵒᵖ | ∃ (p q : Fin n) (v : (Module.End ℂ Q.V)ᵐᵒᵖ),
      blk (stdBlocks d h) p < blk (stdBlocks d h) q ∧ y = X p q * v}, L y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨p, q, v, hpq, rfl⟩ := hy
      show (v.unop * Q.E q p) w = 0
      rw [Module.End.mul_apply, hw q p hpq, map_zero]
    | zero => exact map_zero L
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul a x _ hx => rw [map_smul, hx, smul_zero]
  have h0 := hL _ hspan
  rw [map_sub, sub_eq_zero] at h0
  have hl3 : ∀ g : Fin 3 → (Module.End ℂ Q.V)ᵐᵒᵖ, (List.ofFn g).prod = g 0 * g 1 * g 2 := by
    intro g
    simp [List.ofFn_succ, mul_assoc]
  rw [hl3] at h0
  simp only [hb, hq] at h0
  have e1 : qdet Q.E (Y + ((n : ℂ) - 1) / 2) w = Qd Q d h 2 Y (Qd Q d h 1 Y (Qd Q d h 0 Y w)) := h0
  simp only [e1, hc, map_smul, smul_smul, Fin.prod_univ_three]

end GlobalTheory.CompanionTheory.RgTransport
