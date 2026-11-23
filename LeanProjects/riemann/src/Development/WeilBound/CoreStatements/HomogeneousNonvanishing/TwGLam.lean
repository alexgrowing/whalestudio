import Mathlib
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGXi
open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

theorem trace_form_mulLeft_bijective (B Z : Type) [CommRing B] [Module.Finite ℤ B] [Module.Free ℤ B] [CommRing Z]
    (l : B →ₗ[ℤ] ℤ) (h : ∀ f : B →ₗ[ℤ] ℤ, ∃ (m : ℤ) (b : B), IsUnit (m : Z) ∧ ∀ a, m * f a = l (b * a))
    (L : Z ⊗[ℤ] B →ₗ[Z] Z) (hL : ∀ z a, L (z ⊗ₜ a) = z * l a) :
    Function.Bijective (fun r : Z ⊗[ℤ] B => L.comp (LinearMap.mulLeft Z r)) := by
  classical
  let T : Z ⊗[ℤ] B →ₗ[Z] Module.Dual Z (Z ⊗[ℤ] B) := (LinearMap.mul Z (Z ⊗[ℤ] B)).compr₂ L
  show Function.Bijective T
  let b := Module.Free.chooseBasis ℤ B
  let bZ := Algebra.TensorProduct.basis Z b
  have hs : Function.Surjective T := by
    intro f
    choose m β hu hm using fun i => h (b.coord i)
    refine ⟨∑ i, (f (bZ i) * ↑(hu i).unit⁻¹) ⊗ₜ β i, bZ.ext fun j => ?_⟩
    rw [map_sum, LinearMap.sum_apply]
    have h1 : ∀ i, T ((f (bZ i) * ↑(hu i).unit⁻¹) ⊗ₜ β i) (bZ j) = if j = i then f (bZ i) else 0 := by
      intro i
      have h2 : bZ j = 1 ⊗ₜ b j := Algebra.TensorProduct.basis_apply _ _
      show L (_ * bZ j) = _
      rw [h2, Algebra.TensorProduct.tmul_mul_tmul, hL, ← hm, mul_one, Module.Basis.coord_apply,
        Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · rw [mul_one, mul_assoc, IsUnit.val_inv_mul, mul_one]
      · simp
    simp [h1]
  refine ⟨?_, hs⟩
  have := OrzechProperty.injective_of_surjective_endomorphism (bZ.toDualEquiv.symm.toLinearMap.comp T)
    (bZ.toDualEquiv.symm.surjective.comp hs)
  exact Function.Injective.of_comp this

theorem tw_g_lam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ (p : ℕ) [Fact p.Prime], ∃ lam : (ℤ_[p] ⊗[ℤ] 𝓞 E) →ₗ[ℤ_[p]] ℤ_[p], (∀ r, lam (Algebra.TensorProduct.map (AlgHom.id ℤ_[p] ℤ_[p]) bar.toRingHom.toIntAlgHom r) = -lam r) ∧ Function.Bijective (fun r : ℤ_[p] ⊗[ℤ] 𝓞 E => lam.comp (LinearMap.mulLeft ℤ_[p] r)) := by
  intro E _ _ _ bar hbar hun p hp
  obtain ⟨ξ, h1, h2, h3⟩ := tw_g_xi E bar hbar hun p hp.out
  choose l0 hl0 using h2
  let l : 𝓞 E →ₗ[ℤ] ℤ := (AddMonoidHom.mk' l0 fun a b => by
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [← hl0, ← hl0, ← hl0, ← map_add, ← mul_add]
    rfl).toIntLinearMap
  have hl : ∀ a, (l a : ℚ) = Algebra.trace ℚ E (ξ * a) := fun a => (hl0 a).symm
  let L : ℤ_[p] ⊗[ℤ] 𝓞 E →ₗ[ℤ_[p]] ℤ_[p] :=
    (TensorProduct.AlgebraTensorModule.rid ℤ ℤ_[p] ℤ_[p]).toLinearMap.comp (l.baseChange ℤ_[p])
  have hL : ∀ z a, L (z ⊗ₜ a) = z * l a := by
    intro z a
    simp [L, mul_comm]
  have htr : ∀ x : E, Algebra.trace ℚ E (IsCMField.complexConj E x) = Algebra.trace ℚ E x := fun x =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) x
  have hlb : ∀ a, l (bar a) = -l a := by
    intro a
    apply Int.cast_injective (α := ℚ)
    push_cast
    rw [hl, hl, ← htr, map_mul, h1, hbar, IsCMField.complexConj_apply_apply, neg_mul, map_neg]
  refine ⟨L, fun r => ?_, trace_form_mulLeft_bijective _ _ l (fun f => ?_) L hL⟩
  · induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
      rw [Algebra.TensorProduct.map_tmul, hL, hL]
      show z * (l (bar a) : ℤ_[p]) = _
      rw [hlb]
      push_cast
      ring
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, neg_add]
  · obtain ⟨m, b, hm, hb⟩ := h3 f
    refine ⟨m, b, ?_, fun a => ?_⟩
    · rw [PadicInt.isUnit_iff]
      exact le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hm ((PadicInt.norm_int_lt_one_iff_dvd m).1 h))
    · apply Int.cast_injective (α := ℚ)
      rw [hb, hl, mul_assoc]
      rfl

end PositivityTheory.UnitarySelfGeneration
