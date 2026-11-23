import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicEmbeddingLiesOverOrComplexConjLiesOverStatement
open GlobalTheory.LKTrip

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.MaxIdealTensorPadic

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

theorem conjT_conjT (y : ℚ_[p] ⊗[ℚ] G.F) : conjT G.F ℚ_[p] (conjT G.F ℚ_[p] y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [conjT_tmul, NumberField.IsCMField.complexConj_apply_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem eq_sigma_liftW (f : ℚ_[p] ⊗[ℚ] G.F →+* PadicAlgCl p)
    (hf : ∀ a : ℚ_[p], f (a ⊗ₜ 1) = algebraMap ℚ_[p] (PadicAlgCl p) a)
    (i : Fin G.m) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (h : ∀ x : G.F, f (1 ⊗ₜ x) = σ (G.emb i x)) (y : ℚ_[p] ⊗[ℚ] G.F) :
    f y = σ ((G.liftW i y : G.Fw i) : PadicAlgCl p) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have e : (a ⊗ₜ[ℚ] x : ℚ_[p] ⊗[ℚ] G.F) = (a ⊗ₜ 1) * (1 ⊗ₜ x) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [e, map_mul, hf, h, map_mul, MulMemClass.coe_mul, map_mul]
    congr 1
    · simp [HTGroup.liftW, Algebra.TensorProduct.lift_tmul, HTGroup.embW]
    · congr 1
      simp only [HTGroup.liftW, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add, AddMemClass.coe_add, map_add]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (M : Ideal (TensorProduct ℚ ℚ_[p] G.F)), M.IsMaximal →
    ∃ i : Fin G.m, M = RingHom.ker (G.liftW i) ∨
      M = RingHom.ker ((G.liftW i).toRingHom.comp (conjT G.F ℚ_[p])) := by
  intro p _ G M hM
  letI : Field ((ℚ_[p] ⊗[ℚ] G.F) ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite ℚ_[p] ((ℚ_[p] ⊗[ℚ] G.F) ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ_[p] M).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Algebra.IsAlgebraic ℚ_[p] ((ℚ_[p] ⊗[ℚ] G.F) ⧸ M) := Algebra.IsAlgebraic.of_finite _ _
  let ι : ((ℚ_[p] ⊗[ℚ] G.F) ⧸ M) →ₐ[ℚ_[p]] PadicAlgCl p := IsAlgClosed.lift
  let f : ℚ_[p] ⊗[ℚ] G.F →+* PadicAlgCl p := (ι.comp (Ideal.Quotient.mkₐ ℚ_[p] M)).toRingHom
  have hker : ∀ y, y ∈ M ↔ f y = 0 := by
    intro y
    show y ∈ M ↔ ι (Ideal.Quotient.mk M y) = 0
    rw [map_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
  have hf : ∀ a : ℚ_[p], f (a ⊗ₜ 1) = algebraMap ℚ_[p] (PadicAlgCl p) a := fun a =>
    (ι.comp (Ideal.Quotient.mkₐ ℚ_[p] M)).commutes a
  let τ : G.F →+* PadicAlgCl p := f.comp (Algebra.TensorProduct.includeRight : G.F →ₐ[ℚ] _).toRingHom
  rcases GlobalTheory.T.padicEmbedding_liesOver_or_complexConj_liesOver p G τ with hτ | hτ
  · obtain ⟨i, σ, hσ⟩ := G.emb_all τ hτ
    refine ⟨i, Or.inl ?_⟩
    have h : ∀ x : G.F, f (1 ⊗ₜ x) = σ (G.emb i x) := fun x => RingHom.congr_fun hσ x
    ext y
    rw [hker, RingHom.mem_ker, eq_sigma_liftW G f hf i σ h y, map_eq_zero_iff _ σ.injective]
    exact ZeroMemClass.coe_eq_zero
  · obtain ⟨i, σ, hσ⟩ := G.emb_all _ hτ
    refine ⟨i, Or.inr ?_⟩
    let g : ℚ_[p] ⊗[ℚ] G.F →+* PadicAlgCl p := f.comp (conjT G.F ℚ_[p])
    have hg : ∀ a : ℚ_[p], g (a ⊗ₜ 1) = algebraMap ℚ_[p] (PadicAlgCl p) a := fun a => by
      simp only [g, RingHom.comp_apply, conjT_tmul, map_one, hf]
    have h : ∀ x : G.F, g (1 ⊗ₜ x) = σ (G.emb i x) := fun x => RingHom.congr_fun hσ x
    ext y
    have e : f y = g (conjT G.F ℚ_[p] y) := by simp only [g, RingHom.comp_apply, conjT_conjT]
    rw [hker, e, eq_sigma_liftW G g hg i σ h, map_eq_zero_iff _ σ.injective, RingHom.mem_ker]
    exact ZeroMemClass.coe_eq_zero

end GlobalTheory.MaxIdealTensorPadic
