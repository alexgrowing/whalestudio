import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ

namespace GlobalTheory.CompanionTheory.FlatThick

open TensorProduct in
set_option backward.isDefEq.respectTransparency true in

theorem flat_quotientMap {P B : Type} [CommRing P] [CommRing B] [Algebra P B] [Module.Flat P B] (I₀ : Ideal P) :
    (Ideal.quotientMap (I₀.map (algebraMap P B)) (algebraMap P B) Ideal.le_comap_map :
      P ⧸ I₀ →+* B ⧸ I₀.map (algebraMap P B)).Flat := by
  have f3 : (algebraMap (P ⧸ I₀) ((P ⧸ I₀) ⊗[P] B)).Flat := RingHom.flat_algebraMap_iff.2 inferInstance
  let e₂ : (B ⧸ I₀.map (algebraMap P B)) ≃+* (P ⧸ I₀) ⊗[P] B :=
      (((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I₀).toRingEquiv).trans
        (Algebra.TensorProduct.comm P B (P ⧸ I₀)).toRingEquiv)
  have f5 : (e₂.symm.toRingHom).Flat := RingHom.Flat.of_bijective e₂.symm.bijective
  have f4 := RingHom.Flat.comp f3 f5
  convert f4 using 1
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  refine e₂.injective ?_
  have : e₂ (Ideal.Quotient.mk _ (algebraMap P B r)) = algebraMap (P ⧸ I₀) ((P ⧸ I₀) ⊗[P] B) (Ideal.Quotient.mk _ r) := by
    change Algebra.TensorProduct.comm P B (P ⧸ I₀) (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I₀ (Ideal.Quotient.mk _ (algebraMap P B r))) = _
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    simp [Algebra.TensorProduct.algebraMap_apply]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    rfl
  simpa using this

theorem flat_of_surjective_ker {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (f : A →+* B) (hf : f.Flat)
    (π : A →+* A') (hπ : Function.Surjective π) (a : A) (hker : RingHom.ker π = Ideal.span {a})
    (g : A' →+* B ⧸ Ideal.span {f a}) (hg : ∀ r, g (π r) = Ideal.Quotient.mk _ (f r)) : g.Flat := by
  letI : Algebra A B := f.toAlgebra
  haveI : Module.Flat A B := hf
  have hJ : (Ideal.span {a}).map (algebraMap A B) = Ideal.span {f a} := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  let e₁ : (A ⧸ Ideal.span {a}) ≃+* A' :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hπ)
  let e₂ : (B ⧸ (Ideal.span {a}).map (algebraMap A B)) ≃+* (B ⧸ Ideal.span {f a}) := Ideal.quotEquivOfEq hJ
  have h0 := flat_quotientMap (P := A) (B := B) (Ideal.span {a})
  have h1 : (e₁.symm.toRingHom).Flat := RingHom.Flat.of_bijective e₁.symm.bijective
  have h2 : (e₂.toRingHom).Flat := RingHom.Flat.of_bijective e₂.bijective
  have h3 := RingHom.Flat.comp (RingHom.Flat.comp h1 h0) h2
  convert h3 using 1
  refine RingHom.ext fun x => ?_
  obtain ⟨r, rfl⟩ := hπ x
  have hr : e₁.symm (π r) = Ideal.Quotient.mk _ r := by
    rw [RingEquiv.symm_apply_eq]; rfl
  change g (π r) = e₂ (Ideal.quotientMap _ (algebraMap A B) Ideal.le_comap_map (e₁.symm (π r)))
  rw [hr, hg]
  rfl

theorem flatT_qT (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] (O : Type) [CommRing O]
    (F : B.Fn O) (ρ : O →+* k) (n : ℕ) (hn : n ≠ 0) (T : Thick (Wc.L l F ρ (n + 1))) (hT : FlatT T) :
    FlatT (qT hn T) := by
  refine flat_of_surjective_ker T.i hT (Wc.red l k n) ?_ (Ideal.Quotient.mk _ ((l : WittVector l k) ^ n)) ?_ (qi T)
    (qi_red T)
  · intro x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ w, red_mk' w⟩
  · ext x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, red_mk', Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨Ideal.Quotient.mk _ c, (map_mul _ _ _)⟩
    · rintro ⟨c, hc⟩
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
      obtain ⟨d, hd⟩ := hc
      refine ⟨c + (l : WittVector l k) * d, ?_⟩
      rw [mul_add, ← mul_assoc, ← pow_succ, ← hd]
      ring

end GlobalTheory.CompanionTheory.FlatThick

end
