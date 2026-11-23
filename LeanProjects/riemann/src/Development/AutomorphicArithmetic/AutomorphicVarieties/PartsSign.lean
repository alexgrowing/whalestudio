import Development.AutomorphicArithmetic.AutomorphicVarieties.LengthEqAddEigen

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology

namespace UpperTheory.V

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime]

def IsConjOm (σ : Ω ≃+* Ω) : Prop := ∃ j : Ω →+* ℂ, ∀ x, j (σ x) = starRingEnd ℂ (j x)

include E in
theorem IsConjOm.cyc {σ : Ω ≃+* Ω} (h : IsConjOm σ) : cyclotomicCharacter Ω l σ = -1 := by
  obtain ⟨j, hj⟩ := h
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ n) := ⟨hN0⟩
  have hspec := cyclotomicCharacter.spec (L := Ω) l σ ζ hζ.pow_eq_one
  have h1 : σ ζ * ζ = 1 := by
    apply j.injective
    have : ‖j ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hζ.pow_eq_one, map_one]) hN0
    rw [map_mul, hj, map_one, Complex.conj_mul', this]
    simp
  rw [hspec, ← pow_succ, hζ.pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff, Nat.cast_add, ZMod.natCast_zmod_val,
    Nat.cast_one] at h1
  rw [Units.val_neg, Units.val_one, map_neg, map_one]
  exact eq_neg_of_add_eq_zero_left h1

variable [IsCMField E]

theorem IsConjOm.isLift {σ : Ω ≃+* Ω} (h : IsConjOm σ) : IsLift (cE E) σ := by
  obtain ⟨j, hj⟩ := h
  intro x
  apply j.injective
  rw [hj]
  exact (IsCMField.complexEmbedding_complexConj E (j.comp (algebraMap E Ω)) x).symm

omit [IsCMField E] in
include E in
theorem exists_isConjOm : ∃ σ : Ω ≃+* Ω, IsConjOm σ := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  let j : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  let c : ℂ ≃ₐ[ℚ] ℂ := Complex.conjAe.restrictScalars ℚ
  exact ⟨(c.restrictNormal Ω).toRingEquiv, j.toRingHom, fun x => c.restrictNormal_commutes Ω x⟩

omit [IsCMField E] in
include E in
theorem twScal_conj {σ : Ω ≃+* Ω} (h : IsConjOm σ) (e : ℕ) : twScal l σ (e : ℤ) = (-1) ^ e := by
  rw [twScal, h.cyc (E := E), zpow_neg, zpow_natCast, ← inv_pow, inv_neg, inv_one]
  simp

private theorem mem_eig (D : LData E Ω l) (e : ℕ) {σ : Ω ≃+* Ω} (h : IsConjOm σ) (z : Z1 (qzTw D (e : ℤ))) (s : ℤ_[l]) :
    (Submodule.Quotient.mk z : H1 (qzTw D (e : ℤ))) ∈ (cAct D e).eigenspace ((-1) ^ e * s) ↔
      ∃ m, ∀ g, z.1 (conjGS D h.isLift g) - s • z.1 g = qzTw D e g m - m := by
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h.isLift z
  have hs : (-1 : ℤ_[l]) ^ e * (-1) ^ e = 1 := by rw [← mul_pow]; simp
  rw [Module.End.mem_eigenspace_iff, cAct, galois_action_cohomology_eq_conj D e h.isLift, e₁, ← Submodule.Quotient.mk_smul]
  refine (mk_eq_mk_iff _ _ _).trans ?_
  have key : ∀ g, z₁.1 g - (((-1 : ℤ_[l]) ^ e * s) • z).1 g =
      (-1 : ℤ_[l]) ^ e • (z.1 (conjGS D h.isLift g) - s • z.1 g) := fun g => by
    rw [f₁, twScal_conj (E := E) h, smul_sub, smul_smul]; rfl
  simp only [key]
  refine ⟨fun ⟨m, hm⟩ => ⟨(-1 : ℤ_[l]) ^ e • m, fun g => ?_⟩, fun ⟨m, hm⟩ => ⟨(-1 : ℤ_[l]) ^ e • m, fun g => ?_⟩⟩
  · rw [map_smul, ← smul_sub, ← hm, smul_smul, hs, one_smul]
  · rw [map_smul, ← smul_sub, ← hm]

theorem mk_mem_ShaPlus_iff (D : LData E Ω l) (e : ℕ) {σ : Ω ≃+* Ω} (h : IsConjOm σ) (z : Z1 (qzTw D (e : ℤ))) :
    Submodule.Quotient.mk z ∈ ShaPlus D e ↔ Submodule.Quotient.mk z ∈ Sha D e ∧
      ∃ m, ∀ g, z.1 (conjGS D h.isLift g) - z.1 g = qzTw D e g m - m := by
  have := mem_eig D e h z 1
  simp only [mul_one, one_smul] at this
  exact and_congr_right fun _ => this

theorem mk_mem_ShaMinus_iff (D : LData E Ω l) (e : ℕ) {σ : Ω ≃+* Ω} (h : IsConjOm σ) (z : Z1 (qzTw D (e : ℤ))) :
    Submodule.Quotient.mk z ∈ ShaMinus D e ↔ Submodule.Quotient.mk z ∈ Sha D e ∧
      ∃ m, ∀ g, z.1 (conjGS D h.isLift g) + z.1 g = qzTw D e g m - m := by
  have := mem_eig D e h z (-1)
  simp only [← pow_succ, neg_smul, one_smul, sub_neg_eq_add] at this
  exact and_congr_right fun _ => this

end UpperTheory.V

end
